module

public import Purelib.Polynomial.Dense.Companion.Adjunction
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite towers of original root adjunctions

Each stage retains one original companion adjunction and its actual synthetic
quotient. The quotient degree drops by one, so a fuel computed from the
original degree produces a complete tower ending at a constant. Coefficient
algebras may have zero divisors; only the original retained leading unit is
transported to the next stage.
-/

public section

namespace Purelib.Polynomial.Dense.Roots

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic

universe u

namespace Tower

/-- The original coefficient algebra of one retained root-adjoining stage. -/
abbrev StageScalar {K : Type u} [CommRing K] [DecidableEq K] {polynomial : DensePolynomial K}
    (adjunction : Companion.Adjunction polynomial) :=
  Companion.Adjunction.Scalar adjunction.companion adjunction.table

end Tower

set_option genInjectivity false in
/-- A finite chain of actual source-dependent adjunctions ending at degree zero.

The retained coefficient ring is indexed at every stage. Each recursive
quotient belongs to the exact algebra built by that same original adjunction,
and its certified degree is one less than the original stage's degree.
-/
inductive Tower : (K : Type u) → CommRing K → DecidableEq K → DensePolynomial K → Type (u + 1)
  /-- The original source has reached degree zero. -/
  | constant {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
      (polynomial : DensePolynomial K) (degreeZero : polynomial.natDegree = 0) :
      Tower K ring equality polynomial
  /-- Retain one actual adjunction followed by the same quotient's complete tower. -/
  | step {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      (adjunction : Companion.Adjunction polynomial)
      (decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree)
      (remaining : Tower (Tower.StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient) :
      Tower K ring equality polynomial

constructive_injectivity Tower

namespace Tower

/-- Count the actual retained root-adjoining steps in the same original tower. -/
@[expose] def steps {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : Nat :=
  match tower with
  | .constant _ _ => 0
  | .step _ _ remaining => remaining.steps + 1

/-- The actual retained steps exhaust the original natural degree exactly. -/
theorem steps_eq_degree {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) :
    tower.steps = polynomial.natDegree := by
  induction tower with
  | constant polynomial degreeZero => exact degreeZero.symm
  | step adjunction decreases remaining previous =>
      exact (congrArg Nat.succ previous).trans decreases

/-- Construct the original complete tower by structural recursion on a certified exact degree.

The final equality identifies the supplied finite count with the actual source
degree. Every recursive call retains that same equality for its actual quotient.
-/
@[expose] def ofDegree (fuel : Nat) :
    {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] →
    (polynomial : DensePolynomial K) → polynomial.normalize = polynomial →
    (leadingInverse : K) → polynomial.leadingCoeff * leadingInverse = 1 →
    polynomial.natDegree = fuel → Tower K ring equality polynomial :=
  match fuel with
  | 0 => fun polynomial _ _ _ degree => .constant polynomial degree
  | count + 1 => fun polynomial normalized leadingInverse unit degree =>
      let companion := Companion.ofUnit polynomial (degree.symm ▸ Nat.zero_lt_succ count) leadingInverse unit
      let adjunction := companion.adjoin
      have nextDegree : adjunction.division.quotient.natDegree = count :=
        Nat.succ.inj ((adjunction.quotient_degree normalized).trans degree)
      let remaining := ofDegree count adjunction.division.quotient
        (adjunction.quotient_normalized normalized)
        (Cyclic.Element.scalar adjunction.table companion.leadingInverse)
        (adjunction.quotient_unit normalized) nextDegree
      .step adjunction (adjunction.quotient_degree normalized) remaining

/-- Compute a complete original adjunction tower using its source degree as the exact finite recursion budget. -/
@[expose] def prepare {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    (polynomial : DensePolynomial K) (normalized : polynomial.normalize = polynomial)
    (leadingInverse : K) (unit : polynomial.leadingCoeff * leadingInverse = 1) :
    Tower K ring equality polynomial :=
  ofDegree polynomial.natDegree polynomial normalized leadingInverse unit rfl

end Tower

end Purelib.Polynomial.Dense.Roots

end
