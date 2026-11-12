module

public import Purelib.Polynomial.Dense.Roots.Tower.Algebra
public import Purelib.Algebra.Monogenic.Coordinates.Reading.Parameters
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached Gaussian-reading parameters along an original root tower

Every original adjunction supplies one fixed matrix/radius parameter cache.
The next cache uses the same original lifted weight and the preceding fixed
gain. All stages are prepared before any candidate or residual is observed.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming Parameters → CyclicParameters
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

universe u

set_option genInjectivity false in
/-- Original source-indexed reading caches for every retained adjunction in the same tower.

The fixed radius is common to the whole finite chain. Each tail carries the
actual preceding lifted weight and computed gain, so its caches retain their
original coefficient carrier and source quotient without new adjunctions.
-/
inductive Parameters : {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] →
    {polynomial : DensePolynomial K} → Tower K ring equality polynomial → Weight K → Rational → Rational → Type (u + 1)
  /-- The same original degree-zero endpoint needs only its original fixed nonnegativity certificates. -/
  | constant {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {parent : Weight K} {gain radius : Rational} (degreeZero : polynomial.natDegree = 0)
      (gainNonnegative : 0 ≤ gain) (radiusNonnegative : 0 ≤ radius) :
      Parameters (.constant polynomial degreeZero) parent gain radius
  /-- Cache one same original adjunction, followed by all same original quotient stages. -/
  | step {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {adjunction : Companion.Adjunction polynomial}
      {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
      {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
      {parent : Weight K} {gain radius : Rational}
      (current : CyclicParameters adjunction.table parent gain radius)
      (next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius) :
      Parameters (.step adjunction decreases remaining) parent gain radius

constructive_injectivity Parameters

namespace Parameters

/-- Prepare every same original adjunction's parameter cache before observing any candidate. -/
@[expose] def prepare {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial)
    (parent : Weight K) (gain radius : Rational) (gainNonnegative : 0 ≤ gain) (radiusNonnegative : 0 ≤ radius) :
    Parameters tower parent gain radius :=
  match tower with
  | .constant _ degreeZero => .constant degreeZero gainNonnegative radiusNonnegative
  | .step adjunction _ remaining =>
      let current := CyclicParameters.prepare adjunction.table parent gain radius gainNonnegative radiusNonnegative
      let next := prepare remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius
        current.gain_nonnegative radiusNonnegative
      .step current next

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius : Rational}

/-- The original parameter chain retains nonnegativity of its same common squared radius. -/
theorem radius_nonnegative (parameters : Parameters tower parent gain radius) : 0 ≤ radius := by
  cases parameters with
  | constant _ _ nonnegative => exact nonnegative
  | step current _ => exact current.powers.nonnegative

/-- The final weight is the original nested matrix weight of the same final coefficient carrier. -/
@[expose] def finalWeight {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius) :
    Weight tower.Scalar :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ => parent
  | .step _ _ remaining, .step _ next => finalWeight (tower := remaining) next

/-- Read the fixed gain of the same original last stage from the retained parameter chain. -/
@[expose] def finalGain {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius) : Rational :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ => gain
  | .step _ _ _, .step _ next => finalGain next

/-- The fixed gain at the same original tower endpoint is nonnegative. -/
theorem finalGain_nonnegative (parameters : Parameters tower parent gain radius) : 0 ≤ parameters.finalGain := by
  induction parameters with
  | constant _ gainNonnegative _ => exact gainNonnegative
  | step _ _ previous => exact previous

/-- Sum the source-fixed original root-reading bounds from the same retained parameter chain.

Each stage contributes its actual stored gain times its already cached
generator weight. The structural sum reads those original scalars and never
repeats a matrix-weight scan or observes a root candidate.
-/
@[expose] def rootBoundTotal {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius) : Rational :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ => 0
  | .step _ _ _, .step current next => current.gain * current.weights.generatorWeight + rootBoundTotal next

/-- The same structural source-fixed root bound sum is nonnegative. -/
theorem rootBoundTotal_nonnegative (parameters : Parameters tower parent gain radius) :
    0 ≤ parameters.rootBoundTotal := by
  induction parameters with
  | constant => exact le_rfl
  | step current _ previous =>
      exact Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct current.gain_nonnegative current.weights.generatorWeight_nonnegative) previous

variable {adjunction : Companion.Adjunction polynomial}
variable {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
variable {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}

/-- The current original root contribution and same retained tail give the exact structural sum equation. -/
theorem rootBoundTotal_step (current : CyclicParameters adjunction.table parent gain radius)
    (next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius) :
    (Parameters.step (decreases := decreases) current next).rootBoundTotal =
      current.gain * current.weights.generatorWeight + next.rootBoundTotal := rfl

/-- The structural source total bounds the current original retained root contribution. -/
theorem rootBoundTotal_current_le (current : CyclicParameters adjunction.table parent gain radius)
    (next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius) :
    current.gain * current.weights.generatorWeight ≤
      (Parameters.step (decreases := decreases) current next).rootBoundTotal := by
  have bound := Arithmetic.add_le_add_right_direct next.rootBoundTotal_nonnegative
    (current.gain * current.weights.generatorWeight)
  rewrite [Purelib.Data.Rat.Fraction.Field.zero_add, Purelib.Data.Rat.Fraction.Field.add_comm] at bound
  exact bound

/-- The structural source total bounds its same original retained tail's root contribution sum. -/
theorem rootBoundTotal_tail_le (current : CyclicParameters adjunction.table parent gain radius)
    (next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius) :
    next.rootBoundTotal ≤ (Parameters.step (decreases := decreases) current next).rootBoundTotal := by
  have bound := Arithmetic.add_le_add_right_direct
    (Arithmetic.mul_nonneg_direct current.gain_nonnegative current.weights.generatorWeight_nonnegative)
    next.rootBoundTotal
  rewrite [Purelib.Data.Rat.Fraction.Field.zero_add] at bound
  exact bound

/-- Count the actual cached original adjunction stages without observing their roots. -/
@[expose] def layers {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius) : Nat :=
  match tower, parameters with
  | .constant _ _, .constant _ _ _ => 0
  | .step _ _ _, .step _ next => layers next + 1

/-- The retained parameter chain contains every stage of the same original tower exactly once. -/
theorem layers_eq_steps (parameters : Parameters tower parent gain radius) : parameters.layers = tower.steps := by
  induction parameters with
  | constant => rfl
  | step _ _ previous => exact congrArg Nat.succ previous

/-- The same original source degree is exactly the number of prepared parameter layers. -/
theorem layers_eq_degree (parameters : Parameters tower parent gain radius) :
    parameters.layers = polynomial.natDegree := parameters.layers_eq_steps.trans tower.steps_eq_degree

end Parameters

end Purelib.Polynomial.Dense.Roots.Tower.Reading

end
