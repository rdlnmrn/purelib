module

import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Quadratic.Pair.Polynomial.Reduction
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Mul

/-!
# Original-sheet quadratic coefficient and denominator regressions

The examples exercise actual original isolated roots on both sheets, typed
norm-route obstruction for a split radicand, and source-domain preservation
when common polynomial factors cancel. No approximate sample is made into an
exact square root.
-/

namespace TestPurelib.Algebra.QuadraticPolynomial

open Purelib.Algebra.Quadratic.Pair.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Riemann.RootContinuation

/-- The constant radicand two, retaining its finite coefficient table. -/
private def two : Coefficients := DensePolynomial.constant 2

/-- The same isolated root channel and square certificate on either original sheet. -/
private def retainedTwo (sheet : Fin 2) :
    let root := SquareRootSidecar.isolated (2 : Canonical) sheet
    Expression.Denotation (Expression.generator (radicand := two)) 0 root.1 := by
  let root := SquareRootSidecar.isolated (2 : Canonical) sheet
  have parameter : root.2.parameter = 2 := SquareRootSidecar.isolated_parameter (2 : Canonical) sheet
  have square := PowerIdentity.ofSquare root.2.square
  rewrite [parameter] at square
  have identity : PowerIdentity root.1 2 (two.eval 0) := by
    rewrite [show two.eval 0 = 2 from DensePolynomial.eval_constant 2 0]
    exact square
  exact Expression.retain Expression.generator 0 root.1 (Expression.defined_generator 0) identity

example (sheet : Fin 2) :
    let source := retainedTwo sheet
    source.channel = (Expression.generator (radicand := two)).denote 0
      (SquareRootSidecar.isolated (2 : Canonical) sheet).1 :=
  (retainedTwo sheet).channel_readback

example (sheet : Fin 2) :
    let source := retainedTwo sheet
    let attempt := Expression.prepareInverse (Expression.generator (radicand := two))
    let reciprocal := source.reciprocal attempt ⟨Expression.defined_generator 0, by decide +kernel⟩
    NamedEquivalent reciprocal.output.name reciprocal.target.channel.name :=
  let source := retainedTwo sheet
  let attempt := Expression.prepareInverse (Expression.generator (radicand := two))
  (source.reciprocal attempt ⟨Expression.defined_generator 0, by decide +kernel⟩).equivalent

/-- A nonconstant regular radicand with its actual finite coefficients. -/
private def nonconstant : Coefficients := ⟨[1, 0, 1]⟩

example :
    ((Expression.generator (radicand := nonconstant)).mul Expression.generator).Equal
      (Expression.scalar nonconstant) := Expression.generator_square

example :
    let source := (⟨⟨0, DensePolynomial.constant 1⟩, nonconstant⟩ : Expression nonconstant)
    (source.mul source.inverse).Equal Expression.one :=
  Expression.mul_inverse _

/-- The split radicand one with a nonzero selected value of `1+Y`. -/
private def split : Expression (DensePolynomial.constant (1 : Canonical)) :=
  ⟨⟨DensePolynomial.constant 1, DensePolynomial.constant 1⟩, DensePolynomial.constant 1⟩

example : split.normNumerator.isZero = true := by decide +kernel

example : (Expression.prepareInverse split).norm.eval 0 = 0 := by decide +kernel

example : split.Defined 0 := by decide +kernel

example : (split.evaluate 0).re + (split.evaluate 0).im * (1 : Canonical) = 2 := by decide +kernel

example : NamedEquivalent (split.denote 0 (Coherence.exact 1)).name (Coherence.exact 2).name := by
  have reading : split.evaluate 0 = ⟨1, 1⟩ := by decide +kernel
  unfold Expression.denote
  rewrite [reading]
  change NamedEquivalent (CoherentNamed.add (Coherence.exact 1)
    (CoherentNamed.mul (Coherence.exact 1) (Coherence.exact 1))).name (Coherence.exact 2).name
  have addition := Exact.Arithmetic.exact_add (1 : Canonical) 1
  have sum : (1 : Canonical) + 1 = 2 := by decide +kernel
  rewrite [sum] at addition
  exact NamedEquivalent.trans
    (Sum.Congruence.coherentAdd_respects (Coherence.exact 1) (Coherence.exact 1)
      (CoherentNamed.mul (Coherence.exact 1) (Coherence.exact 1)) (Coherence.exact 1)
      (NamedEquivalent.refl _) (Mul.coherentMul_one_left (Coherence.exact 1))) addition

example : ¬(Expression.prepareInverse split).Admitted 0 := by
  intro admitted
  exact admitted.2 (by decide +kernel)

/-- The actual split-radicand check reports norm obstruction while retaining its admitted source domain. -/
private theorem split_norm_obstructed :
    let attempt := Expression.prepareInverse split
    match attempt.check 0 with
    | .normObstructed _ _ => True
    | .admitted _ => False
    | .undefined _ => False := by
  change match (Expression.prepareInverse split).check 0 with
    | .normObstructed _ _ => True
    | .admitted _ => False
    | .undefined _ => False
  unfold Expression.Inverse.check
  rewrite [dif_neg (show split.denominator.eval 0 ≠ 0 from by decide +kernel),
    dif_pos (show (Expression.prepareInverse split).norm.eval 0 = 0 from by decide +kernel)]
  exact True.intro

/-- A displayed quotient with an original cancelled zero at the coordinate zero. -/
private def cancelled : Expression two := ⟨⟨⟨[1, 0]⟩, 0⟩, ⟨[1, 0]⟩⟩

example : ¬cancelled.Defined 0 := by
  intro defined
  exact defined (by decide +kernel)

example : (Expression.cancel cancelled).reduced.Defined 0 := by decide +kernel

/-- The finite cancellation certificate reverses without swapping its two coordinate checks. -/
private theorem cancellation_reverse : (Expression.cancel cancelled).reduced.Equal cancelled :=
  (Expression.cancel cancelled).equal.symm

example : cancelled.Equal (Expression.cancel cancelled).reduced := (Expression.cancel cancelled).equal

/-- The actual inversion check retains the undefined original quotient after cancellation. -/
private theorem cancelled_source_undefined :
    let attempt := Expression.prepareInverse cancelled
    match attempt.check 0 with
    | .undefined _ => True
    | .admitted _ => False
    | .normObstructed _ _ => False := by
  change match (Expression.prepareInverse cancelled).check 0 with
    | .undefined _ => True
    | .admitted _ => False
    | .normObstructed _ _ => False
  unfold Expression.Inverse.check
  rewrite [dif_pos (show cancelled.denominator.eval 0 = 0 from by decide +kernel)]
  exact True.intro

end TestPurelib.Algebra.QuadraticPolynomial
