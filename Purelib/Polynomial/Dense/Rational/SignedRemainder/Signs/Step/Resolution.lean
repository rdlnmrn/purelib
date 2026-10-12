module
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Sign.Products
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Pair.Resolution
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Dominance
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Prepare
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step
import Purelib.Tactic.Ring

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Resolution

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Rat.Fraction.Order

/-- The signed-step scanner succeeds under pair resolution and quotient dominance.

The head sign is already certified and the middle polynomial remains unresolved; clearance of the next pair then
supplies the opposite outer signs required by the scanner. -/
public theorem signedStepCellCertificate?_isSome_of_resolution
    {p q : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    {head : Dense.Rational.Sign.Interval.Basic.Certificate p interval}
    (headFound : Dense.Rational.Sign.Interval.Prepare.certificate? p interval = some head)
    (qNone : Dense.Rational.Sign.Interval.Prepare.certificate? q interval = none)
    (rightClearance : Clearance.Pair.Basic.Certificate q
      (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) interval)
    (rightResolution : Dense.Rational.Sign.Pair.Resolution.PairResolution rightClearance)
    (dominance : Dense.Rational.SignedRemainder.Signs.Dominance.DominanceResolution q
      (Dense.Basic.DensePolynomial.divMod p q).quotient
      (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) rightClearance) :
    (Dense.Rational.SignedRemainder.Signs.Step.Prepare.signedStepCellCertificate? p q interval).isSome = true := by
  let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
  have qUnresolved : ¬(
      Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound q interval *
          Interval.Radius.sampleRadiusSq interval interval.lower <
        q.eval interval.lower ^ 2) := by
    intro margin
    have some := (Dense.Rational.Sign.Interval.Prepare.certificate?_isSome_iff q interval).2 margin
    rw [qNone] at some
    contradiction
  have nextMargin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound next interval *
      Interval.Radius.sampleRadiusSq interval interval.lower <
      next.eval interval.lower ^ 2 :=
    Dense.Rational.Sign.Pair.Resolution.second_margin_of_first_unresolved rightClearance rightResolution qUnresolved
  have headMargin := Dense.Rational.Sign.Interval.Prepare.certificate?_some_margin headFound
  have productSquares :
      (q.eval interval.lower * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval interval.lower) ^ 2 <
        next.eval interval.lower ^ 2 := by
    exact Dense.Rational.SignedRemainder.Signs.Dominance.product_eval_sq_lt_next_eval_sq_of_dominance
      rightClearance dominance qUnresolved
  have outerOpposite : p.eval interval.lower * next.eval interval.lower < 0 := by
    have step := Dense.Rational.SignedRemainder.Evaluation.signedStep_eval_identity p q interval.lower
    change p.eval interval.lower =
      q.eval interval.lower * (Dense.Basic.DensePolynomial.divMod p q).quotient.eval interval.lower -
        next.eval interval.lower at step
    rw [step]
    exact Data.Rat.Sign.Products.sub_mul_neg_of_sq_lt_sq productSquares
  unfold Dense.Rational.SignedRemainder.Signs.Step.Prepare.signedStepCellCertificate?
  dsimp only
  rw [dif_pos headMargin, dif_pos nextMargin, dif_pos outerOpposite]
  rfl

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Resolution
