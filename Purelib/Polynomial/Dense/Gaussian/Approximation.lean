module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field

/-!
# Polynomial evaluation on retained finite approximations

The coefficient-computed box bounds control evaluation of the original sample
program. Each output sample uses that original input index, and refinement
requests are paid through the same retained input approximation.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Approximation

open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat

/-- Evaluate the original polynomial at every retained input sample inside its supplied box.

One coefficient fold supplies the value and sensitivity bounds. Refinement
divides the requested squared tolerance by the positive sensitivity and uses
the original input's refinement operation and starting index.
-/
@[expose] def evaluate (polynomial : CoefficientPolynomial) (ambient : Box)
    (input : ApproximationData) (inside : ∀ index, ambient.Contains (input.sample index)) :
    ApproximationData :=
  let bounds := Bounds.Box.denseHornerNormBounds polynomial ambient
  let multiplier := max 1 bounds.slope
  have positive : 0 < multiplier := Bounds.Box.denseLipschitzBound_pos polynomial ambient
  { sample := fun index => polynomial.eval (input.sample index)
    radiusSq := fun index => multiplier * input.radiusSq index
    radiusSq_nonneg := fun index => Fraction.Order.Arithmetic.mul_nonneg_direct
      positive.le (input.radiusSq_nonneg index)
    later_close := by
      intro earlier later order
      exact (Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
        (inside later) (inside earlier)).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (input.later_close order) positive.le)
    refineIndex := fun current target targetPositive =>
      input.refineIndex current (target / multiplier)
        (Fraction.Order.Field.div_pos_direct targetPositive positive)
    refineIndex_ge := fun current target targetPositive =>
      input.refineIndex_ge current (target / multiplier)
        (Fraction.Order.Field.div_pos_direct targetPositive positive)
    refineIndex_accurate := by
      intro current target targetPositive
      have accurate := input.refineIndex_accurate current (target / multiplier)
        (Fraction.Order.Field.div_pos_direct targetPositive positive)
      rewrite [Fraction.Field.mul_comm]
      exact (Fraction.Order.Field.lt_div_iff_pos positive).mp accurate
    centerBound := bounds.value
    centerBound_nonneg := (Bounds.Box.denseHornerNormBounds_nonneg polynomial ambient).1
    sample_bounded := fun index => Bounds.Box.normSq_eval_le_denseEvalNormBound
      polynomial (inside index) }

/-- Read the polynomial evaluation of the original sample at its unchanged finite index. -/
theorem evaluate_sample (polynomial : CoefficientPolynomial) (ambient : Box)
    (input : ApproximationData) (inside : ∀ index, ambient.Contains (input.sample index))
    (index : Nat) :
    (evaluate polynomial ambient input inside).sample index = polynomial.eval (input.sample index) := rfl

/-- Polynomial evaluation preserves an actual comparison between two retained inputs in the same box.

The original comparison computes both later indices at the coefficient-derived
input tolerance. Its all-later sample bound is transported through polynomial
sensitivity without replacing either input or its starting state.
-/
@[expose] def respects (polynomial : CoefficientPolynomial) (ambient : Box)
    {first second : ApproximationData}
    (firstInside : ∀ index, ambient.Contains (first.sample index))
    (secondInside : ∀ index, ambient.Contains (second.sample index))
    (equivalent : Equivalent first second) :
    Equivalent (evaluate polynomial ambient first firstInside)
      (evaluate polynomial ambient second secondInside) where
  compare firstStart secondStart target targetPositive := by
    let multiplier := Bounds.Box.denseLipschitzBound polynomial ambient
    have positive := Bounds.Box.denseLipschitzBound_pos polynomial ambient
    let comparison := equivalent.compare firstStart secondStart (target / multiplier)
      (Fraction.Order.Field.div_pos_direct targetPositive positive)
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro firstLater secondLater firstOrder secondOrder
          change Purelib.Data.Gaussian.Norm.Basic.normSq
            (polynomial.eval (first.sample firstLater) - polynomial.eval (second.sample secondLater)) < target
          have small := (Fraction.Order.Field.lt_div_iff_pos positive).mp
            (comparison.close firstOrder secondOrder)
          rewrite [Fraction.Field.mul_comm] at small
          exact (Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
            (firstInside firstLater) (secondInside secondLater)).trans_lt small }

end Purelib.Polynomial.Dense.Gaussian.Approximation

end
