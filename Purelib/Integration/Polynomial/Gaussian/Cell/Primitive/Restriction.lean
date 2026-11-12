module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Data.List.Reverse
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Restricted integrals from the same retained primitive residual

An existing affine polynomial restriction retains the actual child model.
The original primitive and derivative residual control its increment on
any admitted parameter subinterval, with the squared interval length kept
explicit. Neither a primitive constant nor a new derivative bound is given.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Primitive

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)

/-- The exact displaced primitive reads the original polynomial integral between any two actual parameter values. -/
theorem displacedPrimitive_increment_between (cell : Basic.CellModel) (first last : Canonical) :
    (DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox).value.eval last -
      (DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox).value.eval first =
      cell.displacement * Ascending.Gaussian.Integral.definiteIntegral cell.polynomial first last := by
  let scaled := Ascending.Gaussian.Arithmetic.scale cell.displacement cell.polynomial
  have reverseTable :
      (⟨(displacedPolynomial cell).coeffs.reverse⟩ : Ascending.Gaussian.CoefficientPolynomial) = scaled := by
    change (⟨scaled.coefficients.reverse.reverse⟩ : Ascending.Gaussian.CoefficientPolynomial) = scaled
    rewrite [Purelib.Data.List.Reverse.reverse_reverse]
    rfl
  change (Dense.Gaussian.Antiderivative.denseAntiderivative (displacedPolynomial cell)).eval last -
    (Dense.Gaussian.Antiderivative.denseAntiderivative (displacedPolynomial cell)).eval first = _
  rewrite [Dense.Gaussian.Antiderivative.denseAntiderivative, reverseTable,
    Ascending.Gaussian.Dense.Evaluation.toDense_eval, Ascending.Gaussian.Dense.Evaluation.toDense_eval]
  exact Ascending.Gaussian.Integral.definiteIntegral_scale cell.displacement cell.polynomial first last

namespace Comparison

/-- The original residual controls its same primitive increment against the actual cached restricted-cell integral.

The existing derivative and residual caches supply the whole unit-interval
bound. Finite primitive comparison then retains the original orientation
and squared parameter length. The restricted integral consumes the actual
supplied coefficient cache, including for repeated or reversed endpoints.
-/
theorem restricted_integral_error_le {cell : Basic.CellModel} (comparison : Comparison cell)
    {first last : Fraction.Rational}
    (cached : Ascending.Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last))
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    Norm.Basic.normSq
      (comparison.value.eval (Cast.Path.ofCoordinate last) -
        comparison.value.eval (Cast.Path.ofCoordinate first) - (Cell.Restriction.model cell cached).integralSample) ≤
      2 * comparison.bound * (last - first) ^ 2 := by
  let left := Dense.Gaussian.Primitive.Certificate.derivativePrimitive comparison.value unitBox
  let right := DensePrimitive.ofPolynomial (displacedPolynomial cell) unitBox
  have estimate := Dense.Gaussian.Primitive.Segment.Comparison.DensePrimitive.difference_increment_le
    left right 1 0 1 (of_decide_eq_true rfl) unitInterval
    (fun _ inside => unitLine_inside inside) (fun _ inside => unitLine_inside inside)
    comparison.bound
    (by
      intro input inside
      rewrite [Basic.one_mul]
      exact comparison.derivative_error_le inside)
    (first := last) (last := first) lastInside firstInside
  have point (input : Fraction.Rational) : Affine.line (0 : Canonical) 1 input = Cast.Path.ofCoordinate input := by
    change (0 : Canonical) + Cast.Path.ofCoordinate input * 1 = Cast.Path.ofCoordinate input
    rewrite [Basic.mul_one, Basic.zero_add]
    rfl
  rewrite [point last, point first, Basic.one_mul,
    show Norm.Basic.normSq (1 : Canonical) = 1 from of_decide_eq_true rfl,
    Fraction.Field.mul_one_direct, displacedPrimitive_increment_between,
    ← Cell.Restriction.integralSample_eq cell cached] at estimate
  exact estimate

end Comparison

end Purelib.Integration.Polynomial.Gaussian.Cell.Primitive

end
