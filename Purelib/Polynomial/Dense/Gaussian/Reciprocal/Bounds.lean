module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> GaussianPolynomial

/-!
# Reciprocal polynomial bounds at the coefficient radius

The original coefficient radius controls the reversed polynomial throughout
its reciprocal disk. A quarter-sized tail bound supplies a uniform positive
radicand margin, including the chart origin.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

open Purelib.Data Purelib.Data.Rat Purelib.Polynomial
open Purelib.Algebra.Semiring.Normalization (product_pow)

public section

/-- Four times the lower coefficient weight fits below the outer-radius bound.

A nonzero polynomial has positive leading quadrance. Multiplying the scalar
quotient bound by that same quadrance yields the coefficient-radius inequality. -/
theorem four_weight_le (polynomial : GaussianPolynomial) (nonzero : polynomial.isZero =
  false) :
    4 * Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial ≤
      Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff *
        Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2 := by
  let weight := Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial
  let leading := Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff
  let quotient := weight / leading
  have leadingPositive : 0 < leading :=
    Gaussian.Norm.Basic.normSq_pos (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero)
  have quotientNonnegative : 0 ≤ quotient :=
    Fraction.Order.Field.div_nonneg_direct (Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight_nonneg
      polynomial) leadingPositive.le
  have quotient_eq : leading * quotient = weight := by
    rw [_root_.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ leadingPositive.ne'
  have elementary : 4 * quotient ≤ (quotient + 1) ^ 2 := by
    calc
      _ ≤ 4 * quotient + (quotient - 1) ^ 2 :=
        le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have radiusBound : quotient + 1 ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial :=
    Fraction.Order.Basic.le_max_right _ _
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
    (add_nonneg quotientNonnegative (by decide : (0 : Fraction.Rational) ≤ 1)) radiusBound 2
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (elementary.trans squares) leadingPositive.le
  change 4 * weight ≤ _
  calc
    _ = leading * (4 * quotient) := by rw [show leading * (4 * quotient) = 4 * (leading * quotient) by ring1,
      quotient_eq]
    _ ≤ _ := scaled

/-- The reversed nonconstant tail equals a scaled lower-term inverse evaluation.

For a positive-degree polynomial and nonzero point, the original leading term
cancels using the product of the point and inverse-point powers. -/
private theorem reversed_tail (polynomial : GaussianPolynomial) (degreePositive : 0 <
  polynomial.natDegree)
    (point : Gaussian.Basic.Canonical) (pointNonzero : point ≠ 0) :
    (Dense.Gaussian.Reciprocal.reversed polynomial).eval point - polynomial.leadingCoeff =
      point ^ polynomial.natDegree * (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial polynomial).eval point⁻¹ :=
        open Purelib.Algebra.Field in by
  have powers : point ^ polynomial.natDegree * (point⁻¹) ^ polynomial.natDegree = 1 := by
    rw [← product_pow, ExplicitField.mul_inv_cancel point pointNonzero, one_pow]
  rw [Dense.Gaussian.Reciprocal.reversed_identity polynomial point pointNonzero,
    ← Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eval degreePositive,
      Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_eval degreePositive]
  calc
    _ = polynomial.leadingCoeff * (point ^ polynomial.natDegree * (point⁻¹) ^ polynomial.natDegree) +
        point ^ polynomial.natDegree * (Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial polynomial).eval point⁻¹ -
          polynomial.leadingCoeff := by ring1
    _ = _ := by rw [powers]; ring1

/-- The original coefficient weight bounds the reversed tail quadrance.

The point has quadrance at most one and the polynomial has positive degree.
Zero gives an explicit constant readback; elsewhere inverse powers cancel. -/
theorem tail_bound (polynomial : GaussianPolynomial) (degreePositive : 0 <
  polynomial.natDegree)
    (point : Gaussian.Basic.Canonical) (unitBound : Data.Gaussian.Norm.Basic.normSq point ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Reciprocal.reversed polynomial).eval point -
      polynomial.leadingCoeff) ≤
      Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial * Data.Gaussian.Norm.Basic.normSq
        point := open Purelib.Algebra.Field in by
  by_cases zero : point = 0
  · subst point
    rw [Dense.Gaussian.Reciprocal.reversed_origin, _root_.sub_self, Gaussian.Norm.Basic.normSq_zero]
    have zeroProduct : Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial * 0 = (0 :
      Fraction.Rational) := by ring1
    rw [zeroProduct]
  · have reciprocalNorm : Data.Gaussian.Norm.Basic.normSq point⁻¹ = (Data.Gaussian.Norm.Basic.normSq point)⁻¹ :=
      by rw [Gaussian.Field.inv_eq, Gaussian.Field.normSq_inv point zero]
    have inverseLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq point⁻¹ := by
      rw [reciprocalNorm]
      have inverse := Fraction.Order.Field.inv_le_inv_of_pos_direct (Gaussian.Norm.Basic.normSq_pos zero) unitBound
      simpa only [show (1 : Fraction.Rational)⁻¹ = 1 from by decide] using inverse
    have upper : Data.Gaussian.Norm.Basic.normSq point⁻¹ ≤ 2 * Data.Gaussian.Norm.Basic.normSq point⁻¹ := by
      calc
        _ ≤ Data.Gaussian.Norm.Basic.normSq point⁻¹ + Data.Gaussian.Norm.Basic.normSq point⁻¹ :=
          le_add_of_nonneg_right (Gaussian.Norm.Basic.normSq_nonneg _)
        _ = _ := by ring1
    have lower := Dense.Gaussian.Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive upper
      inverseLower
    rw [reversed_tail polynomial degreePositive point zero, Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow]
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg point) polynomial.natDegree)
    apply scaled.trans_eq
    have cancel : Data.Gaussian.Norm.Basic.normSq point * Data.Gaussian.Norm.Basic.normSq point⁻¹ = 1 := by
      rw [← Gaussian.Norm.Basic.normSq_mul, ExplicitField.mul_inv_cancel point zero, Gaussian.Norm.Basic.normSq_one]
    have degree : polynomial.natDegree = (polynomial.natDegree - 1) + 1 := by omega
    have step := congrArg (fun exponent => Data.Gaussian.Norm.Basic.normSq point ^ exponent) degree
    rw [pow_succ] at step
    rw [step]
    calc
      _ = Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial * Data.Gaussian.Norm.Basic.normSq
        point *
          (Data.Gaussian.Norm.Basic.normSq point * Data.Gaussian.Norm.Basic.normSq point⁻¹) ^
            (polynomial.natDegree - 1) := by rw [product_pow]; ring1
      _ = _ := by rw [cancel, one_pow]; ring1

/-- The coefficient-computed outer radius has square at least one. -/
theorem radius_square_one_le (polynomial : GaussianPolynomial) : 1 ≤
  Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2 := by
  simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct
    (by decide : (0 : Fraction.Rational) ≤ 1) (Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius
      polynomial) 2

/-- The disk is defined by a denominator-cleared inequality at the same
coefficient radius as the original outer square. -/
@[expose] def InDisk (polynomial : GaussianPolynomial) (point :
  Gaussian.Basic.Canonical) : Prop :=
  Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2 * Data.Gaussian.Norm.Basic.normSq point ≤ 1

/-- The denominator-cleared reciprocal-disk condition implies quadrance at most one. -/
theorem disk_unit_bound {polynomial : GaussianPolynomial} {point :
  Gaussian.Basic.Canonical} (inside :
  InDisk polynomial point) :
    Data.Gaussian.Norm.Basic.normSq point ≤ 1 := by
  calc
    _ = 1 * Data.Gaussian.Norm.Basic.normSq point := by ring1
    _ ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2 * Data.Gaussian.Norm.Basic.normSq
      point :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (radius_square_one_le polynomial)
        (Gaussian.Norm.Basic.normSq_nonneg point)
    _ ≤ _ := inside

/-- On the reciprocal disk, four times the reversed-tail quadrance is bounded by the original leading-coefficient
quadrance. -/
theorem disk_tail_bound (polynomial : GaussianPolynomial) (degreePositive : 0 <
  polynomial.natDegree)
    (point : Gaussian.Basic.Canonical) (inside : InDisk polynomial point) :
    4 * Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Reciprocal.reversed polynomial).eval point -
      polynomial.leadingCoeff) ≤ Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff := by
  have tail := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (tail_bound polynomial degreePositive point (disk_unit_bound inside)) (by decide : (0 : Fraction.Rational) ≤ 4)
  have weight := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (four_weight_le polynomial (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive))
      (Gaussian.Norm.Basic.normSq_nonneg point)
  have radius := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside (Gaussian.Norm.Basic.normSq_nonneg
    polynomial.leadingCoeff)
  calc
    _ ≤ 4 * (Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial *
      Data.Gaussian.Norm.Basic.normSq point) := tail
    _ = (4 * Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight polynomial) *
      Data.Gaussian.Norm.Basic.normSq point := by
      ring1
    _ ≤ (Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff *
      Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2) * Data.Gaussian.Norm.Basic.normSq
      point := weight
    _ = Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff *
      (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ^ 2 * Data.Gaussian.Norm.Basic.normSq
      point) := by
      ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff * 1 := radius
    _ = _ := by ring1

/-- A uniform positive radicand margin on the entire reciprocal disk,
not just on boundary samples or a finite list of corners. -/
theorem disk_lower (polynomial : GaussianPolynomial) (degreePositive : 0 <
  polynomial.natDegree)
    (point : Gaussian.Basic.Canonical) (inside : InDisk polynomial point) :
    Data.Gaussian.Norm.Basic.normSq polynomial.leadingCoeff / 4 ≤ Data.Gaussian.Norm.Basic.normSq
      ((Dense.Gaussian.Reciprocal.reversed polynomial).eval point) :=
  Gaussian.Norm.Bounds.lower_of_tail _ _ (disk_tail_bound polynomial degreePositive point
    inside)

end

end Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
