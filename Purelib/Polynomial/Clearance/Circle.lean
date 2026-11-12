module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Boundary
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Separation
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Quantitative polynomial clearance on the whole rational unit circle

Both rational charts have real denominator between one and two on the retained
cell. One exact fourth-power coefficient bound therefore converts the cached
cleared-coordinate margins into a uniform original-polynomial margin.
-/

namespace Purelib.Polynomial.Clearance.Circle

open Purelib.Data
open Purelib.RationalFunctions.Curve
open Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The common circle denominator has quadrance at most four on the bounded chart cell. -/
private theorem denominator_bound {parameter : Rational} (inside : Boundary.parameters.Contains parameter) :
    Gaussian.Norm.Basic.normSq (⟨parameter ^ 2 + 1, 0⟩ : Gaussian.Basic.Canonical) ≤ 4 := by
  have square : parameter ^ 2 ≤ 1 :=
    (Rat.Interval.Bounds.sq_le_squareBound inside).trans_eq (by decide)
  have sumBound : parameter ^ 2 + 1 ≤ 2 :=
    (Arithmetic.add_le_add_right_direct square 1).trans_eq (by decide)
  have sumNonnegative : 0 ≤ parameter ^ 2 + 1 :=
    add_nonneg (Arithmetic.sq_nonneg_direct _) (by decide)
  have powered := Arithmetic.pow_le_pow_direct sumNonnegative sumBound 2
  change (parameter ^ 2 + 1) ^ 2 + 0 ^ 2 ≤ 4
  calc
    (parameter ^ 2 + 1) ^ 2 + 0 ^ 2 = (parameter ^ 2 + 1) ^ 2 := by ring1
    _ ≤ (2 : Rational) ^ 2 := powered
    _ = 4 := by decide

/-- A chart clearance divided by the fixed denominator-power bound controls original evaluation. -/
private theorem chart_lower {polynomial : CoefficientPolynomial} {curve : RationalCurve}
    (data : Substitution.Retained polynomial curve)
    (clearance : Pair.Basic.Certificate data.real data.imaginary Boundary.parameters)
    {parameter : Rational} (inside : Boundary.parameters.Contains parameter)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (denominatorBound : Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter) ≤ 4)
    (floor : Rational) (floorBound : floor ≤ clearance.bound) :
    floor / (4 : Rational) ^ polynomial.coeffs.length ≤
      Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) := by
  have ceilingPositive : 0 < (4 : Rational) ^ polynomial.coeffs.length :=
    Arithmetic.pow_pos_direct (by decide) _
  have clearedLower : floor ≤ Gaussian.Norm.Basic.normSq
      ((clearedEval polynomial curve).eval (Gaussian.Cast.Path.ofCoordinate parameter)) := by
    have original := floorBound.trans (clearance.lower parameter inside)
    simpa only [data.real_readback, data.imaginary_readback, clearedReal, clearedImag,
      Dense.Gaussian.Components.eval_realPart, Dense.Gaussian.Components.eval_imagPart,
      Gaussian.Norm.Basic.normSq] using original
  have semantics := eval_clearedEval polynomial curve parameter denominatorNonzero
  rw [semantics, Gaussian.Norm.Basic.normSq_mul] at clearedLower
  have powerUpper : Gaussian.Norm.Basic.normSq
      ((clearingState polynomial curve).denominatorPower.eval (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
        (4 : Rational) ^ polynomial.coeffs.length := by
    rw [eval_denominatorPower, Gaussian.Power.normSq_pow]
    exact Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg _) denominatorBound _
  apply (Field.div_le_iff_pos ceilingPositive).mpr
  calc
    floor ≤ Gaussian.Norm.Basic.normSq
        ((clearingState polynomial curve).denominatorPower.eval (Gaussian.Cast.Path.ofCoordinate parameter)) *
          Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) := clearedLower
    _ ≤ (4 : Rational) ^ polynomial.coeffs.length *
        Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct powerUpper (Gaussian.Norm.Basic.normSq_nonneg _)
    _ = Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) *
        (4 : Rational) ^ polynomial.coeffs.length := Rat.Fraction.Field.mul_comm _ _

/-- The two full chart clearances give an explicit uniform original-polynomial margin.

The exponent is the original retained coefficient-list length. Both chart
floors and that single bound refer to the same original polynomial. -/
public theorem lower {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) (point : Gaussian.Basic.Canonical)
    (unit : Gaussian.Basic.Canonical.normSq point = 1) :
    min clearance.primary.bound clearance.reciprocal.bound / (4 : Rational) ^ polynomial.coeffs.length ≤
      Gaussian.Norm.Basic.normSq (polynomial.eval point) := by
  rcases Boundary.covers point unit with ⟨parameter, inside, equal⟩ | ⟨parameter, inside, equal⟩
  · rw [← equal]
    apply chart_lower paths.primary clearance.primary inside (circle_denominator_ne 1 parameter)
      _ _ (Basic.min_le_left _ _)
    rw [circle_denominatorAt]
    exact denominator_bound inside
  · rw [← equal]
    apply chart_lower paths.reciprocal clearance.reciprocal inside (reciprocalCircle_denominator_ne 1 parameter)
      _ _ (Basic.min_le_right _ _)
    rw [reciprocalCircle_denominatorAt]
    exact denominator_bound inside

set_option genInjectivity false in
/-- A positive uniform polynomial residual bound on the whole rational unit circle. -/
public structure Certificate (polynomial : CoefficientPolynomial) where
  /-- The retained original-polynomial quadrance margin. -/ bound : Rational
  /-- The original-polynomial margin is strictly positive. -/ positive : 0 < bound
  /-- Every rational unit-circle point satisfies this same margin. -/ lower :
    ∀ point, Gaussian.Basic.Canonical.normSq point = 1 →
      bound ≤ Gaussian.Norm.Basic.normSq (polynomial.eval point)

constructive_injectivity Certificate

namespace Certificate

/-- Equal retained rational bounds identify complete certificates of the same original polynomial.

The remaining fields are proofs of positivity and the same quantified lower
bound. No polynomial evaluation or comparison operation is performed.
-/
public theorem eq_of_bound_eq {polynomial : CoefficientPolynomial} (left right : Certificate polynomial)
    (equal : left.bound = right.bound) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Transporting the same complete certificate along a source polynomial equality preserves its retained bound. -/
public theorem transport_bound {source target : CoefficientPolynomial} (equal : source = target)
    (clearance : Certificate source) :
    (show Certificate target from equal ▸ clearance).bound = clearance.bound := by
  cases equal
  rfl

/-- Original polynomial clearance transfers to a retained norm-one rational chart.

The original clearing denominator has quadrance at least one at every
parameter. Its retained finite power therefore preserves the same original
polynomial margin without a new bounded cover search.
-/
private def onChart {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    {curve : RationalCurve} (data : Substitution.Retained polynomial curve)
    (unit : ∀ parameter, (curve.point parameter).normSq = 1)
    (denominatorNonzero : ∀ parameter, curve.denominatorAt parameter ≠ 0)
    (denominatorLower : ∀ parameter, (1 : Rational) ≤ Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter)) :
    Pair.Basic.Certificate data.real data.imaginary Boundary.parameters :=
  { bound := clearance.bound
    positive := clearance.positive
    lower := by
      intro parameter _
      have original := clearance.lower (curve.point parameter) (unit parameter)
      have powerLower : (1 : Rational) ≤ Gaussian.Norm.Basic.normSq
          ((clearingState polynomial curve).denominatorPower.eval (Gaussian.Cast.Path.ofCoordinate parameter)) := by
        rw [eval_denominatorPower, Gaussian.Power.normSq_pow]
        exact (Arithmetic.pow_le_pow_direct (by decide : (0 : Rational) ≤ 1)
          (denominatorLower parameter) polynomial.coeffs.length).trans_eq' (by
            rw [one_pow])
      have lower : clearance.bound ≤ Gaussian.Norm.Basic.normSq
          (data.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter)) := by
        rw [data.state_value, eval_clearedEval polynomial curve parameter (denominatorNonzero parameter),
          Gaussian.Norm.Basic.normSq_mul]
        calc
          clearance.bound ≤ Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) := original
          _ = 1 * Gaussian.Norm.Basic.normSq (polynomial.eval (curve.point parameter)) :=
            (Rat.Fraction.Field.one_mul _).symm
          _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct powerLower (Gaussian.Norm.Basic.normSq_nonneg _)
      rw [← data.coordinates parameter] at lower
      exact lower }

/-- The original real circle denominator has quadrance at least one at every rational parameter. -/
private theorem circle_denominator_lower (parameter : Rational) :
    (1 : Rational) ≤ Gaussian.Norm.Basic.normSq (⟨parameter ^ 2 + 1, 0⟩ : Gaussian.Basic.Canonical) := by
  have atLeastOne : (1 : Rational) ≤ parameter ^ 2 + 1 := by
    have lower := Arithmetic.add_le_add_right_direct (Arithmetic.sq_nonneg_direct parameter) 1
    simpa only [Rat.Fraction.Field.zero_add] using lower
  have square := Arithmetic.pow_le_pow_direct (by decide : (0 : Rational) ≤ 1) atLeastOne 2
  change 1 ≤ (parameter ^ 2 + 1) ^ 2 + 0 ^ 2
  calc
    (1 : Rational) = 1 ^ 2 := by decide
    _ ≤ (parameter ^ 2 + 1) ^ 2 := square
    _ = (parameter ^ 2 + 1) ^ 2 + 0 ^ 2 := by ring1

/-- Certify both same retained complete-circle charts directly from an original-polynomial margin. -/
public def onBoundary {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (paths : Boundary.Substitutions polynomial) : Boundary.Clearance paths :=
  { primary := onChart clearance paths.primary
      (fun parameter => (normSq_circle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one)
      (circle_denominator_ne 1)
      (fun parameter => by rw [circle_denominatorAt]; exact circle_denominator_lower parameter)
    reciprocal := onChart clearance paths.reciprocal
      (fun parameter => (normSq_reciprocalCircle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one)
      (reciprocalCircle_denominator_ne 1)
      (fun parameter => by rw [reciprocalCircle_denominatorAt]; exact circle_denominator_lower parameter) }

/-- Transfer the same margin along exact evaluation agreement on the whole rational circle.

The target retains its own original coefficient table. Only its values on the
same rational unit boundary are compared; the retained positive payment is
exactly the source payment.
-/
@[expose] public def transport {source target : CoefficientPolynomial}
    (clearance : Certificate source)
    (same : ∀ point : Gaussian.Basic.Canonical, point.normSq = 1 → target.eval point = source.eval point) :
    Certificate target :=
  { bound := clearance.bound
    positive := clearance.positive
    lower := fun point unit => (same point unit).symm ▸ clearance.lower point unit }

/-- Multiply two original whole-circle margins for the actual dense polynomial product. -/
@[expose] public def product {left right : CoefficientPolynomial}
    (leftClearance : Certificate left) (rightClearance : Certificate right) : Certificate (left * right) :=
  { bound := leftClearance.bound * rightClearance.bound
    positive := Arithmetic.mul_pos_direct leftClearance.positive rightClearance.positive
    lower := by
      intro point unit
      rw [Dense.Basic.DensePolynomial.eval_mul, Gaussian.Norm.Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct (leftClearance.lower point unit) (rightClearance.lower point unit)
        rightClearance.positive.le (Gaussian.Norm.Basic.normSq_nonneg _) }

/-- The target polynomial differs by at most one sixteenth of the original circle margin in quadrance. -/
@[expose] public def Close {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    (target : CoefficientPolynomial) : Prop :=
  ∀ point : Gaussian.Basic.Canonical, point.normSq = 1 →
    Gaussian.Norm.Basic.normSq (target.eval point - polynomial.eval point) ≤ clearance.bound / 16

/-- A sufficiently small original-polynomial perturbation retains a quarter-margin on the same whole circle. -/
@[expose] public def perturbation {polynomial target : CoefficientPolynomial} (clearance : Certificate polynomial)
    (close : clearance.Close target) : Certificate target :=
  { bound := clearance.bound / 4
    positive := Field.div_pos_direct clearance.positive (by decide)
    lower := by
      intro point unit
      have original := clearance.lower point unit
      have scaled := Field.divide_mono original (by decide : (0 : Rational) < 4)
      have closeAtPoint : Gaussian.Norm.Basic.normSq (polynomial.eval point - target.eval point) ≤
          Gaussian.Norm.Basic.normSq (polynomial.eval point) / 4 := by
        rw [Gaussian.Norm.Bounds.normSq_sub_symm]
        exact ((close point unit).trans
          (Field.div_le_div_of_nonneg_left_direct clearance.positive.le (by decide) (by decide))).trans scaled
      exact scaled.trans (Gaussian.Norm.Bounds.quarter_normSq_le_of_close _ _ closeAtPoint) }

/-- The perturbed certificate retains exactly one quarter of the original margin. -/
public theorem perturbation_bound {polynomial target : CoefficientPolynomial} (clearance : Certificate polynomial)
    (close : clearance.Close target) : (clearance.perturbation close).bound = clearance.bound / 4 := rfl

/-- A positive whole-circle margin excludes an exact zero at every original unit point. -/
public theorem eval_ne {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial)
    {point : Gaussian.Basic.Canonical} (unit : point.normSq = 1) : polynomial.eval point ≠ 0 := by
  intro zero
  have lower := clearance.lower point unit
  rw [zero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_lt_of_ge lower) clearance.positive

/-- A polynomial with positive whole-circle clearance is not the zero polynomial. -/
public theorem nonzero {polynomial : CoefficientPolynomial} (clearance : Certificate polynomial) :
    polynomial.isZero = false :=
  Dense.Basic.DensePolynomial.isZero_false_of_eval_ne (clearance.eval_ne Gaussian.Basic.Canonical.normSq_one)

end Certificate

set_option genInjectivity false in
/-- A quantitative margin read from the same retained whole-circle chart certificate.

The original paths and certificate remain indices. The coefficient-computed
denominator ceiling and resulting positive margin are cached with exact equations. -/
public structure Margin {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) extends Certificate polynomial where
  /-- The once-computed bound for either cleared denominator power. -/ ceiling : Rational
  /-- The ceiling uses the original coefficient-list length. -/ ceiling_eq :
    ceiling = (4 : Rational) ^ polynomial.coeffs.length
  /-- The margin uses both original chart floors and the exact retained ceiling. -/ bound_eq :
    bound = min clearance.primary.bound clearance.reciprocal.bound / ceiling

constructive_injectivity Margin

namespace Margin

/-- Compute and retain the uniform circle margin from both original chart clearances. -/
@[expose] public def prepare {polynomial : CoefficientPolynomial} (paths : Boundary.Substitutions polynomial)
    (clearance : Boundary.Clearance paths) : Margin paths clearance :=
  let ceiling := (4 : Rational) ^ polynomial.coeffs.length
  { ceiling, ceiling_eq := rfl
    toCertificate :=
      { bound := min clearance.primary.bound clearance.reciprocal.bound / ceiling
        positive := Field.div_pos_direct (Basic.lt_min clearance.primary.positive clearance.reciprocal.positive)
          (Arithmetic.pow_pos_direct (by decide) _)
        lower := Circle.lower paths clearance }
    bound_eq := rfl }

end Margin
end Purelib.Polynomial.Clearance.Circle
