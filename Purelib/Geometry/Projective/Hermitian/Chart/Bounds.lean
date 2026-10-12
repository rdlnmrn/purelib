module
import Purelib.Data.Rat.Interval.Width
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.RationalFunctions.Curve.Projective.Bounds
public import Purelib.RationalFunctions.Curve.Projective.Clearance
public import Purelib.RationalFunctions.Curve.Substitution
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RationalFunctions.Curve.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Chart

open Purelib.Geometry.Projective.Line.Hermitian

open Purelib.Polynomial

open Purelib.Polynomial.Clearance

open Purelib.RationalFunctions

open Purelib.RationalFunctions.Curve

section
public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart.BoundedChart

section

/-- Uniform lower bound for the affine curve-denominator quadrance whenever the represented point lies in a displayed
finite box. It is obtained from the chart's homogeneous-weight lower bound and the box's finite norm majorant, so no
affine compactness argument is involved. -/
@[expose] def affineDenominatorNormSqLower
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) (box : Rational.Box) :
    Fraction.Rational :=
  chart.parameterization.weightLower / (box.normSqBound + 1)

/-- The box-based lower bound for the affine denominator quadrance is strictly positive. -/
theorem affineDenominatorNormSqLower_pos
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) (box : Rational.Box) :
    0 < chart.affineDenominatorNormSqLower box :=
  Fraction.Order.Field.div_pos_direct
    chart.parameterization.weightLowerPositive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct box.normSqBound_nonneg (by decide))

/-- Every non-pole chart point inside the box satisfies the computed denominator quadrance lower bound. -/
theorem affineDenominatorNormSqLower_le
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) (box : Rational.Box)
    (parameter : Fraction.Rational)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (inside : box.Contains
      (chart.parameterization.curve.point parameter)) :
    chart.affineDenominatorNormSqLower box ≤
      Data.Gaussian.Norm.Basic.normSq (chart.parameterization.curve.denominatorAt parameter) := by
  let curve := chart.parameterization.curve
  let pointNorm := Data.Gaussian.Norm.Basic.normSq (curve.point parameter)
  let denominatorNorm := Data.Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter)
  let scale := box.normSqBound + 1
  have scalePositive : 0 < scale := by
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct box.normSqBound_nonneg (by decide)
  have pointBound : pointNorm ≤ box.normSqBound := by
    simpa only [-eq_self, -iff_self, pointNorm, curve] using box.normSq_le_normSqBound inside
  have scaleBound : pointNorm + 1 ≤ scale := by
    exact Fraction.Order.Arithmetic.add_le_add_direct pointBound le_rfl
  have weightIdentity :
      Proj.weight (chart.projective parameter) =
        (pointNorm + 1) * denominatorNorm := by
    have numeratorIdentity :=
      curve.numeratorAt_eq_point_mul_denominatorAt parameter
        denominatorNonzero
    simp only [-eq_self, -iff_self, BoundedChart.projective,
      Projective.projective,
      Proj.weight]
    rw [numeratorIdentity, Data.Gaussian.Norm.Basic.normSq_mul]
    dsimp only [pointNorm, denominatorNorm]
    ring1
  apply (Fraction.Order.Field.div_le_iff_pos scalePositive).2
  calc
    chart.parameterization.weightLower ≤
        Proj.weight (chart.projective parameter) :=
      chart.weightLower_le_projective parameter
    _ = (pointNorm + 1) * denominatorNorm := weightIdentity
    _ ≤ scale * denominatorNorm :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaleBound
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ = denominatorNorm * scale :=
      Fraction.Field.mul_comm _ _

/-- Uniform lower bound for the finite Horner denominator power over affine chart points lying in a displayed box. -/
@[expose] def affineDenominatorPowerNormSqLower
    (p : CoefficientPolynomial) {form : Hermitian.HermitianForm}
    (chart : Chart.BoundedChart form) (box : Rational.Box) : Fraction.Rational :=
  chart.affineDenominatorNormSqLower box ^ p.coeffs.length

/-- The retained denominator-power quadrance bound is strictly positive at every polynomial degree. -/
theorem affineDenominatorPowerNormSqLower_pos
    (p : CoefficientPolynomial) {form : Hermitian.HermitianForm}
    (chart : Chart.BoundedChart form) (box : Rational.Box) :
    0 < chart.affineDenominatorPowerNormSqLower p box :=
  Fraction.Order.Arithmetic.pow_pos_direct
    (chart.affineDenominatorNormSqLower_pos box) p.coeffs.length

/-- The finite Horner denominator power at an in-box non-pole parameter satisfies the computed quadrance lower bound. -/
theorem affineDenominatorPowerNormSqLower_le
    (p : CoefficientPolynomial) {form : Hermitian.HermitianForm}
    (chart : Chart.BoundedChart form) (box : Rational.Box) (parameter : Fraction.Rational)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (inside : box.Contains
      (chart.parameterization.curve.point parameter)) :
    chart.affineDenominatorPowerNormSqLower p box ≤
      Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearingState p
          chart.parameterization.curve).denominatorPower.eval
            (Path.ofCoordinate parameter)) := by
  rw [Curve.eval_denominatorPower, Power.normSq_pow]
  exact Fraction.Order.Arithmetic.pow_le_pow_direct
    (chart.affineDenominatorNormSqLower_pos box).le
    (chart.affineDenominatorNormSqLower_le box parameter
      denominatorNonzero inside) p.coeffs.length

/-- Pole-safe coefficient for squared-chordal variation. Unlike the older affine-denominator coefficient, this divides
by a lower bound for the full homogeneous weight and therefore remains valid when the affine chart passes through
infinity. -/
@[expose] def uniformChordalVariationCoefficient
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) : Fraction.Rational :=
  Projective.crossVariationCoefficient
      chart.parameterization.curve chart.cell.interval /
    chart.parameterization.weightLower ^ 2

/-- The homogeneous-weight variation coefficient of the bounded chart is nonnegative. -/
theorem uniformChordalVariationCoefficient_nonneg
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) :
    0 ≤ chart.uniformChordalVariationCoefficient :=
  Fraction.Order.Field.div_nonneg_direct
    (Projective.crossVariationCoefficient_nonneg
      chart.parameterization.curve chart.cell.interval)
    (Fraction.Order.Arithmetic.pow_pos_direct
      chart.parameterization.weightLowerPositive 2).le

/-- Genuine squared-chordal variation of a bounded chart, with no affine denominator-clearance hypothesis and hence no
exceptional pole case. -/
theorem chordalSq_le_uniform
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form)
    {left right : Fraction.Rational}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    Chordal.Basic.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * (left - right) ^ 2 := by
  let leftPoint := chart.projective left
  let rightPoint := chart.projective right
  let actualDenominator :=
    Proj.weight leftPoint *
      Proj.weight rightPoint
  let lowerSq := chart.parameterization.weightLower ^ 2
  let upper :=
    Projective.crossVariationCoefficient
        chart.parameterization.curve chart.cell.interval *
      (left - right) ^ 2
  have leftWeightPositive :
      0 < Proj.weight leftPoint :=
    chart.projective_weight_pos left
  have rightWeightPositive :
      0 < Proj.weight rightPoint :=
    chart.projective_weight_pos right
  have actualPositive : 0 < actualDenominator :=
    Fraction.Order.Arithmetic.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have lowerSqPositive : 0 < lowerSq :=
    Fraction.Order.Arithmetic.pow_pos_direct
      chart.parameterization.weightLowerPositive 2
  have actualLower : lowerSq ≤ actualDenominator := by
    dsimp only [lowerSq, actualDenominator]
    simpa only [-eq_self, -iff_self, pow_two] using
      (Fraction.Order.Arithmetic.mul_le_mul_direct
        (chart.weightLower_le_projective left)
        (chart.weightLower_le_projective right)
        chart.parameterization.weightLowerPositive.le
        leftWeightPositive.le)
  have upperNonnegative : 0 ≤ upper :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Projective.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right))
  calc
    Chordal.Basic.chordalSq leftPoint rightPoint =
        Data.Gaussian.Norm.Basic.normSq (Proj.cross leftPoint rightPoint) /
          actualDenominator := rfl
    _ ≤ upper / actualDenominator := by
      apply (Fraction.Order.Field.div_le_iff_pos actualPositive).2
      have cancel : upper / actualDenominator * actualDenominator = upper :=
        Fraction.Field.div_mul_cancel_of_ne upper
          actualDenominator actualPositive.ne'
      rw [cancel]
      exact Projective.normSq_cross_le
        chart.parameterization.curve chart.cell.interval
          leftInside rightInside
    _ ≤ upper / lowerSq :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        upperNonnegative lowerSqPositive actualLower
    _ = chart.uniformChordalVariationCoefficient * (left - right) ^ 2 := by
      simp only [-eq_self, -iff_self,
        uniformChordalVariationCoefficient,
        Algebra.Field.ExplicitField.div_eq_mul_inv]
      rw [Fraction.Field.mul_assoc,
        Fraction.Field.mul_comm ((left - right) ^ 2),
        ← Fraction.Field.mul_assoc]

/-- Width-only pole-safe squared-chordal diameter bound for a complete bounded chart. -/
theorem chordalSq_le_uniformWidth
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form)
    {left right : Fraction.Rational}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    Chordal.Basic.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient *
        (Interval.Bounds.width chart.cell.interval) ^ 2 :=
  (chart.chordalSq_le_uniform leftInside rightInside).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Interval.parameter_sub_sq_le_width_sq
        chart.cell.interval leftInside rightInside)
      chart.uniformChordalVariationCoefficient_nonneg)

/-- The homogeneous cross product of any two parameters in a bounded chart shrinks quadratically with the displayed
parameter-cell width, even across an affine pole. -/
theorem normSq_cross_le_width
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form)
    {left right : Fraction.Rational}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq (Proj.cross
        (chart.projective left) (chart.projective right)) ≤
      Projective.crossVariationCoefficient
          chart.parameterization.curve chart.cell.interval *
        (Interval.Bounds.width chart.cell.interval) ^ 2 := by
  have crossBound :=
    Projective.normSq_cross_le
      chart.parameterization.curve chart.cell.interval
      leftInside rightInside
  have widthBound :=
    Interval.parameter_sub_sq_le_width_sq
      chart.cell.interval leftInside rightInside
  exact crossBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthBound
      (Projective.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval))

/-- Once a positive affine-denominator clearance is supplied, the same bounded chart has a squared-chordal image
diameter proportional to width squared. -/
theorem chordalSq_le_width
    {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form)
    (clearance : Pair.Basic.Certificate
      (Coordinates.denominatorReal
        chart.parameterization.curve)
      (Coordinates.denominatorImaginary
        chart.parameterization.curve)
      chart.cell.interval)
    {left right : Fraction.Rational}
    (leftInside : chart.cell.interval.Contains left)
    (rightInside : chart.cell.interval.Contains right) :
    Chordal.Basic.chordalSq
        (chart.projective left) (chart.projective right) ≤
      Projective.chordalVariationCoefficient
          chart.parameterization.curve chart.cell.interval clearance *
        (Interval.Bounds.width chart.cell.interval) ^ 2 :=
  Projective.chordalSq_projective_le_width
    chart.parameterization.curve chart.cell.interval clearance
      leftInside rightInside

end
end Purelib.Geometry.Projective.Hermitian.Chart.BoundedChart

end
