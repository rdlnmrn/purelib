module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary.Budget
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Data
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Dimensions

open Purelib.Polynomial.Clearance.Box.Boundary.Basic
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants

open Fraction.Order

/-- Protected-boundary radius with the admitted Lipschitz majorant in place
of the newly revealed polynomial's exact scan.

The same retained clearance and admitted Lipschitz majorant determine the quotient threshold alongside the two original
one-sixteenth side widths. -/
@[expose] def majorizedProtectedRadius
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) : Fraction.Rational :=
  min (1 / Box.Boundary.Budget.protectedBoundaryScale)
    (min (clearance.bound / (2 * majorants.lipschitz))
      (min (ambient.widthX / 16) (ambient.widthY / 16)))

/-- The retained-majorant protected radius equals its numerical data formula. -/
@[simp] theorem majorizedProtectedRadius_eq_data
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) :
    majorizedProtectedRadius clearance majorants =
      Box.Boundary.Budget.predictedProtectedRadiusData ambient clearance.bound
        majorants.lipschitz := rfl

/-- The retained-majorant protected radius is positive on a proper box.

Positive clearance and Lipschitz bounds combine with the two positive side widths. -/
theorem majorizedProtectedRadius_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) (proper : ambient.Proper) :
    0 < majorizedProtectedRadius clearance majorants := by
  have scalePositive : 0 < Box.Boundary.Budget.protectedBoundaryScale := by
    unfold Box.Boundary.Budget.protectedBoundaryScale
    exact Arithmetic.mul_pos_direct
      (Arithmetic.mul_pos_direct (by decide) (by decide))
      (by decide)
  exact Basic.lt_min
    (Field.div_pos_direct (by decide) scalePositive)
    (Basic.lt_min
      (Field.div_pos_direct clearance.positive
        (Arithmetic.mul_pos_direct
          (by decide) majorants.lipschitz_pos))
      (Basic.lt_min
        (Field.div_pos_direct
          (Arithmetic.sub_pos_direct proper.1) (by decide))
        (Field.div_pos_direct
          (Arithmetic.sub_pos_direct proper.2) (by decide))))

/-- A Lipschitz majorant yields a radius below the exact protected radius.

Increasing the positive denominator decreases the clearance ratio; the other defining minima are unchanged. -/
theorem majorizedProtectedRadius_le
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) :
    majorizedProtectedRadius clearance majorants ≤
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
  unfold majorizedProtectedRadius Clearance.Box.ProtectedRadius.protectedBoundaryRadius
  apply le_min
  · exact Basic.min_le_left _ _
  · apply le_min
    · have actualDenominatorPositive :
          0 < (2 : Fraction.Rational) * Bounds.Box.denseLipschitzBound p ambient :=
        Arithmetic.mul_pos_direct (by decide)
          (Bounds.Box.denseLipschitzBound_pos p ambient)
      have denominatorOrder :
          2 * Bounds.Box.denseLipschitzBound p ambient ≤ 2 * majorants.lipschitz :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          majorants.lipschitz_upper (by decide)
      exact ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)).trans
        (Field.div_le_div_of_nonneg_left_direct
          clearance.positive.le actualDenominatorPositive denominatorOrder)
    · exact (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)

/-- Radius which is guaranteed to lie below the actual extraction radius of
every polynomial satisfying `majorants`.

The original protected radius, derivative separation margin, Taylor ceiling and requested epsilon are retained in the
exact same nested minima. -/
@[expose] def majorizedExtractionRadius
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  min
    (min ((1 / 2 : Fraction.Rational) *
        majorizedProtectedRadius clearance majorants)
      (min 1 (separation.margin / (72 * majorants.taylor))))
    ((1 / 8 : Fraction.Rational) * epsilon)

/-- The retained-majorant extraction radius equals its numerical data formula. -/
@[simp] theorem majorizedExtractionRadius_eq_data
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) (epsilon : Fraction.Rational) :
    majorizedExtractionRadius separation clearance majorants epsilon =
      Data.predictedExtractionRadiusData ambient separation.margin clearance.bound
        majorants.lipschitz majorants.taylor epsilon := rfl

/-- The extraction radius is positive for a proper box and positive accuracy request.

The protected-boundary, derivative-separation, Taylor and requested-size constraints each contribute a positive term. -/
theorem majorizedExtractionRadius_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) (proper : ambient.Proper)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < majorizedExtractionRadius separation clearance majorants epsilon := by
  exact Basic.lt_min
    (Basic.lt_min
      (Arithmetic.mul_pos_direct (by decide)
        (majorizedProtectedRadius_pos clearance majorants proper))
      (Basic.lt_min (by decide)
        (Field.div_pos_direct separation.margin_pos
          (Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 72) (by decide)) majorants.taylor_pos))))
    (Arithmetic.mul_pos_direct (by decide) epsilonPositive)

/-- The retained-majorant extraction radius is no larger than the exact radius.

The supplied Lipschitz and Taylor upper bounds strengthen the corresponding denominator constraints. -/
theorem majorizedExtractionRadius_le
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient)
    (epsilon : Fraction.Rational) :
    majorizedExtractionRadius separation clearance majorants epsilon ≤
      Separated.separatedExtractionRadius separation ambient clearance epsilon := by
  unfold majorizedExtractionRadius Separated.separatedExtractionRadius
  apply le_min
  · apply (Basic.min_le_left _ _).trans
    unfold Separated.separatedBaseExtractionRadius
    apply le_min
    · exact (Basic.min_le_left _ _).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (majorizedProtectedRadius_le clearance majorants) (by decide))
    · apply (Basic.min_le_right _ _).trans
      apply le_min
      · exact Basic.min_le_left _ _
      · have actualDenominatorPositive :
            0 < (72 : Fraction.Rational) * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient :=
          Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
            (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
        have denominatorOrder :
            72 * Bounds.Box.Taylor.denseTaylorRemainderBound p ambient ≤
              72 * majorants.taylor :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct
            majorants.taylor_upper
            (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide)).le
        exact (Basic.min_le_right _ _).trans
          (Field.div_le_div_of_nonneg_left_direct
            separation.margin_pos.le actualDenominatorPositive denominatorOrder)
  · exact Basic.min_le_right _ _

/-- Twice the retained derivative ceiling.

This coefficient is the linearization majorant before the radius factor is applied. -/
@[expose] def majorizedLinearizationMajorant
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (majorants : Majorants.ExtractionMajorants p ambient) : Fraction.Rational :=
  2 * majorants.derivative

/-- The retained linearization coefficient is positive. -/
theorem majorizedLinearizationMajorant_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (majorants : Majorants.ExtractionMajorants p ambient) :
    0 < majorizedLinearizationMajorant majorants :=
  Arithmetic.mul_pos_direct
    (by decide) majorants.derivative_pos

/-- Predicted positive clearance bound available before the admitted
polynomial is read.

The cached numerical formula squares the retained derivative-margin radius bound and divides by the same positive
derivative ceiling. -/
@[expose] def predictedExtractionClearance
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  let radius := majorizedExtractionRadius separation clearance majorants epsilon
  let margin := separation.margin * radius ^ 2 / 2
  margin ^ 2 / (8 * majorants.derivative)

/-- The predicted clearance equals the formula on its retained numerical inputs. -/
@[simp] theorem predictedExtractionClearance_eq_data
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) (epsilon : Fraction.Rational) :
    predictedExtractionClearance separation clearance majorants epsilon =
      Data.predictedExtractionClearanceData ambient separation.margin
        clearance.bound majorants.lipschitz majorants.taylor
        majorants.derivative epsilon := rfl

/-- Predicted extraction clearance is positive for a proper box and positive request.

The positive extraction radius and derivative margin give a positive squared numerator over the retained positive
derivative ceiling. -/
theorem predictedExtractionClearance_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient)
    (majorants : Majorants.ExtractionMajorants p ambient) (proper : ambient.Proper)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionClearance separation clearance majorants epsilon := by
  have radiusPositive := majorizedExtractionRadius_pos separation clearance
    majorants proper epsilonPositive
  have marginPositive : 0 < separation.margin *
      majorizedExtractionRadius separation clearance majorants epsilon ^ 2 / 2 :=
    Field.div_pos_direct
      (Arithmetic.mul_pos_direct separation.margin_pos
        (Arithmetic.pow_pos_direct radiusPositive 2))
      (by decide)
  exact Field.div_pos_direct
    (Arithmetic.pow_pos_direct marginPositive 2)
    (Arithmetic.mul_pos_direct
      (by decide) majorants.derivative_pos)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants

end
