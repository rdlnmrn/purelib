module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic (Certificate)

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

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated

open Fraction.Order

/-- Radius chosen from the protected boundary, the unit scale, and the
Taylor scale attached to an explicit derivative margin.

The original protected-boundary radius is halved and compared with one and the derivative-margin-to-Taylor quotient for
the same polynomial and box. -/
@[expose] def separatedBaseExtractionRadius
    {p : CoefficientPolynomial} (separation :
      Certificate p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient) :
      Fraction.Rational :=
  min ((1 / 2 : Fraction.Rational) *
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance)
    (min 1 (separation.margin /
      (72 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient)))

/-- A proper box and derivative-separation certificate give a positive protected and Taylor-controlled base radius.

The retained box is proper, the derivative margin is positive and the exact Taylor bound is positive; each input of the
same nested minimum is therefore positive. -/
theorem separatedBaseExtractionRadius_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper) :
    0 < separatedBaseExtractionRadius separation ambient clearance := by
  have denominatorPositive :
      0 < (72 : Fraction.Rational) * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  exact Basic.lt_min
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p clearance proper))
    (Basic.lt_min (by decide)
      (Fraction.Order.Field.div_pos_direct
        separation.margin_pos denominatorPositive))

/-- The final radius also meets the caller's displayed accuracy request.

The same separated base radius and one eighth of the supplied accuracy are retained as the two inputs of the original
rational minimum. -/
@[expose] def separatedExtractionRadius
    {p : CoefficientPolynomial} (separation :
      Certificate p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  min (separatedBaseExtractionRadius separation ambient clearance)
    ((1 / 8 : Fraction.Rational) * epsilon)

/-- A positive accuracy request gives a positive final separated Newton extraction radius.

The proper box and positive derivative separation make the original base radius positive; the strictly positive supplied
epsilon makes its one-eighth constraint positive. -/
theorem separatedExtractionRadius_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < separatedExtractionRadius separation ambient clearance epsilon :=
  Basic.lt_min (separatedBaseExtractionRadius_pos separation clearance proper)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) epsilonPositive)

/-- The final separated Newton radius is no larger than the original boundary-protected radius.

The selected radius is below half of the same protected-boundary radius, whose nonnegativity transports the fixed
half-scale comparison. -/
theorem separatedExtractionRadius_le_protected
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedExtractionRadius separation ambient clearance epsilon ≤
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance := by
  have halfBound :
      separatedExtractionRadius separation ambient clearance epsilon ≤
        (1 / 2 : Fraction.Rational) *
          Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
    (Basic.min_le_left _ _).trans (Basic.min_le_left _ _)
  calc
    separatedExtractionRadius separation ambient clearance epsilon ≤
        (1 / 2 : Fraction.Rational) *
          Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance := halfBound
    _ ≤ 1 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Fraction.Rational) ≤ 1 by decide)
        (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_nonneg p ambient clearance)
    _ = Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance := _root_.one_mul _

/-- The final separated Newton radius is at most one.

The unit constraint is retained within the same base-radius minimum; the outer and inner projections preserve that exact
input. -/
theorem separatedExtractionRadius_le_one
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedExtractionRadius separation ambient clearance epsilon ≤ 1 :=
  (Basic.min_le_left _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))

/-- The final separated Newton radius is at most one eighth of the supplied accuracy request.

This is the right input of the original final-radius minimum, with the same supplied rational epsilon. -/
theorem separatedExtractionRadius_le_eighth
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedExtractionRadius separation ambient clearance epsilon ≤
      (1 / 8 : Fraction.Rational) * epsilon :=
  Basic.min_le_right _ _

/-- The computed extraction radius makes the doubled Taylor remainder budget no larger than the retained derivative
margin.

The original radius lies below one and the retained derivative-margin-to-Taylor quotient. Its square is no larger than
itself, so the positive denominator transports that same constraint. -/
theorem separatedExtractionRadius_taylor
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    let r := separatedExtractionRadius separation ambient clearance epsilon
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) ≤
      separation.margin := by
  let r := separatedExtractionRadius separation ambient clearance epsilon
  let taylor := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  have radiusPositive : 0 < r :=
    separatedExtractionRadius_pos separation clearance proper epsilonPositive
  have radiusLeOne : r ≤ 1 :=
    separatedExtractionRadius_le_one separation clearance epsilon
  have radiusRatio : r ≤ separation.margin / (72 * taylor) :=
    (Basic.min_le_left _ _).trans ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))
  have denominatorPositive : 0 < (72 : Fraction.Rational) * taylor :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (72 * taylor) ≤ separation.margin :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = r := _root_.one_mul _
  calc
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * r ^ 2) =
        (72 * taylor) * r ^ 2 := by
      dsimp only [taylor]
      ring1
    _ ≤ (72 * taylor) * r :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareLeRadius denominatorPositive.le
    _ = r * (72 * taylor) := by ring1
    _ ≤ separation.margin := ratioScaled

/-- Source subdivision threshold for an explicit derivative separation.

The original protected radius, derivative residual threshold, margin, extraction radius and box Lipschitz bound give the
three retained squared-diagonal constraints. -/
@[expose] def separatedSourceDiagonalThreshold
    {p : CoefficientPolynomial} (separation :
      Certificate p ambient)
    (ambient : Box) (clearance : BoundaryClearance p ambient)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance
  let r := separatedExtractionRadius separation ambient clearance epsilon
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  min (rho ^ 2)
    (min (separation.threshold / lipschitz)
      (separation.margin * r ^ 2 / lipschitz))

/-- A proper box and positive accuracy request give a positive source-diagonal threshold.

Properness and the positive accuracy supply a positive original radius; the positive separation witnesses and Lipschitz
bound make each retained threshold positive. -/
theorem separatedSourceDiagonalThreshold_pos
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (proper : ambient.Proper)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < separatedSourceDiagonalThreshold separation ambient clearance epsilon :=
  Basic.lt_min
    (Fraction.Order.Arithmetic.pow_pos_direct
      (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p clearance proper) 2)
    (Basic.lt_min
      (Fraction.Order.Field.div_pos_direct separation.threshold_pos
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient))
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct separation.margin_pos
          (Fraction.Order.Arithmetic.pow_pos_direct
            (separatedExtractionRadius_pos separation clearance proper
              epsilonPositive) 2))
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient)))

/-- The source-diagonal threshold is bounded by the squared protected-boundary radius.

The same squared protected radius is the left input of the retained source threshold minimum. -/
theorem separatedSourceDiagonalThreshold_le_protected
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance ^ 2 :=
  Basic.min_le_left _ _

/-- The source-diagonal threshold fits the derivative-separation residual budget divided by the box Lipschitz
multiplier.

The derivative-separation threshold divided by the original box Lipschitz bound is retained as the middle minimum input.
-/
theorem separatedSourceDiagonalThreshold_le_derivative
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      separation.threshold / Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
  (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)

/-- The source-diagonal threshold fits the derivative-margin displacement budget for the exact extraction radius.

The original derivative margin, selected extraction radius and box Lipschitz bound form the last input of that same
source threshold minimum. -/
theorem separatedSourceDiagonalThreshold_le_displacement
    {p : CoefficientPolynomial} {ambient : Box}
    (separation : Certificate p ambient)
    (clearance : BoundaryClearance p ambient) (epsilon : Fraction.Rational) :
    separatedSourceDiagonalThreshold separation ambient clearance epsilon ≤
      separation.margin *
          separatedExtractionRadius separation ambient clearance epsilon ^ 2 /
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
  (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated

end
