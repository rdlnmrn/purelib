module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Boundary.Budget
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib

section
public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Data

/-- Polynomial-independent extraction radius.  This is the numerical content
of `majorizedExtractionRadius`, separated from its proof-carrying resources. -/
@[expose] def predictedExtractionRadiusData
    (ambient : Geometry.Rational.Box) (margin clearanceBound lipschitz taylor epsilon :
      Fraction.Rational) : Fraction.Rational :=
  min
    (min ((1 / 2 : Fraction.Rational) *
        Geometry.Rational.Box.Boundary.Budget.predictedProtectedRadiusData ambient clearanceBound lipschitz)
      (min 1 (margin / (72 * taylor))))
    ((1 / 8 : Fraction.Rational) * epsilon)

open Purelib.Polynomial
/-- Positive boundary-clearance lower bound computable solely from displayed
rational input data, before the polynomial carrying those bounds is read. -/
@[expose] def predictedExtractionClearanceData
    (ambient : Geometry.Rational.Box)
    (margin clearanceBound lipschitz taylor derivative epsilon : Fraction.Rational) :
    Fraction.Rational :=
  let radius := predictedExtractionRadiusData ambient margin clearanceBound
    lipschitz taylor epsilon
  let dominance := margin * radius ^ 2 / 2
  dominance ^ 2 / (8 * derivative)

/-- Positive displayed bounds give a positive predicted extraction radius.

The ambient box must be proper, and the margin, clearance, Lipschitz, Taylor and requested precision parameters must all
be positive. -/
theorem predictedExtractionRadiusData_pos
    {ambient : Geometry.Rational.Box} {margin clearanceBound lipschitz taylor epsilon :
      Fraction.Rational}
    (proper : ambient.Proper) (marginPositive : 0 < margin)
    (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) (taylorPositive : 0 < taylor)
    (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionRadiusData ambient margin clearanceBound
      lipschitz taylor epsilon := by
  exact Purelib.Data.Rat.Fraction.Order.Basic.lt_min
    (Purelib.Data.Rat.Fraction.Order.Basic.lt_min
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (Geometry.Rational.Box.Boundary.Budget.predictedProtectedRadiusData_pos proper clearancePositive
          lipschitzPositive))
      (Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
        (Fraction.Order.Field.div_pos_direct marginPositive
          (Fraction.Order.Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 72) (by decide)) taylorPositive))))
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) epsilonPositive)

/-- Positive displayed bounds give a positive predicted extraction clearance.

The proper ambient box and positive extraction parameters are supplemented by a positive derivative bound. -/
theorem predictedExtractionClearanceData_pos
    {ambient : Geometry.Rational.Box}
    {margin clearanceBound lipschitz taylor derivative epsilon : Fraction.Rational}
    (proper : ambient.Proper) (marginPositive : 0 < margin)
    (clearancePositive : 0 < clearanceBound)
    (lipschitzPositive : 0 < lipschitz) (taylorPositive : 0 < taylor)
    (derivativePositive : 0 < derivative) (epsilonPositive : 0 < epsilon) :
    0 < predictedExtractionClearanceData ambient margin clearanceBound
      lipschitz taylor derivative epsilon := by
  have radiusPositive := predictedExtractionRadiusData_pos proper
    marginPositive clearancePositive lipschitzPositive taylorPositive
    epsilonPositive
  have dominancePositive : 0 < margin *
      predictedExtractionRadiusData ambient margin clearanceBound lipschitz
        taylor epsilon ^ 2 / 2 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct marginPositive
        (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2))
      (by decide)
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct dominancePositive 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      derivativePositive)
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Data

end
