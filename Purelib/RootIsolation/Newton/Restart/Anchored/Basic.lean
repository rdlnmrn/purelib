module

public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart.Anchored.Basic

set_option genInjectivity false in
/-- Direct finite input for building a seed at a displayed rational point.
The four margin inequalities leave three radii for the selected Newton band;
the remaining hypotheses are coefficient-computed scalar budgets. -/
structure AnchoredInput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient) where
  /-- The displayed Gaussian rational sample used as the source anchor. -/ point : Gaussian.Basic.Canonical
  /-- The retained rational radius for the restart construction. -/ radius : Fraction.Rational
  /-- The retained radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- Three retained radii fit strictly between the sample and the left boundary. -/ leftMargin : current.box.xLower + 3
    * radius < point.re
  /-- Three retained radii fit strictly between the sample and the right boundary. -/ rightMargin : point.re + 3 *
    radius < current.box.xUpper
  /-- Three retained radii fit strictly between the sample and the bottom boundary. -/ bottomMargin : current.box.yLower
    + 3 * radius < point.im
  /-- Three retained radii fit strictly between the sample and the top boundary. -/ topMargin : point.im + 3 * radius <
    current.box.yUpper
  /-- The sample's squared residual norm is bounded by the anchored-square variation budget. -/ residual :
    Data.Gaussian.Norm.Basic.normSq (p.eval point) ≤
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * radius ^ 2)
  /-- The anchored-square variation budget is below the squarefree derivative threshold. -/ threshold :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * radius ^ 2) ≤
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box
  /-- Dividing the actual squared residual by the derivative margin gives at most the squared radius. -/
    displacementBudget :
    Data.Gaussian.Norm.Basic.normSq (p.eval point) /
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box ≤ radius ^ 2
  /-- The retained radius makes the coefficient-computed Taylor remainder fit the derivative margin. -/ taylorSmall :
    2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box

constructive_injectivity AnchoredInput

namespace AnchoredInput

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
variable {current : Clearance.Box.Region.ProtectedAmbient p ambient}

open Purelib.RootIsolation in
/-- The displayed point's anchored source square lies inside the current
winding box. -/
theorem sourceRefines
    (input : Newton.Restart.Anchored.Basic.AnchoredInput squarefree current) :
    (Box.Square.Anchored.anchoredSquare input.point input.radius input.radiusPositive.le).Refines
      current.box := by
  have radiusLeThree : input.radius ≤ 3 * input.radius := by
    have twiceNonnegative : 0 ≤ 2 * input.radius :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        input.radiusPositive.le
    calc
      input.radius = 0 + input.radius := by ring1
      _ ≤ 2 * input.radius + input.radius :=
        Fraction.Order.Arithmetic.add_le_add_right_direct twiceNonnegative
          input.radius
      _ = 3 * input.radius := by ring1
  have threeRadiusPositive : 0 < 3 * input.radius :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      input.radiusPositive
  have xLower : current.box.xLower ≤ input.point.re := by
    have beforeMargin : current.box.xLower <
        current.box.xLower + 3 * input.radius := by
      calc
        current.box.xLower = 0 + current.box.xLower := by ring1
        _ < 3 * input.radius + current.box.xLower :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct
            threeRadiusPositive current.box.xLower
        _ = current.box.xLower + 3 * input.radius := by ring1
    exact (beforeMargin.trans input.leftMargin).le
  have xUpper : input.point.re + input.radius ≤ current.box.xUpper := by
    exact (calc
        input.point.re + input.radius ≤
            input.point.re + 3 * input.radius := by
          rw [Fraction.Field.add_comm input.point.re input.radius,
            Fraction.Field.add_comm input.point.re
              (3 * input.radius)]
          exact Fraction.Order.Arithmetic.add_le_add_right_direct radiusLeThree
            input.point.re
        _ < current.box.xUpper := input.rightMargin).le
  have yLower : current.box.yLower ≤ input.point.im := by
    have beforeMargin : current.box.yLower <
        current.box.yLower + 3 * input.radius := by
      calc
        current.box.yLower = 0 + current.box.yLower := by ring1
        _ < 3 * input.radius + current.box.yLower :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct
            threeRadiusPositive current.box.yLower
        _ = current.box.yLower + 3 * input.radius := by ring1
    exact (beforeMargin.trans input.bottomMargin).le
  have yUpper : input.point.im + input.radius ≤ current.box.yUpper := by
    exact (calc
        input.point.im + input.radius ≤
            input.point.im + 3 * input.radius := by
          rw [Fraction.Field.add_comm input.point.im input.radius,
            Fraction.Field.add_comm input.point.im
              (3 * input.radius)]
          exact Fraction.Order.Arithmetic.add_le_add_right_direct radiusLeThree
            input.point.im
        _ < current.box.yUpper := input.topMargin).le
  exact
    ⟨xLower, xUpper, yLower, yUpper⟩
end AnchoredInput

end Purelib.RootIsolation.Newton.Restart.Anchored.Basic

end
