module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
public import Purelib.RootIsolation.Newton.Extraction.Separated.Basic
import Purelib.RootIsolation.State.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Majorized.Basic

set_option genInjectivity false in
/-- The extraction result equipped with the a-priori clearance certificate
used by progressive continuation. -/
structure MajorizedSeparatedOutput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (majorants : Dense.Gaussian.Newton.Box.Majorants.ExtractionMajorants p current.box)
    (epsilon : Fraction.Rational) where
  /-- The original separated Newton extraction result for this input state and accuracy request. -/ core :
    Newton.Extraction.Separated.Basic.SeparatedOutput current separation epsilon
  /-- The retained boundary-clearance certificate on the exact extracted core box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p core.box
  /-- The clearance equals the squared separated dominance margin divided by eight times the retained derivative
    majorant. -/ clearance_bound : clearance.bound =
    Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation
        core.radius ^ 2 /
      (8 * majorants.derivative)
  /-- The original a priori extraction-clearance prediction is bounded by the retained actual clearance. -/
    predicted_clearance_le :
    Dense.Gaussian.Newton.Box.Budget.Majorants.predictedExtractionClearance separation current.clearance majorants
      epsilon ≤
      clearance.bound

constructive_injectivity MajorizedSeparatedOutput

end Purelib.RootIsolation.Newton.Extraction.Majorized.Basic

end
