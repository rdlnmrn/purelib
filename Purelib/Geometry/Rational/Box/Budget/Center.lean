module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
Expose the original candidate's winding request before clearance construction.
The pending value caches its selected band. Supplying a source-certified
winding restores exactly the original complete optional refinement, including
the original clearance constructors. No alternative owner is substituted.
-/

namespace Purelib.Geometry.Rational.Box.Budget.Center

/-- The minimum of one eighth of the requested tolerance and one quarter of the four center-to-side gaps. -/
def radius (box : Rational.Box) (epsilon :
  Fraction.Rational) (center : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  min (epsilon / 8) (min (center.re - box.xLower)
    (min (box.xUpper - center.re)
      (min (center.im - box.yLower) (box.yUpper - center.im))) / 4)

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {degreeBound : Nat}
  (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
    degreeBound)
  (current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient) (epsilon : Purelib.Data.Rat.Fraction.Rational)
  (center : Purelib.Data.Gaussian.Basic.Canonical) (clearances :
    Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
end Purelib.Geometry.Rational.Box.Budget.Center

end
