module
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.State.Raw

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free exact finite isolation

A finite list of clear constructive-rational regions carries an exact raw
winding total.  Each step selects the first positive region, extracts one
strictly interior Newton band of raw winding four, and replaces the region by
the eight clear cells of its complement.  Global nonnegativity makes exactly
`count` such steps possible when the initial raw winding is `4 * count`.
-/

namespace Purelib.Polynomial.Clearance.Box.Region.ClearRegion

/-- Attach a supplied nonzero raw-winding proof to an existing clear region without changing its box or clearance. -/
def raw
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (region : Clearance.Box.Region.ClearRegion p ambient)
    (windingNonzero : Winding.Box.Basic.quadrupledBoxWinding p region.box ≠ 0) :
    State.Raw.RawWindingState p ambient where
  box := region.box
  refinesAmbient := region.refinesAmbient
  proper := region.proper
  clearance := region.clearance
  rawWinding_ne := windingNonzero
end Purelib.Polynomial.Clearance.Box.Region.ClearRegion

end
