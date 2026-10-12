module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Separation
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Clearance.Box.Region

set_option genInjectivity false in
/-- One clear region in a fixed finite ambient box. -/
structure ClearRegion (p :
  CoefficientPolynomial) (ambient
  : Box) where
  /-- The retained region rectangle. -/ box : Box
  /-- The retained box refines its original fixed ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The retained box has positive widths. -/ proper : box.Proper
  /-- The quantitative polynomial clearance on this retained box boundary. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box

constructive_injectivity ClearRegion

/-- The two retained clear-region boxes have disjoint interiors witnessed by coordinate separation. -/
def Basic.regionInteriorSeparated
    {p : CoefficientPolynomial} {ambient : Box}
    (left right : ClearRegion p ambient) : Prop :=
  left.box.InteriorSeparated right.box

/-- Interior separation of retained clear regions is symmetric. -/
theorem Basic.regionInteriorSeparated_symm
    {p : CoefficientPolynomial} {ambient : Box}
    {left right : ClearRegion p ambient}
    (separated : Clearance.Box.Region.Basic.regionInteriorSeparated left right) :
    Clearance.Box.Region.Basic.regionInteriorSeparated right left :=
  Box.interiorSeparated_symm separated
end Purelib.Polynomial.Clearance.Box.Region

end

section
@[expose] public section

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

namespace Purelib.Polynomial.Clearance.Box.Region

set_option genInjectivity false in
/-- Minimal protected parent needed by residual Newton localization.  The
parent winding count is intentionally absent: geometry, boundary clearance,
and refinement into the fixed ambient box are sufficient.  The squarefree
and elimination arguments supplied to the constructors carry the derivative,
Taylor, and safe-line data. -/
structure ProtectedAmbient (p :
  CoefficientPolynomial)
  (ambient : Box) where
  /-- The retained region rectangle. -/ box : Box
  /-- The retained box refines its original fixed ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The retained box has positive widths. -/ proper : box.Proper
  /-- The quantitative polynomial clearance on this retained box boundary. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box

constructive_injectivity ProtectedAmbient

end Purelib.Polynomial.Clearance.Box.Region

end
