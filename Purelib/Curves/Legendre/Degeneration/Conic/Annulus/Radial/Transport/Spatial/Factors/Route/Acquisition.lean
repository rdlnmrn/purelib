module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Riemann.Paths.OwnerTracePath

/-! # Width-paid covered acquisition on an original sharp spatial route

The complete original Geometry and Factors.Route remain input owners. Each
actual stored physical edge receives the original factor width request and
one new internally paid covered acquisition. The original source Owner is
supplied once, and all subsequent edges use exact stored finish handoffs.
The retained result owns its particular original CoveredTracedPath value.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {budgets : Budgets anchor}
variable {geometry : Parallel.Geometry source targetReading anchor.regular payment}
variable (factorRoute : Route budgets geometry)
variable (sourceOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 quarter positive first)))

/-- The original factor-route cache and complete new paid covered acquisition remain retained together.

The width assignment is exactly widthRequest on each original physical
edge. The existing covered acquisition stores its complete successful
spine, actual trace/mesh/acquisition caches and particular covered result.
No equality to the older CoveredTracedPath.build is asserted.
-/
@[expose] def Acquisition :=
  { retained : Route budgets geometry // retained = factorRoute } ×
    CoveredTracedPath.Acquisition (fun {_start _finish} segment => widthRequest anchor segment)
      geometry.route.path geometry.route.within sourceOwner

namespace Acquisition

/-- Retain the complete original factor cache beside an already completed paid covered acquisition. -/
@[expose] def ofCompleted
    (paid : CoveredTracedPath.Acquisition (fun {_start _finish} segment => widthRequest anchor segment)
      geometry.route.path geometry.route.within sourceOwner) : Acquisition factorRoute sourceOwner :=
  ⟨⟨factorRoute, rfl⟩, paid⟩

/-- Acquire the sharp-route edges once with sufficient finite widths and exact source-owner handoffs. -/
def build : Acquisition factorRoute sourceOwner :=
  let paid := CoveredTracedPath.Acquisition.build (fun {_start _finish} segment => widthRequest anchor segment)
    geometry.route.path geometry.route.within sourceOwner
  ofCompleted factorRoute sourceOwner paid

variable {factorRoute : Route budgets geometry}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 quarter positive first))}
variable (retained : Acquisition factorRoute sourceOwner)

/-- Read the entire same original physical factor preparation route supplied before the covered acquisition. -/
@[expose] def factors : Route budgets geometry := retained.1.val

/-- The complete original factor route remains exactly the supplied input cache. -/
theorem factors_eq : retained.factors = factorRoute := retained.1.property

/-- Read the complete original covered acquisition with its unchanged width/request and actual terminal caches. -/
@[expose] def paid := retained.2

/-- Read the entire retained acquisition spine on the exact original stored physical route. -/
@[expose] def spine := retained.paid.spine

/-- Read the particular original CoveredTracedPath assembled from those same actual width-paid acquisitions. -/
@[expose] def covered := retained.paid.covered

/-- The particular stored covered path is the exact original assembly of the identical retained acquisition spine. -/
theorem covered_eq : retained.covered = CoveredTracedPath.Acquisition.Spine.assemble
    (fun {_start _finish} segment => widthRequest anchor segment)
    geometry.route.path geometry.route.within sourceOwner retained.spine := retained.paid.covered_eq

/-- The source of the actual new covered execution is the same supplied nominal original Owner. -/
@[expose] def startOwner (_retained : Acquisition factorRoute sourceOwner) : Owner ((Paths.polynomial parameter).eval
    (Spatial.coordinate site parameter 2 quarter positive first)) := sourceOwner

/-- The finishing full-cubic Owner is the same original cache stored in this particular assembled covered path. -/
@[expose] def finishOwner : Owner ((Paths.polynomial parameter).eval
    (Spatial.coordinate site parameter 2 quarter positive last)) := retained.covered.traced.finishOwner

/-- Read the original complete retained owner trace between those exact supplied and stored nominal Owners. -/
@[expose] def trace : OwnerPath (Paths.polynomial parameter)
    (Spatial.coordinate site parameter 2 quarter positive first) sourceOwner
    (Spatial.coordinate site parameter 2 quarter positive last) retained.finishOwner :=
  retained.covered.traced.trace.get

end Acquisition

/-- Use an already completed original Source attachment as the sole source attachment of the new paid route.

The attachment is an input cache. Building the route never attaches or
prepares another independent source Owner; subsequent physical edges use
the exact retained finish Owner of their preceding actual trace.
-/
def start (factorRoute : Route budgets geometry) {prepared : Division.Prepared source.lift.value}
    (attachment : Spatial.Source source prepared) : Acquisition factorRoute attachment.attached.owner :=
  Acquisition.build factorRoute attachment.attached.owner

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route
