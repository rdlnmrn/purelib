module

public import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Geometry.Grid.Winding

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
public import Purelib.Data.List.DependentProduct
public import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Polynomial.Bounds.Horner
import Purelib.Tactic.Ring

/-! # Actual parallel spatial covers with retained owner handoffs

Original start and target quarter Reading caches accompany the exact
branch-factor region clearance and its actual spatial L route. The constant
depth-seven chart payment pays these spatial edges. Their primitive-covered
path is built once on a supplied original continuation Owner, which may be
the preceding block's exact finishOwner. Only the first block needs the
already completed full-cubic Source attachment.

Whole existing RegionClearance, Route and CoveredTracedPath values are
retained with factory identities. Agreement with the separate original root
readings, chart-to-spatial integral comparison and canonical cut attachment
remain additional certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.RootIsolation
open Purelib.Data.List (DependentProduct)
open Purelib.Integration.Path.Dyadic

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2} {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}

/-- The exact sharp spatial square about the original retained quarter source coordinate. -/
@[expose] def box (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (first : Fraction.Rational) (regular : parameter ≠ criticalValue site) : Geometry.Rational.Box :=
  Radial.Clearance.box site parameter (Waist.direction quarter first) regular

/-- The source of the original retained quarter lies in its exact branch-factor spatial square. -/
theorem source_inside (regular : parameter ≠ criticalValue site) :
    (box site parameter quarter first regular).Contains (coordinate site parameter 2 quarter positive first) :=
  Radial.Clearance.point_inside_box site parameter (Waist.direction quarter first) regular

/-- The constant original depth-seven payment puts the actual target coordinate in the same sharp source square. -/
theorem target_inside (regular : parameter ≠ criticalValue site)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) :
    (box site parameter quarter first regular).Contains (coordinate site parameter 2 quarter positive last) :=
  Radial.Clearance.quarter_target_inside site parameter quarter regular first last payment

/-- Every actual curved-quarter point between two paid chart endpoints lies in that same sharp source square. -/
theorem interval_inside (regular : parameter ≠ criticalValue site)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last) :
    (box site parameter quarter first regular).Contains (coordinate site parameter 2 quarter positive time) :=
  target_inside (last := time) regular
    ((Arithmetic.pow_le_pow_direct
      (Arithmetic.sub_nonneg_direct between.1)
      (Arithmetic.sub_le_sub_right_direct between.2 first) 2).trans payment)

/-- The existing full-cubic clearance type on the exact sharp source square of this retained quarter. -/
@[expose] def ClearanceType (regular : parameter ≠ criticalValue site) : Type :=
  RegionClearance (Paths.polynomial parameter) (box site parameter quarter first regular)

/-- The existing spatial Route type on the same original source and target quarter coordinates. -/
@[expose] def RouteType (regular : parameter ≠ criticalValue site) : Type :=
  ClearBoxPaths.Route (Paths.polynomial parameter) (box site parameter quarter first regular)
    (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)

/-- The two original Reading caches and whole sharp-clearance/route factories retained for one actual spatial block.

Each value is an existing parent container. The exact subtype equations bind
the retained reading pair, region clearance and paid L route to their original
inputs and completed factories. No root request or owner attachment occurs in
this geometry construction, so later covered blocks accept genuine handoffs.
-/
@[expose] def Geometry (reading : Reading actual first firstInside) (targetReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) : Type 1 :=
  { retained : Reading actual first firstInside × Reading actual last lastInside //
      retained.1 = reading ∧ retained.2 = targetReading } ×
    Σ clearance : { retained : ClearanceType (quarter := quarter) (first := first) regular //
        retained = Radial.Clearance.clearance site parameter (Waist.direction quarter first)
          regular actual.data.bound },
      { route : RouteType (positive := positive) (quarter := quarter) (first := first) (last := last) regular //
        route = ClearBoxPaths.Route.build clearance.val
          (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
          (source_inside (positive := positive) regular)
          (target_inside (positive := positive) regular payment) }

namespace Geometry

variable {reading : Reading actual first firstInside} {targetReading : Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}

/-- Retain completed sharp geometry with the identical original reading caches and factory equations. -/
@[expose] def ofCompleted (reading : Reading actual first firstInside) (targetReading : Reading actual last lastInside)
    (clearance : ClearanceType (quarter := quarter) (first := first) regular)
    (clearance_eq : clearance = Radial.Clearance.clearance site parameter (Waist.direction quarter first)
      regular actual.data.bound)
    (route : RouteType (positive := positive) (quarter := quarter) (first := first) (last := last) regular)
    (route_eq : route = ClearBoxPaths.Route.build clearance
      (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
      (source_inside (positive := positive) regular)
      (target_inside (positive := positive) regular payment)) : Geometry reading targetReading regular payment :=
  ⟨⟨⟨reading, targetReading⟩, rfl, rfl⟩, ⟨⟨clearance, clearance_eq⟩, ⟨route, route_eq⟩⟩⟩

/-- Compute the factor-paid clearance and actual spatial Route once, retaining both supplied Reading caches. -/
def build (reading : Reading actual first firstInside) (targetReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7)
    (retainedClearance : {retained : ClearanceType (quarter := quarter) (first := first) regular //
        retained = Radial.Clearance.clearance site parameter (Waist.direction quarter first) regular actual.data.bound}
      := ⟨Radial.Clearance.clearance site parameter (Waist.direction quarter first) regular actual.data.bound, rfl⟩) :
    Geometry reading targetReading regular payment :=
  let clearance := retainedClearance.val
  let route := ClearBoxPaths.Route.build clearance
      (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
      (source_inside (positive := positive) regular)
      (target_inside (positive := positive) regular payment)
  ofCompleted reading targetReading clearance retainedClearance.property route rfl

/-- Read the identical entire original source Reading retained beside the spatial geometry. -/
@[expose] def source (geometry : Geometry reading targetReading regular payment) : Reading actual first firstInside :=
  geometry.1.val.1

/-- Read the identical entire original target Reading with its separate original cofactor/cubic channels. -/
@[expose] def target (geometry : Geometry reading targetReading regular payment) : Reading actual last lastInside :=
  geometry.1.val.2

/-- The complete source Reading is the supplied original cache. -/
theorem source_eq (geometry : Geometry reading targetReading regular payment) : geometry.source = reading :=
  geometry.1.property.1

/-- The complete target Reading is the supplied original cache. -/
theorem target_eq (geometry : Geometry reading targetReading regular payment) : geometry.target = targetReading :=
  geometry.1.property.2

/-- Read the complete original branch-factor RegionClearance cache retained by this geometry. -/
@[expose] def clearance (geometry : Geometry reading targetReading regular payment) :
    ClearanceType (quarter := quarter) (first := first) regular := geometry.2.1.val

/-- Build an actual finite rectangular model cover from this same retained sharp geometry and source Owner.

The original factor-clear radius proves box properness, and the original
quarter source lies inside it. The acquired cover retains the real
source-to-anchor trace and its exact ending Owner, then the same budget,
spatial mesh and signed model bank. No assertion that one inverse box
contains the curved interval or the spatial route is required.
-/
def primitiveCover (geometry : Geometry reading targetReading regular payment)
    (sourceOwner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter positive first))) :=
  RectangularPatch.acquireAt geometry.clearance
    (Box.Square.Centered.centeredSquare_proper _ (Radial.Clearance.radius_positive site parameter regular))
    (coordinate site parameter 2 quarter positive first) (source_inside (positive := positive) regular) sourceOwner

/-- The clearance is the whole original factory on the same parameter, quarter source and intrinsic admission proof. -/
theorem clearance_eq (geometry : Geometry reading targetReading regular payment) : geometry.clearance =
    Radial.Clearance.clearance site parameter (Waist.direction quarter first) regular actual.data.bound :=
  geometry.2.1.property

/-- Read the complete original spatial L Route retained on that exact branch-factor-clear square. -/
@[expose] def route (geometry : Geometry reading targetReading regular payment) :
    RouteType (positive := positive) (quarter := quarter) (first := first) (last := last) regular := geometry.2.2.val

/-- The spatial Route is the whole original paid factory using the identical retained clearance cache. -/
theorem route_eq (geometry : Geometry reading targetReading regular payment) : geometry.route =
    ClearBoxPaths.Route.build geometry.clearance
      (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
      (source_inside (positive := positive) regular)
      (target_inside (positive := positive) regular payment) :=
  geometry.2.2.property

/-- Retaining completed geometry preserves its entire original clearance value. -/
theorem ofCompleted_clearance (reading : Reading actual first firstInside)
    (targetReading : Reading actual last lastInside)
    (clearance : ClearanceType (quarter := quarter) (first := first) regular)
    (clearance_eq : clearance = Radial.Clearance.clearance site parameter (Waist.direction quarter first)
      regular actual.data.bound)
    (route : RouteType (positive := positive) (quarter := quarter) (first := first) (last := last) regular)
    (route_eq : route = ClearBoxPaths.Route.build clearance
      (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
      (source_inside (positive := positive) regular)
      (target_inside (positive := positive) regular payment)) :
    (ofCompleted (payment := payment) reading targetReading clearance clearance_eq route route_eq).clearance =
      clearance := rfl

/-- Retaining completed geometry preserves the whole original Route, including its path and within cache. -/
theorem ofCompleted_route (reading : Reading actual first firstInside) (targetReading : Reading actual last lastInside)
    (clearance : ClearanceType (quarter := quarter) (first := first) regular)
    (clearance_eq : clearance = Radial.Clearance.clearance site parameter (Waist.direction quarter first)
      regular actual.data.bound)
    (route : RouteType (positive := positive) (quarter := quarter) (first := first) (last := last) regular)
    (route_eq : route = ClearBoxPaths.Route.build clearance
      (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
      (source_inside (positive := positive) regular)
      (target_inside (positive := positive) regular payment)) :
    (ofCompleted (payment := payment) reading targetReading clearance clearance_eq route route_eq).route = route := rfl

/-- The actual affine spatial chord consumes this geometry's original clearance and the retained whole Horner cache.

Its source and target are the supplied original Reading coordinates. The
ambient bounds are the original Leg's global bounds; the sharper region and
its numerical clearance remain distinct cached data.
-/
@[expose] def chord (geometry : Geometry reading targetReading regular payment)
    (bounds : Horner)
    (bounds_eq : bounds = Polynomial.Dense.Gaussian.Bounds.Box.denseHornerNormBounds
      (Paths.polynomial parameter) (spatialBox site)) :
    Polynomial.Geometry.ClearPath.ClearSegment (Paths.polynomial parameter) (spatialBox site)
      (coordinate site parameter 2 quarter positive first)
      (coordinate site parameter 2 quarter positive last) .region :=
  .affine _ _ (box site parameter quarter first regular)
    ⟨point_inside site parameter 2 (Waist.direction quarter first) positive
        actual.data.lower actual.data.upper actual.data.bound,
      point_inside site parameter 2 (Waist.direction quarter last) positive
        actual.data.lower actual.data.upper actual.data.bound⟩
    geometry.clearance (source_inside regular) (target_inside regular payment) bounds bounds_eq

/-- The affine chord retains the same full original region clearance numerically. -/
theorem chord_clearance (geometry : Geometry reading targetReading regular payment)
    (bounds : Horner)
    (bounds_eq : bounds = Polynomial.Dense.Gaussian.Bounds.Box.denseHornerNormBounds
      (Paths.polynomial parameter) (spatialBox site)) :
    (geometry.chord bounds bounds_eq).clearanceBound = Radial.Clearance.floor site parameter := by
  change geometry.clearance.bound = _
  rewrite [geometry.clearance_eq]
  rfl

/-- The retained original spatial route stays in the coordinate hull of its actual chart endpoints.

The complete route factory equality retains its computed horizontal or
vertical branches. Degenerate endpoints satisfy the same closed-box bound.
-/
theorem route_inBox (geometry : Geometry reading targetReading regular payment) :
    Polynomial.Geometry.ClearPath.InBox
      (Box.Hull.hull
        (Box.Point.pointBox (coordinate site parameter 2 quarter positive first))
        (Box.Point.pointBox (coordinate site parameter 2 quarter positive last))) geometry.route.path := by
  rewrite [geometry.route_eq]
  exact ClearBoxPaths.Route.build_inBox _ _ _ _ _

end Geometry

variable {reading : Reading actual first firstInside} {targetReading : Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}

/-- The exact existing CoveredTracedPath type on this retained spatial Route and supplied genuine source Owner. -/
@[expose] def CoveredType (geometry : Geometry reading targetReading regular payment)
    (sourceOwner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter positive first))) : Type :=
  CoveredTracedPath geometry.route.path sourceOwner

/-- One completed original covered path and its factory identity on the identical supplied source Owner.

The owner can be a preceding block's actual finishOwner. The subtype retains
the entire original primitive cover, preparation, subdivisions and trace. It
does not construct a new source attachment or identify the separately retained
original root-reading caches with this continued owner.
-/
@[expose] def Covered (geometry : Geometry reading targetReading regular payment)
    (sourceOwner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter positive first))) : Type :=
  { covered : CoveredType geometry sourceOwner // covered =
      CoveredTracedPath.build geometry.route.path geometry.route.within sourceOwner }

namespace Covered

variable {geometry : Geometry reading targetReading regular payment}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive first))}

/-- Retain a completed original spatial cover without rebuilding its mesh, preparation or continuation owner. -/
@[expose] def ofCompleted (covered : CoveredType geometry sourceOwner)
    (retained : covered = CoveredTracedPath.build geometry.route.path geometry.route.within sourceOwner) :
    Covered geometry sourceOwner := ⟨covered, retained⟩

/-- Build the actual cleared spatial cover once on the supplied original source Owner or exact prior handoff. -/
def build (geometry : Geometry reading targetReading regular payment)
    (sourceOwner : Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive first))) :
    Covered geometry sourceOwner :=
  let covered := CoveredTracedPath.build geometry.route.path geometry.route.within sourceOwner
  ofCompleted covered rfl

/-- Read the entire retained original cover and preparation with its actual terminal-owner cache. -/
@[expose] def block (covered : Covered geometry sourceOwner) : CoveredType geometry sourceOwner := covered.val

/-- The complete cache is the original factory on the same spatial Route, within certificate and actual source Owner. -/
theorem block_eq (covered : Covered geometry sourceOwner) : covered.block =
    CoveredTracedPath.build geometry.route.path geometry.route.within sourceOwner := covered.property

/-- Retaining a completed block preserves the identical entire original covered/prepared value. -/
theorem ofCompleted_block (covered : CoveredType geometry sourceOwner)
    (retained : covered = CoveredTracedPath.build geometry.route.path geometry.route.within sourceOwner) :
    (ofCompleted covered retained).block = covered := rfl

/-- The source continuation Owner remains the exact supplied original index of the completed covered block. -/
@[expose] def startOwner (_covered : Covered geometry sourceOwner) :
    Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive first)) := sourceOwner

/-- The terminal full-cubic Owner is the original covered path's actual cached finish owner at the spatial endpoint. -/
@[expose] def finishOwner (covered : Covered geometry sourceOwner) :
    Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive last)) :=
  covered.block.traced.finishOwner

/-- Read the original completed block's deferred OwnerPath trace with the unchanged supplied source Owner. -/
@[expose] def trace (covered : Covered geometry sourceOwner) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter positive first) sourceOwner
      (coordinate site parameter 2 quarter positive last) covered.finishOwner := covered.block.traced.trace.get

/-- Every actual retained spatial trace vertex lies in the exact rectangle of the original chart endpoints.

The factory identity selects the same original covered preparation and
request cache. The actual route's computed branches keep all repeated
handoffs and subdivision vertices inside its endpoint hull.
-/
theorem trace_inBox (covered : Covered geometry sourceOwner) (value : Canonical)
    (member : value ∈ covered.trace.vertices) :
    (Box.Hull.hull
      (Box.Point.pointBox (coordinate site parameter 2 quarter positive first))
      (Box.Point.pointBox (coordinate site parameter 2 quarter positive last))).Contains value := by
  change value ∈ covered.block.traced.trace.get.vertices at member
  rewrite [covered.block_eq] at member
  exact CoveredTracedPath.build_inBox _ geometry.route.path geometry.route.within sourceOwner
    geometry.route_inBox value member

/-- Retain the same completed original block in the varying-box chain, preserving its actual owner handoff indices. -/
@[expose] def blocks (covered : Covered geometry sourceOwner) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter positive first) sourceOwner
      (coordinate site parameter 2 quarter positive last) covered.finishOwner :=
  CoveredTracedPath.Blocks.singleton covered.block

/-- The varying-box view preserves the entire original completed OwnerPath trace value. -/
theorem blocks_trace (covered : Covered geometry sourceOwner) : covered.blocks.trace = covered.trace :=
  CoveredTracedPath.Blocks.singleton_trace covered.block

/-- The varying-box view retains the exact original preparation's ordered moving-vertex cache. -/
theorem blocks_movingVertices (covered : Covered geometry sourceOwner) :
    covered.blocks.movingVertices = covered.block.traced.movingVertices :=
  CoveredTracedPath.Blocks.singleton_movingVertices covered.block

variable {prepared : Gaussian.Division.Prepared reading.lift.value}

/-- Start the first spatial block using the identical already completed full-cubic Source attachment.

Later blocks use build with the previous exact finishOwner directly. This
entry point obtains no new root reading, cofactor certificate or attachment.
-/
def start (source : Source reading prepared) (geometry : Geometry reading targetReading regular payment) :
    Covered geometry source.attached.owner := build geometry source.attached.owner

/-- The initial entry retains the identical full-cubic Owner from the completed original Source attachment. -/
theorem start_owner (source : Source reading prepared) (geometry : Geometry reading targetReading regular payment) :
    (start source geometry).startOwner = source.attached.owner := rfl

variable {finish : Fraction.Rational} {finishInside : FixedRootBoxPath.Inside finish}
variable {finishReading : Reading actual finish finishInside}
variable {nextPayment : (finish - last) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {nextGeometry : Geometry targetReading finishReading regular nextPayment}

/-- Concatenate two original covered spatial blocks at the identical middle Reading and actual retained finish Owner.

The local sharp boxes and complete covered/prepared caches may differ. The
second block is indexed by the first block's actual terminal owner, and the
original Blocks append retains both complete values without attaching again.
-/
@[expose] def append (left : Covered geometry sourceOwner) (right : Covered nextGeometry left.finishOwner) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter positive first) sourceOwner
      (coordinate site parameter 2 quarter positive finish) right.finishOwner :=
  left.blocks.append right.blocks

/-- Appending two original covered blocks delegates to the same complete OwnerPath concatenation. -/
theorem append_trace (left : Covered geometry sourceOwner) (right : Covered nextGeometry left.finishOwner) :
    (left.append right).trace = left.trace.append right.trace := by
  change (left.blocks.append right.blocks).trace = left.trace.append right.trace
  rewrite [CoveredTracedPath.Blocks.append_trace, left.blocks_trace, right.blocks_trace]
  rfl

/-- Covered spatial concatenation retains both original ordered moving-vertex caches exactly. -/
theorem append_movingVertices (left : Covered geometry sourceOwner) (right : Covered nextGeometry left.finishOwner) :
    (left.append right).movingVertices = left.block.traced.movingVertices ++ right.block.traced.movingVertices := by
  change (left.blocks.append right.blocks).movingVertices = _
  rewrite [CoveredTracedPath.Blocks.append_movingVertices, left.blocks_movingVertices, right.blocks_movingVertices]
  rfl

/-- The original quarter Horner cache pays movement at every actual retained spatial trace vertex.

Endpoint-rectangle containment is derived from the actual completed cover,
not supplied as a movement hypothesis. The bound consumes the same Leg
and whole stored polynomial fold as its original affine trace budget.
-/
theorem trace_movement (leg : Leg site parameter quarter) {accuracy : Leg.TraceAccuracy leg}
    (budget : Leg.TraceBudget leg accuracy)
    {sourceReading : Reading leg.actual first firstInside} {finishReading : Reading leg.actual last lastInside}
    {stepPaid : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    {retainedGeometry : Geometry sourceReading finishReading leg.regular stepPaid}
    {retainedSource : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    (covered : Covered retainedGeometry retainedSource) (value : Canonical)
    (member : value ∈ covered.trace.vertices) :
    Data.Gaussian.Norm.Basic.normSq ((Paths.polynomial parameter).eval value -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)) ≤
      leg.traceMovement budget.bounds * (first - last) ^ 2 :=
  budget.movement_inBox first last value (covered.trace_inBox value member)

end Covered

section WholeQuarter

/-- Every retained chart time of this exact finite table lies in the original quarter. -/
@[expose] def Inside (times : List Fraction.Rational) : Prop :=
  ∀ time ∈ times, FixedRootBoxPath.Inside time

/-- A materialized table of actual original quarter readings at their bounded original time occurrences. -/
@[expose] def Readings (actual : Quarter site parameter 2 quarter positive)
    (times : List Fraction.Rational) (inside : Inside times) : Type 1 :=
  DependentProduct times (fun index => Reading actual (times[index.val]'index.isLt)
    (inside _ (List.getElem_mem index.isLt)))

namespace Readings

/-- Read a complete retained original quarter query without invoking its preparation or lift producer again. -/
@[expose] def get {times : List Fraction.Rational} {inside : Inside times}
    (readings : Readings actual times inside) (index : Fin times.length) :
    Reading actual (times[index.val]'index.isLt) (inside _ (List.getElem_mem index.isLt)) :=
  DependentProduct.get times readings index

/-- Retain the unchanged original source of a nonempty reading table. -/
@[expose] def head {first : Fraction.Rational} {times : List Fraction.Rational} {inside : Inside (first :: times)}
    (readings : Readings actual (first :: times) inside) : Reading actual first (inside _ (List.Mem.head _)) :=
  readings.1

/-- Retain the unchanged original table tail under the same bounded time occurrences. -/
@[expose] def tail {first : Fraction.Rational} {times : List Fraction.Rational} {inside : Inside (first :: times)}
    (readings : Readings actual (first :: times) inside) :
    Readings actual times (fun time member => inside time (List.Mem.tail first member)) := readings.2

/-- Materialize each actual quarter query once, retaining the original Leg endpoint caches at zero and one. -/
def ofLeg (leg : Leg site parameter quarter) (times : List Fraction.Rational) (inside : Inside times) :
    Readings leg.actual times inside :=
  DependentProduct.ofFn times (fun index =>
    leg.readingAt (times[index.val]'index.isLt) (inside _ (List.getElem_mem index.isLt)))

/-- Lookup consumes the actual original Leg query supplied at this same retained time occurrence. -/
theorem get_ofLeg (leg : Leg site parameter quarter) (times : List Fraction.Rational) (inside : Inside times)
    (index : Fin times.length) : (ofLeg leg times inside).get index =
      leg.readingAt (times[index.val]'index.isLt) (inside _ (List.getElem_mem index.isLt)) :=
  DependentProduct.get_ofFn times _ index

/-- Original cofactor observations and their once-computed actual product readings at the retained bounded vertices.

Each entry is an existing ResidualObservation followed by a scalar cache and
its exact original product equation. The original Reading table is an index;
no reading, root owner, cofactor certificate or process is reconstructed by
lookup, neighboring-edge construction or the later Chain fold.
-/
@[expose] def Samples {times : List Fraction.Rational} {inside : Inside times}
    (readings : Readings actual times inside) (accuracy : AccuracyRequest) : Type :=
  DependentProduct times (fun index =>
    Σ sample : CertifiedSquareRoot.Sampling.ResidualObservation (readings.get index).lift.unitRoot
        ((readings.get index).productRequest accuracy),
      {value : Canonical // value = (readings.get index).productReading sample})

namespace Samples

variable {times : List Fraction.Rational} {inside : Inside times}
variable {readings : Readings actual times inside} {accuracy : AccuracyRequest}

/-- Read the entire original observation/product cache entry at its unchanged bounded vertex index. -/
@[expose] def get (samples : Samples readings accuracy) (index : Fin times.length) :
    Σ sample : CertifiedSquareRoot.Sampling.ResidualObservation (readings.get index).lift.unitRoot
        ((readings.get index).productRequest accuracy),
      {value : Canonical // value = (readings.get index).productReading sample} :=
  DependentProduct.get times samples index

/-- Read the identical retained original cofactor observation, without another numerical request. -/
@[expose] def sample (samples : Samples readings accuracy) (index : Fin times.length) :
    CertifiedSquareRoot.Sampling.ResidualObservation (readings.get index).lift.unitRoot
      ((readings.get index).productRequest accuracy) := (samples.get index).1

/-- Read the once-computed actual full-cubic numerical product at this retained vertex. -/
@[expose] def value (samples : Samples readings accuracy) (index : Fin times.length) : Canonical :=
  (samples.get index).2.val

/-- Each retained scalar is the original product of that same observation and original conic ordinate. -/
theorem value_eq (samples : Samples readings accuracy) (index : Fin times.length) :
    samples.value index = (readings.get index).productReading (samples.sample index) := (samples.get index).2.property

/-- Materialize one original cofactor request and one actual scalar product at each stored Reading occurrence. -/
@[expose] def build (readings : Readings actual times inside) (accuracy : AccuracyRequest) :
    Samples readings accuracy :=
  DependentProduct.ofFn times (fun index =>
    let sample := (readings.get index).requestProduct accuracy
    let value := (readings.get index).productReading sample
    ⟨sample, ⟨value, rfl⟩⟩)

/-- Materialization retains the complete original observation and scalar cache at the exact same bounded occurrence. -/
theorem get_build (readings : Readings actual times inside) (accuracy : AccuracyRequest) (index : Fin times.length) :
    (build readings accuracy).get index =
      (let sample := (readings.get index).requestProduct accuracy
       let value := (readings.get index).productReading sample
       ⟨sample, ⟨value, rfl⟩⟩) := DependentProduct.get_ofFn times _ index

/-- Read the original first cached observation and product of a nonempty vertex table. -/
@[expose] def head {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    (samples : Samples readings accuracy) :
    Σ sample : CertifiedSquareRoot.Sampling.ResidualObservation readings.head.lift.unitRoot
        (readings.head.productRequest accuracy),
      {value : Canonical // value = readings.head.productReading sample} := samples.1

/-- Keep the literal original tail of the materialized observation/product bank. -/
@[expose] def tail {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    (samples : Samples readings accuracy) : Samples readings.tail accuracy := samples.2

/-- Read the actual retained scalar products in their original ordered vertex occurrences. -/
@[expose] def values : ∀ {times : List Fraction.Rational} {inside : Inside times}
    {readings : Readings actual times inside}, Samples readings accuracy → List Canonical
  | [], _, _, _ => []
  | _ :: _, _, _, samples => samples.head.2.val :: values samples.tail

end Samples

/-- Actual original trace Edges on adjacent entries of one retained product bank.

The endpoints are the literal neighboring cached scalar products at the same
bounded vertex occurrences. The container stores each full original Edge;
it supplies neither another root owner nor an alternative trace datatype.
-/
@[expose] def Edges {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    {accuracy : AccuracyRequest} (samples : Samples readings accuracy) : Type :=
  DependentProduct times (fun edge => SquareRootTrace.Edge (Paths.polynomial parameter)
    (samples.value edge.castSucc) (samples.value edge.succ)
    (coordinate site parameter 2 quarter positive (DyadicTrace.indexed first times edge.castSucc))
    (coordinate site parameter 2 quarter positive (DyadicTrace.indexed first times edge.succ)))

namespace Edges

/-- Read one complete original cached Edge at its same bounded adjacent-vertex occurrence. -/
@[expose] def get {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    {accuracy : AccuracyRequest} {samples : Samples readings accuracy}
    (edges : Edges samples) (edge : Fin times.length) :
    SquareRootTrace.Edge (Paths.polynomial parameter) (samples.value edge.castSucc) (samples.value edge.succ)
      (coordinate site parameter 2 quarter positive (DyadicTrace.indexed first times edge.castSucc))
      (coordinate site parameter 2 quarter positive (DyadicTrace.indexed first times edge.succ)) :=
  DependentProduct.get times edges edge

/-- Keep the original edge-bank tail on the very same retained neighboring product entries. -/
@[expose] def tail {first next : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: next :: times)} {readings : Readings actual (first :: next :: times) inside}
    {accuracy : AccuracyRequest} {samples : Samples readings accuracy} (edges : Edges samples) :
    Edges samples.tail := edges.2

/-- Fold cached original Edges into the original Chain with literal shared numerical endpoints.

The head's target is the same stored scalar that starts its literal tail.
This fold performs no root request, Reading query, scalar product or EdgeData
construction. All original edge caches are consumed unchanged in order.
-/
@[expose] def chain : ∀ {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    {accuracy : AccuracyRequest} {samples : Samples readings accuracy}, Edges samples →
    SquareRootTrace.Chain (Paths.polynomial parameter) samples.head.2.val samples.tail.values
      (coordinate site parameter 2 quarter positive first)
      (times.map (coordinate site parameter 2 quarter positive))
  | _, [], _, _, _, _, _ => .nil _ _
  | _, _ :: _, _, _, _, _, edges => .cons edges.1 (chain edges.tail)

/-- The actual original sampled chain has one certified edge for every retained chart-time edge. -/
theorem chain_root_count : ∀ {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings actual (first :: times) inside}
    {accuracy : AccuracyRequest} {samples : Samples readings accuracy} (_edges : Edges samples),
    samples.tail.values.length = times.length
  | _, [], _, _, _, _, _ => rfl
  | _, _ :: _, _, _, _, _, edges => congrArg Nat.succ (chain_root_count edges.tail)

/-- Materialize original full-polynomial Edges from the same neighboring retained Reading and product entries.

The existing Leg budget pays every edge. Source/target caches and cofactor
observations are only looked up; the edge constructor consumes the retained
product-cache views directly and never invokes those producers again.
-/
@[expose] def ofLeg (leg : Leg site parameter quarter) {budgetAccuracy : Leg.TraceAccuracy leg}
    (budget : Leg.TraceBudget leg budgetAccuracy)
    {inside : Inside (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)}
    (readings : Readings leg.actual (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) inside)
    (samples : Samples readings (leg.source.traceRequest leg.regular)) : Edges samples :=
  let times := DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1
  DependentProduct.ofFn times (fun edge =>
    let first := readings.get edge.castSucc
    let last := readings.get edge.succ
    first.traceEdgeOfSamples last leg.regular (leg.traceMovement budget.bounds)
      (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)
      (budget.movement _ _) (budget.edge_paid_trace edge) (samples.sample edge.castSucc) (samples.sample edge.succ)
      (samples.get edge.castSucc).2 (samples.get edge.succ).2)

/-- The complete original edge factory stores the supplied retained movement budget exactly. -/
theorem ofLeg_movement (leg : Leg site parameter quarter) {budgetAccuracy : Leg.TraceAccuracy leg}
    (budget : Leg.TraceBudget leg budgetAccuracy)
    {inside : Inside (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)}
    (readings : Readings leg.actual (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) inside)
    (samples : Samples readings (leg.source.traceRequest leg.regular))
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    ((ofLeg leg budget readings samples).get edge).data.movementBound = leg.traceMovement budget.bounds *
      (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 := by
  unfold ofLeg get
  rewrite [DependentProduct.get_ofFn]
  rfl

end Edges

end Readings

/-- Every vertex of the original selected unit-quarter mesh lies in the same retained unit interval. -/
theorem mesh_inside (depth : Nat) : Inside (0 :: DyadicTrace.tail depth (0 : Fraction.Rational) 1) := by
  intro time member
  cases member with
  | head => exact ⟨Fraction.Order.Basic.le_refl _, by decide +kernel⟩
  | tail _ retained => exact DyadicTrace.tail_inside depth (by decide +kernel) retained

/-- An exact cache view of one original sampled Chain and its actual retained vertex and edge banks.

Only original dependent containers, original Reading/ResidualObservation/
Edge values and the original Chain are retained. The additional invariant is
literal shared endpoint consumption: edges use the cached product entries,
and the Chain folds those same Edge values without producer calls.
-/
@[expose] def RootTrace (leg : Leg site parameter quarter) {budgetAccuracy : Leg.TraceAccuracy leg}
    (budget : Leg.TraceBudget leg budgetAccuracy) : Type 1 :=
  let times := DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1
  Σ readings : {retained : Readings leg.actual (0 :: times) (mesh_inside budget.selection.stage) //
      retained = Readings.ofLeg leg (0 :: times) (mesh_inside budget.selection.stage)},
  Σ samples : {retained : Readings.Samples readings.val (leg.source.traceRequest leg.regular) //
      retained = Readings.Samples.build readings.val (leg.source.traceRequest leg.regular)},
  Σ edges : {retained : Readings.Edges samples.val //
      retained = Readings.Edges.ofLeg leg budget readings.val samples.val},
    {retained : SquareRootTrace.Chain (Paths.polynomial parameter) samples.val.head.2.val samples.val.tail.values
        (coordinate site parameter 2 quarter (by decide +kernel) 0)
        (times.map (coordinate site parameter 2 quarter (by decide +kernel))) //
      retained = Readings.Edges.chain edges.val}

namespace RootTrace

variable {leg : Leg site parameter quarter} {budgetAccuracy : Leg.TraceAccuracy leg}
variable {budget : Leg.TraceBudget leg budgetAccuracy}

/-- Materialize every original endpoint Reading/request/product once, then consume the same neighboring edge caches.

The actual original Leg source and target queries are retained by readingAt.
The original finite depth selection and all mathematical Edge payments are
consumed unchanged. This produces a sampled Chain; an all-future OwnerPath
comparison is a separate certificate and is not presumed by this builder.
-/
@[expose] def build (leg : Leg site parameter quarter) {budgetAccuracy : Leg.TraceAccuracy leg}
    (budget : Leg.TraceBudget leg budgetAccuracy) : RootTrace leg budget :=
  let times := DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1
  let readings := Readings.ofLeg leg (0 :: times) (mesh_inside budget.selection.stage)
  let samples := Readings.Samples.build readings (leg.source.traceRequest leg.regular)
  let edges := Readings.Edges.ofLeg leg budget readings samples
  let chain := Readings.Edges.chain edges
  ⟨⟨readings, rfl⟩, ⟨⟨samples, rfl⟩, ⟨⟨edges, rfl⟩, ⟨chain, rfl⟩⟩⟩⟩

/-- Read the identical complete original Reading bank at the actual selected depth. -/
@[expose] def readings (trace : RootTrace leg budget) :
    Readings leg.actual (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)
      (mesh_inside budget.selection.stage) := trace.1.val

/-- The Reading bank is the exact original producer on this same Leg and selected mesh. -/
theorem readings_eq (trace : RootTrace leg budget) : trace.readings =
    Readings.ofLeg leg (0 :: DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)
      (mesh_inside budget.selection.stage) := trace.1.property

/-- Read the stored original observation/product bank without another request or multiplication. -/
@[expose] def samples (trace : RootTrace leg budget) :
    Readings.Samples trace.readings (leg.source.traceRequest leg.regular) := trace.2.1.val

/-- The complete retained sample bank is the original once-materialized producer on those same Reading entries. -/
theorem samples_eq (trace : RootTrace leg budget) : trace.samples =
    Readings.Samples.build trace.readings (leg.source.traceRequest leg.regular) := trace.2.1.property

/-- Read the stored complete Edge bank with its exact neighboring cached endpoints. -/
@[expose] def edges (trace : RootTrace leg budget) : Readings.Edges trace.samples := trace.2.2.1.val

/-- Every retained Edge is from the same budget, actual Reading bank and actual product bank. -/
theorem edges_eq (trace : RootTrace leg budget) : trace.edges =
    Readings.Edges.ofLeg leg budget trace.readings trace.samples := trace.2.2.1.property

/-- Read the original sampled Chain retaining those same complete Edge values and literal shared endpoints. -/
@[expose] def chain (trace : RootTrace leg budget) :
    SquareRootTrace.Chain (Paths.polynomial parameter) trace.samples.head.2.val trace.samples.tail.values
      (coordinate site parameter 2 quarter (by decide +kernel) 0)
      ((DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).map
        (coordinate site parameter 2 quarter (by decide +kernel))) := trace.2.2.2.val

/-- The complete retained Chain is the original direct fold of the same stored Edge bank. -/
theorem chain_eq (trace : RootTrace leg budget) : trace.chain = Readings.Edges.chain trace.edges := trace.2.2.2.property

/-- The sampled Chain keeps precisely one root edge per original selected dyadic edge. -/
theorem count (trace : RootTrace leg budget) : trace.samples.tail.values.length = 2 ^ budget.selection.stage :=
  (Readings.Edges.chain_root_count trace.edges).trans (DyadicSteps.tail_length budget.selection.stage 0 1)

/-- The first retained vertex is the identical complete original Leg source Reading. -/
theorem source (trace : RootTrace leg budget) : trace.readings.get 0 = leg.source := by
  rewrite [trace.readings_eq, Readings.get_ofLeg]
  exact leg.readingAt_zero

/-- The last retained vertex is the identical complete original target Reading, with only exact time transport. -/
theorem target (trace : RootTrace leg budget) :
    HEq (trace.readings.get (Fin.last (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length))
      leg.target := by
  rewrite [trace.readings_eq, Readings.get_ofLeg]
  exact leg.readingAt_of_one _ _ ((DyadicTrace.indexed_last (0 : Fraction.Rational)
    (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)).trans
      (DyadicTrace.tail_terminal budget.selection.stage 0 1))

/-- The last retained original Reading has the exact same named channel as the original quarter target.

Only the computed endpoint-time equality transports the complete original
Reading. The original target-ownership equality supplies the readback; no
new lift or independently selected numerical channel is constructed.
-/
theorem target_name (trace : RootTrace leg budget) :
    (trace.readings.get
      (Fin.last (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length)).lift.value.name =
        leg.target.lift.value.name := by
  have project (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
      (reading : Reading leg.actual time inside) (equal : time = 1) (same : HEq reading leg.target) :
      reading.lift.value.name = leg.target.lift.value.name := by
    cases equal
    exact congrArg (fun retained : Reading leg.actual 1 (by decide +kernel) => retained.lift.value.name)
      (eq_of_heq same)
  exact project _ _ _ ((DyadicTrace.indexed_last (0 : Fraction.Rational)
    (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1)).trans
      (DyadicTrace.tail_terminal budget.selection.stage 0 1)) trace.target

/-- Read the actual stored movement cache through the complete retained Edge-bank factory equation. -/
theorem movement (trace : RootTrace leg budget)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    (trace.edges.get edge).data.movementBound = leg.traceMovement budget.bounds *
      (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 :=
  (congrArg (fun retained : Readings.Edges trace.samples => (retained.get edge).data.movementBound)
    trace.edges_eq).trans (Readings.Edges.ofLeg_movement leg budget trace.readings trace.samples edge)

end RootTrace

/-- The complete original sharp geometries materialized once on the same ordered reading table.

Each entry retains both actual readings, the full branch-factor clearance
and its exact paid spatial Route. The original constant chart-time payment
is derived from the same retained step certificate for every bounded edge.
-/
@[expose] def Geometries {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} (readings : Readings actual (first :: times) inside)
    (regular : parameter ≠ criticalValue site) (step : Fraction.Rational)
    (steps : DyadicSteps.Steps first times step)
    (payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) : Type 1 :=
  DependentProduct times (fun edge => Geometry (readings.get edge.castSucc) (readings.get edge.succ) regular (by
    change (DyadicTrace.indexed first times edge.succ - DyadicTrace.indexed first times edge.castSucc) ^ 2 ≤ _
    rewrite [steps.indexed edge]
    exact payment))

namespace Geometries

/-- Read the exact stored original geometry at its original bounded chart edge. -/
@[expose] def get {first : Fraction.Rational} {times : List Fraction.Rational} {inside : Inside (first :: times)}
    {readings : Readings actual (first :: times) inside} {regular : parameter ≠ criticalValue site}
    {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometries : Geometries readings regular step steps payment) (edge : Fin times.length) :
    Geometry (readings.get edge.castSucc) (readings.get edge.succ) regular (by
      change (DyadicTrace.indexed first times edge.succ - DyadicTrace.indexed first times edge.castSucc) ^ 2 ≤ _
      rewrite [steps.indexed edge]
      exact payment) := DependentProduct.get times geometries edge

/-- Materialize each full original sharp clearance and paid spatial Route once on those same stored readings. -/
def build {first : Fraction.Rational} {times : List Fraction.Rational} {inside : Inside (first :: times)}
    (readings : Readings actual (first :: times) inside) (regular : parameter ≠ criticalValue site)
    (step : Fraction.Rational) (steps : DyadicSteps.Steps first times step)
    (payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7)
    (clearanceAt : (time : Fraction.Rational) →
        {retained : ClearanceType (quarter := quarter) (first := time) regular //
          retained = Radial.Clearance.clearance site parameter (Waist.direction quarter time)
            regular actual.data.bound} := fun time =>
      ⟨Radial.Clearance.clearance site parameter (Waist.direction quarter time) regular actual.data.bound, rfl⟩) :
    Geometries readings regular step steps payment :=
  DependentProduct.ofFn times (fun edge => Geometry.build (readings.get edge.castSucc) (readings.get edge.succ)
    regular (by
      change (DyadicTrace.indexed first times edge.succ - DyadicTrace.indexed first times edge.castSucc) ^ 2 ≤ _
      rewrite [steps.indexed edge]
      exact payment) (clearanceAt (DyadicTrace.indexed first times edge.castSucc)))

end Geometries

/-- The original covered-block chain with its actual terminal owner and exact retained chart-edge count.

This is a Sigma/subtype view of the existing Blocks owner, not another path
or continuation family. Every stored block retains its complete primitive
cover, accepted root requests and actual terminal-owner cache.
-/
@[expose] def Chain (first : Fraction.Rational) (times : List Fraction.Rational)
    (source : Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive first))) : Type :=
  Σ target : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter positive (DyadicTrace.terminal first times))),
    { blocks : CoveredTracedPath.Blocks (Paths.polynomial parameter)
        (coordinate site parameter 2 quarter positive first) source
        (coordinate site parameter 2 quarter positive (DyadicTrace.terminal first times)) target //
      blocks.length = times.length }

/-- Consume the actual ordered geometry bank into original covered blocks with exact cached owner handoffs.

Each block is built once on the previous block's actual terminal Owner. The
reading and geometry tails are retained literally; the recursion constructs
no new reading, source attachment, clearance or Route.
-/
@[expose] def cover (first : Fraction.Rational) (times : List Fraction.Rational) :
    (inside : Inside (first :: times)) → (readings : Readings actual (first :: times) inside) →
    (regular : parameter ≠ criticalValue site) → (step : Fraction.Rational) →
    (steps : DyadicSteps.Steps first times step) →
    (payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) →
    Geometries readings regular step steps payment →
    (source : Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter positive first))) →
    Chain (quarter := quarter) (positive := positive) first times source :=
  match times with
  | [] => fun _ _ _ _ _ _ _ source =>
      ⟨source, ⟨.nil _ source, CoveredTracedPath.Blocks.length_nil _ source⟩⟩
  | next :: times => fun inside readings regular step steps payment geometries source =>
      let covered := Covered.build geometries.1 source
      let remainingGeometries : Geometries readings.tail regular step steps.2 payment := geometries.2
      let remaining := cover next times (fun time member => inside time (List.Mem.tail first member))
        readings.tail regular step steps.2 payment remainingGeometries covered.finishOwner
      ⟨remaining.1, ⟨.cons covered.block remaining.2.val, by
        rewrite [CoveredTracedPath.Blocks.length_cons]
        exact congrArg Nat.succ remaining.2.property⟩⟩
termination_by structural times

/-- The exact original depth-seven unit-quarter endpoint table. -/
@[irreducible, expose] def times : List Fraction.Rational := DyadicTrace.tail 7 0 1

/-- Every retained original mesh time lies in the closed unit quarter. -/
theorem times_inside : Inside (0 :: times) := by
  intro time member
  cases member with
  | head => exact ⟨Fraction.Order.Basic.le_refl _, by decide +kernel⟩
  | tail _ retained =>
      unfold times at retained
      exact DyadicTrace.tail_inside 7 (by decide +kernel) retained

/-- The original ordered mesh has the same exact dyadic chart step at every edge. -/
theorem times_steps : DyadicSteps.Steps 0 times ((1 - 0) * (1 / 2) ^ 7) := by
  unfold times
  exact DyadicSteps.tail_steps 7 0 1

/-- The internally fixed depth-seven chart mesh pays the original sharp-clearance bound. -/
theorem times_payment : (((1 : Fraction.Rational) - 0) * (1 / 2) ^ 7) ^ 2 ≤
    Geometric.Basic.quarterRadius 1 7 := by
  rewrite [Radial.Clearance.quarterRadius_seven]
  decide +kernel

/-- The internally fixed original quarter mesh contains exactly 128 ordered chart edges. -/
theorem times_length : times.length = 128 := by
  unfold times
  exact (DyadicSteps.tail_length 7 0 1).trans (by decide +kernel)

/-- The internally fixed original mesh has edges, so whole-quarter location cannot encounter an empty tail. -/
theorem times_nonempty : times ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  change times.length = 0 at length
  rewrite [times_length] at length
  cases length

/-- The original ordered unit-quarter mesh ends at the exact original chart-time target. -/
theorem times_terminal : DyadicTrace.terminal (0 : Fraction.Rational) times = 1 := by
  unfold times
  exact DyadicTrace.tail_terminal 7 0 1

/-- Exact spatial endpoints of consecutive original geometric quarters agree, including the base-coordinate closure.

These are coordinate identities only. They permit transporting one actual
continued owner to the next source index; they do not identify independently
constructed roots or assert that the final owner returns to its first sheet.
-/
theorem quarter_seams (site : Fin 2) (parameter : Canonical) :
    coordinate site parameter 2 .first (by decide +kernel) (DyadicTrace.terminal 0 times) =
        coordinate site parameter 2 .second (by decide +kernel) 0 ∧
      coordinate site parameter 2 .second (by decide +kernel) (DyadicTrace.terminal 0 times) =
        coordinate site parameter 2 .third (by decide +kernel) 0 ∧
      coordinate site parameter 2 .third (by decide +kernel) (DyadicTrace.terminal 0 times) =
        coordinate site parameter 2 .fourth (by decide +kernel) 0 ∧
      coordinate site parameter 2 .fourth (by decide +kernel) (DyadicTrace.terminal 0 times) =
        coordinate site parameter 2 .first (by decide +kernel) 0 := by
  have join {leftQuarter rightQuarter : UnitCircuitQuarter}
      (equal : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0) :
      coordinate site parameter 2 leftQuarter (by decide +kernel) (DyadicTrace.terminal 0 times) =
        coordinate site parameter 2 rightQuarter (by decide +kernel) 0 := by
    rewrite [times_terminal]
    exact congrArg (fun direction => (Radial.point site parameter 2 direction (by decide +kernel)).base) equal
  exact ⟨join Waist.directions_join.1, join Waist.directions_join.2.1,
    join Waist.directions_join.2.2.1, join Waist.directions_join.2.2.2⟩

/-- One original quarter and all its actual reading, geometry, attachment and covered-chain caches.

Every component is an existing owner/container. Factory equalities link the
same materialized banks to the consumed original covered chain. The complete
Leg retains its target reading independently of the continued finish Owner;
no matching coordinate is used to identify these distinct owners.
-/
@[expose] def Coverage (original : Leg site parameter quarter) : Type 1 :=
  Σ leg : {retained : Leg site parameter quarter // retained = original},
  Σ readings : {retained : Readings leg.val.actual (0 :: times) times_inside //
      retained = Readings.ofLeg leg.val (0 :: times) times_inside},
  Σ geometries : {retained : Geometries readings.val leg.val.regular _ times_steps times_payment //
      retained = Geometries.build readings.val leg.val.regular _ times_steps times_payment},
  Σ source : {retained : Source leg.val.source leg.val.sourcePrepared //
      retained = Source.build leg.val.source leg.val.sourcePrepared},
    {retained : Chain (positive := by decide +kernel) 0 times source.val.attached.owner //
      retained = cover 0 times times_inside readings.val leg.val.regular _ times_steps times_payment
        geometries.val source.val.attached.owner}

namespace Coverage

/-- Compute the original quarter caches and consume their exact ordered owner handoffs at the fixed finite depth. -/
def build (leg : Leg site parameter quarter) : Coverage leg :=
  let readings := Readings.ofLeg leg (0 :: times) times_inside
  let geometries := Geometries.build readings leg.regular _ times_steps times_payment
  let source := Source.build leg.source leg.sourcePrepared
  let chain := cover 0 times times_inside readings leg.regular _ times_steps times_payment
    geometries source.attached.owner
  ⟨⟨leg, rfl⟩, ⟨⟨readings, rfl⟩, ⟨⟨geometries, rfl⟩, ⟨⟨source, rfl⟩, ⟨chain, rfl⟩⟩⟩⟩⟩

variable {original : Leg site parameter quarter}

/-- Read the complete original retained Leg, including its root preparation, both endpoint readings and apart caches. -/
@[expose] def leg (coverage : Coverage original) : Leg site parameter quarter := coverage.1.val

/-- The complete retained Leg is the supplied original owner, not a reconstruction from its coordinate values. -/
theorem leg_eq (coverage : Coverage original) : coverage.leg = original := coverage.1.property

/-- Read the same complete materialized original quarter Reading table. -/
@[expose] def readings (coverage : Coverage original) : Readings coverage.leg.actual (0 :: times) times_inside :=
  coverage.2.1.val

/-- The retained table consumes the identical original Leg endpoint cache and prepared quarter. -/
theorem readings_eq (coverage : Coverage original) : coverage.readings =
    Readings.ofLeg coverage.leg (0 :: times) times_inside := coverage.2.1.property

/-- The first actual mesh entry is the identical complete original Leg source query. -/
theorem readings_source (coverage : Coverage original) :
    Readings.get (actual := coverage.leg.actual) (times := 0 :: times) (inside := times_inside)
      coverage.readings ⟨0, Nat.zero_lt_succ times.length⟩ = coverage.leg.source := by
  let index : Fin (0 :: times).length := ⟨0, Nat.zero_lt_succ times.length⟩
  have retained := congrArg
    (fun bank : Readings coverage.leg.actual (0 :: times) times_inside =>
      Readings.get (actual := coverage.leg.actual) (times := 0 :: times) (inside := times_inside) bank index)
    coverage.readings_eq
  have original := Readings.get_ofLeg coverage.leg (0 :: times) times_inside index
  exact retained.trans (original.trans coverage.leg.readingAt_zero)

/-- The final actual mesh entry retains the identical original target query at its exact original chart-time index. -/
theorem readings_target (coverage : Coverage original) :
    HEq (coverage.readings.get (Fin.last times.length)) coverage.leg.target := by
  rewrite [coverage.readings_eq, Readings.get_ofLeg]
  exact coverage.leg.readingAt_of_one _ _
    ((DyadicTrace.indexed_last (0 : Fraction.Rational) times).trans times_terminal)

/-- Read every retained original sharp geometry without invoking its clearance or Route builder. -/
@[expose] def geometries (coverage : Coverage original) :
    Geometries coverage.readings coverage.leg.regular _ times_steps times_payment := coverage.2.2.1.val

/-- The complete geometry bank is the original factory on those exact retained Reading objects. -/
theorem geometries_eq (coverage : Coverage original) : coverage.geometries =
    Geometries.build coverage.readings coverage.leg.regular _ times_steps times_payment := coverage.2.2.1.property

/-- Read the identical original completed source attachment, with its own retained product-channel comparison. -/
@[expose] def source (coverage : Coverage original) : Source coverage.leg.source coverage.leg.sourcePrepared :=
  coverage.2.2.2.1.val

/-- The source attachment is the original factory on the same retained source reading and prepared channel. -/
theorem source_eq (coverage : Coverage original) : coverage.source =
    Source.build coverage.leg.source coverage.leg.sourcePrepared := coverage.2.2.2.1.property

/-- Read the stored complete original covered chain and its actual terminal owner. -/
@[expose] def chain (coverage : Coverage original) :
    Chain (positive := by decide +kernel) 0 times coverage.source.attached.owner := coverage.2.2.2.2.val

/-- The complete stored chain consumes the same retained geometry bank and source attachment. -/
theorem chain_eq (coverage : Coverage original) : coverage.chain =
    cover 0 times times_inside coverage.readings coverage.leg.regular _ times_steps times_payment
      coverage.geometries coverage.source.attached.owner := coverage.2.2.2.2.property

/-- Continue the same retained original quarter geometry from a supplied actual source owner.

Both materialized Reading and Geometry banks are consumed unchanged. The
covered preparations are constructed on this supplied owner, passing every
actual finish owner to the next block. No source attachment, root-reading,
clearance or Route factory is called here. The original coverage's separately
stored chain and attachment remain unchanged; use chain for that original
source rather than repeating its construction through this operation.
-/
@[expose] def continueFrom (coverage : Coverage original)
    (owner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) 0))) :
    Chain (positive := by decide +kernel) 0 times owner :=
  cover 0 times times_inside coverage.readings coverage.leg.regular _ times_steps times_payment
    coverage.geometries owner

/-- Continuation on the retained banks has the same internally paid whole-quarter block count. -/
theorem continueFrom_count (coverage : Coverage original)
    (owner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) 0))) :
    (coverage.continueFrom owner).2.val.length = 128 :=
  (coverage.continueFrom owner).2.property.trans times_length

/-- Append the retained quarter geometry after an actual covered prefix at an exact spatial-coordinate seam.

The next continuation starts at the prefix's very same finish owner, with
only its parameter index transported by the coordinate equality. The result
is the existing Blocks owner and its complete caches, not a new path family.
The independent original target Reading is not identified with its finish.
-/
@[expose] def appendFrom (coverage : Coverage original) {start finish : Canonical}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {last : Owner ((Paths.polynomial parameter).eval finish)}
    (prefixBlocks : CoveredTracedPath.Blocks (Paths.polynomial parameter) start owner finish last)
    (seam : finish = coordinate site parameter 2 quarter (by decide +kernel) 0) :
    Σ target : Owner ((Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal 0 times))),
      {blocks : CoveredTracedPath.Blocks (Paths.polynomial parameter) start owner
          (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal 0 times)) target //
        blocks.length = prefixBlocks.length + 128} :=
  (fun (nextOwner : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) 0)))
    (sameOwner : HEq last nextOwner)
    (next : Chain (quarter := quarter) (positive := by decide +kernel) 0 times nextOwner) =>
      ⟨next.1, ⟨CoveredTracedPath.Blocks.appendAt prefixBlocks next.2.val seam sameOwner, by
        exact (CoveredTracedPath.Blocks.appendAt_length prefixBlocks next.2.val seam sameOwner).trans
          (congrArg (fun count => prefixBlocks.length + count) (next.2.property.trans times_length))⟩⟩)
    (SquareRoot.Owner.Transport.castOwnerParameter (congrArg (Paths.polynomial parameter).eval seam) last)
    (SquareRoot.Owner.Transport.castOwnerParameter_heq (congrArg (Paths.polynomial parameter).eval seam) last).symm
    (coverage.continueFrom
      (SquareRoot.Owner.Transport.castOwnerParameter (congrArg (Paths.polynomial parameter).eval seam) last))

/-- Appending a retained quarter preserves the prefix's complete moving cache and the actual new continuation cache. -/
theorem appendFrom_movingVertices (coverage : Coverage original) {start finish : Canonical}
    {owner : Owner ((Paths.polynomial parameter).eval start)}
    {last : Owner ((Paths.polynomial parameter).eval finish)}
    (prefixBlocks : CoveredTracedPath.Blocks (Paths.polynomial parameter) start owner finish last)
    (seam : finish = coordinate site parameter 2 quarter (by decide +kernel) 0) :
    (coverage.appendFrom prefixBlocks seam).2.val.movingVertices = prefixBlocks.movingVertices ++
      (coverage.continueFrom
        (SquareRoot.Owner.Transport.castOwnerParameter
          (congrArg (Paths.polynomial parameter).eval seam) last)).2.val.movingVertices :=
  prefixBlocks.appendAt_movingVertices _ seam (SquareRoot.Owner.Transport.castOwnerParameter_heq _ last).symm

/-- Read the original Blocks container with its exact cached primitive covers and terminal-owner handoffs. -/
@[expose] def blocks (coverage : Coverage original) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) coverage.source.attached.owner
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal 0 times)) coverage.chain.1 :=
  coverage.chain.2.val

/-- The whole-quarter construction retains exactly the internally computed 128 original spatial blocks. -/
theorem count (coverage : Coverage original) : coverage.blocks.length = 128 :=
  coverage.chain.2.property.trans times_length

/-- Read the actual continued finish Owner of the original covered quarter without replacing its independent target. -/
@[expose] def finishOwner (coverage : Coverage original) :
    Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal 0 times))) := coverage.chain.1

/-- Read the complete original spatial OwnerPath on its exact initial attachment and actual continued finish Owner. -/
@[expose] def trace (coverage : Coverage original) : OwnerPath (Paths.polynomial parameter)
    (coordinate site parameter 2 quarter (by decide +kernel) 0) coverage.source.attached.owner
    (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal 0 times)) coverage.finishOwner :=
  coverage.blocks.trace

/-- Locate every original unit-quarter point in an actual retained block's sharp-clear source box.

The computed bounded index reads the same original mesh and geometry bank.
Its returned inequalities pay containment of the whole curved chart interval,
not only its two sampled endpoints. The corresponding original clearance is
read through geometries.get at that identical index without rebuilding it.
-/
def locate (coverage : Coverage original) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    {edge : Fin times.length //
      (box site parameter quarter (DyadicTrace.indexed 0 times edge.castSucc) coverage.leg.regular).Contains
        (coordinate site parameter 2 quarter (by decide +kernel) time)} :=
  let selected := DyadicTrace.locate 0 times times_nonempty time inside.1 (by
    rewrite [times_terminal]
    exact inside.2)
  have payment : (DyadicTrace.indexed 0 times selected.val.succ -
      DyadicTrace.indexed 0 times selected.val.castSucc) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := by
    rewrite [times_steps.indexed selected.val]
    exact times_payment
  ⟨selected.val, interval_inside coverage.leg.regular payment time selected.property⟩

/-- The original trace keeps the signed raw winding of those same ordered covered-preparation moving caches. -/
theorem winding_eq (coverage : Coverage original) :
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) coverage.trace.vertices =
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) coverage.blocks.movingVertices :=
  coverage.blocks.trace_winding_eq

end Coverage

/-- Cover one selected original circuit leg while retaining the entire circuit and all four original signed seams.

The new spatial finish Owner remains distinct from the circuit's original
target Reading. This operation constructs one complete covered quarter;
closing four such traces requires their original endpoint comparisons.
-/
@[expose] def coverLeg (original : Circuit site parameter) (quarter : UnitCircuitQuarter) :
    Σ retained : {actual : Circuit site parameter // actual = original}, Coverage (retained.val.leg quarter) :=
  ⟨⟨original, rfl⟩, Coverage.build (original.leg quarter)⟩

/-- Retaining a covered circuit leg preserves the entire supplied original circuit and every original seam. -/
theorem coverLeg_circuit (original : Circuit site parameter) (quarter : UnitCircuitQuarter) :
    (coverLeg original quarter).1.val = original := rfl

/-- Construct the original regular nodal circuit and one whole covered quarter from intrinsic local parameter data.

The fixed radius and regularity hypotheses describe the existing local
nodal neighbourhood. All root budgets, accepted cofactor moves, actual
readings, clearances and sufficient subdivision are constructed internally.
-/
def buildLeg (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : RadiusBound site parameter) (quarter : UnitCircuitQuarter) :
    Σ original : Circuit site parameter, Coverage (original.leg quarter) :=
  let original := Circuit.build site parameter regular bound
  ⟨original, Coverage.build (original.leg quarter)⟩

end WholeQuarter

open Purelib.Polynomial.Dense.Gaussian.Bounds

/-- The same retained sharp-clearance spatial route lies in the original canonical Legendre ambient.

The actual quarter's retained radius condition admits both original curved
endpoints to their existing collision square. Its exact hull contains the
computed spatial route, so box refinement transports that same whole path
without extending clear grid lines or replacing its signed root owners. -/
theorem Geometry.route_inAmbient
    {reading : Reading actual first firstInside} {targetReading : Reading actual last lastInside}
    {regular : parameter ≠ criticalValue site}
    {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Geometry reading targetReading regular payment) :
    Polynomial.Geometry.ClearPath.InBox (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))
      geometry.route.path := by
  have firstSpatial := Radial.point_inside site parameter 2 (Waist.direction quarter first) positive
    (by decide) (by decide) actual.data.bound
  have lastSpatial := Radial.point_inside site parameter 2 (Waist.direction quarter last) positive
    (by decide) (by decide) actual.data.bound
  have firstRefines : (Box.Point.pointBox (coordinate site parameter 2 quarter positive first)).Refines
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)) :=
    (spatialBox_refines_largeSquare site parameter).contains firstSpatial
  have lastRefines : (Box.Point.pointBox (coordinate site parameter 2 quarter positive last)).Refines
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)) :=
    (spatialBox_refines_largeSquare site parameter).contains lastSpatial
  exact Polynomial.Geometry.ClearPath.InBox.mono (Box.Hull.refines firstRefines lastRefines) geometry.route_inBox

namespace Geometry

open Purelib.Geometry.Rational.Box.Square
open Purelib.Geometry.Rational.Box.Refinement
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Geometry.Grid

/-- The same uniform small square about a physical point, independent of its source occurrence. -/
def neighborhood (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site) (value : Canonical) : Box :=
  Centered.Affine.centeredSquare value (Radial.Clearance.radius site parameter / 32)
    (Fraction.Order.Field.div_pos_direct (Radial.Clearance.radius_positive site parameter regular)
      (by decide +kernel)).le

/-- Every original neighbourhood has proper rational sides from the same positive sharp radius. -/
theorem neighborhood_proper (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site) (value : Canonical) :
    (neighborhood site parameter regular value).Proper :=
  Centered.centeredSquare_proper value
    (Fraction.Order.Field.div_pos_direct (Radial.Clearance.radius_positive site parameter regular)
      (by decide +kernel))

/-- Actual nodal vertices give strict ambient containment for their uniform neighbourhood.

The retained parameter budget bounds the sharp radius by one five-hundred-
twelfth. The same original vertex lies in the half-width-one-half nodal
box; its endpoint enclosure is at most three halves, while the original
coefficient-computed ambient radius is at least four.
-/
theorem neighborhood_inAmbient (site : Fin 2) (parameter : Canonical)
    (regular : parameter ≠ criticalValue site)
    (bound : Data.Gaussian.Norm.Basic.normSq (parameter - criticalValue site) ≤
      (1 / 64 : Fraction.Rational))
    (value : Canonical) (inside : (spatialBox site).Contains value) :
    (neighborhood site parameter regular value).StrictInterior
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)) := by
  have enclosed := (spatialBox site).refines_symmetric_of_enclosingRadius_le
    (by decide +kernel : (0 : Fraction.Rational) ≤ 3 / 2) (spatialBox_enclosingRadius_le site)
  have coordinates := enclosed.contains inside
  change -(3 / 2 : Fraction.Rational) ≤ value.re ∧ value.re ≤ 3 / 2 ∧
    -(3 / 2 : Fraction.Rational) ≤ value.im ∧ value.im ≤ 3 / 2 at coordinates
  let delta := Radial.Clearance.radius site parameter / 32
  let outer := RootRadius.denseLargeSquareRadius (Paths.polynomial parameter)
  have deltaUpper : delta ≤ 1 :=
    (Fraction.Order.Field.divide_mono (Radial.Clearance.radius_le site parameter bound)
      (by decide +kernel : (0 : Fraction.Rational) < 32)).trans (by decide +kernel)
  have margin : (3 / 2 : Fraction.Rational) + delta < outer :=
    ((Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) deltaUpper).trans_lt
      (by decide +kernel : (3 / 2 : Fraction.Rational) + 1 < 4)).trans_le
        (Curves.Legendre.Polynomial.four_le_largeSquareRadius parameter)
  have lower (coordinate : Fraction.Rational) (paid : -(3 / 2 : Fraction.Rational) ≤ coordinate) :
      -outer < coordinate - delta := by
    calc
      -outer < -((3 / 2 : Fraction.Rational) + delta) :=
        Arithmetic.neg_lt_neg_direct margin
      _ = -(3 / 2 : Fraction.Rational) - delta := by ring0
      _ ≤ coordinate - delta := Arithmetic.sub_le_sub_right_direct paid _
  have upper (coordinate : Fraction.Rational) (paid : coordinate ≤ (3 / 2 : Fraction.Rational)) :
      coordinate + delta < outer :=
    (Arithmetic.add_le_add_right_direct paid delta).trans_lt margin
  exact ⟨lower _ coordinates.1, upper _ coordinates.2.1,
    lower _ coordinates.2.2.1, upper _ coordinates.2.2.2⟩

/-- Move a physical point using one original eliminant and the same literal neighbourhood rule. -/
def move {degreeBound : Nat}
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (regular : parameter ≠ criticalValue site) (value : Canonical) : Canonical :=
  Extension.gapPoint elimination (neighborhood site parameter regular value)
    (neighborhood_proper site parameter regular value)

/-- Original paired line payloads with the whole same-neighbourhood factory identity. -/
@[expose] def Lines {degreeBound : Nat} {ambient : Box}
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (regular : parameter ≠ criticalValue site)
    (value : Canonical) (inside : (neighborhood site parameter regular value).Refines ambient) : Type :=
  {retained : VerticalLine (Paths.polynomial parameter) ambient ×
      HorizontalLine (Paths.polynomial parameter) ambient //
    retained = Extension.gapLines elimination clearances (neighborhood site parameter regular value)
      (neighborhood_proper site parameter regular value) inside}

namespace Lines

variable {degreeBound : Nat} {ambient : Box}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination} {value : Canonical}
variable {inside : (neighborhood site parameter regular value).Refines ambient}

/-- Read the intersection of the literal cached line payloads, without another coordinate scan. -/
@[expose] def point (lines : Lines elimination clearances regular value inside) : Canonical :=
  Data.Gaussian.Basic.point lines.val.1.coordinate lines.val.2.coordinate

/-- The cached intersection is the same uniform point on its actual original source coordinate. -/
theorem point_eq (lines : Lines elimination clearances regular value inside) :
    lines.point = move elimination regular value :=
  (congrArg (fun pair : VerticalLine (Paths.polynomial parameter) ambient ×
      HorizontalLine (Paths.polynomial parameter) ambient =>
    Data.Gaussian.Basic.point pair.1.coordinate pair.2.coordinate) lines.property).trans
      (Extension.gapLines_point elimination clearances _ _ inside)

/-- The actual cached intersection lies in its same original small neighbourhood. -/
theorem point_inside (lines : Lines elimination clearances regular value inside) :
    (neighborhood site parameter regular value).Contains lines.point := by
  rewrite [lines.point_eq]
  exact (Extension.gapPoint_spec elimination _ _).2.2.contains

/-- The same retained selected point belongs to its original sharp source square.

The original small-neighbourhood inclusion uses the retained positive
radius and the literal point_inside readback; no new line is selected.
-/
theorem point_in_source
    {inside : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    (lines : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) inside) :
    (box site parameter quarter first regular).Contains lines.point := by
  have smaller : Radial.Clearance.radius site parameter / 32 < Radial.Clearance.radius site parameter := by
    apply (Fraction.Order.Field.div_lt_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 32)).mpr
    calc
        Radial.Clearance.radius site parameter = 1 * Radial.Clearance.radius site parameter := by ring1
        _ < 32 * Radial.Clearance.radius site parameter :=
          Arithmetic.mul_lt_mul_of_pos_right_direct
            (by decide +kernel : (1 : Fraction.Rational) < 32)
            (Radial.Clearance.radius_positive site parameter regular)
        _ = Radial.Clearance.radius site parameter * 32 := by ring1
  exact (StrictInterior.refines (Centered.centeredSquare_strictInterior_of_lt
    (coordinate site parameter 2 quarter positive first)
    (Fraction.Order.Field.div_pos_direct (Radial.Clearance.radius_positive site parameter regular)
      (by decide +kernel)).le (Radial.Clearance.radius_positive site parameter regular).le
        smaller)).contains lines.point_inside

/-- The same retained target point belongs to the source square paid by its original chart step.

The existing quarter payment places the entire original target
neighbourhood in that source square. The selected line payloads and
all original physical indices remain unchanged.
-/
theorem point_in_target
    {inside : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (lines : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) inside)
    (first : Fraction.Rational)
    (payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) :
    (box site parameter quarter first regular).Contains lines.point := by
  exact (StrictInterior.refines (Radial.Clearance.quarter_target_neighborhood_strictInterior
    site parameter quarter regular first last payment)).contains lines.point_inside

universe u

/-- Original paired line caches at each occurrence of a retained finite physical point list.

The original items and location function preserve repetitions. Their
intrinsic nodal containment and retained parameter bound place every
uniform neighbourhood in the same original coefficient-computed ambient.
-/
@[expose] def Bank {α : Type u}
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (regular : parameter ≠ criticalValue site)
    (bound : Data.Gaussian.Norm.Basic.normSq (parameter - criticalValue site) ≤
      (1 / 64 : Fraction.Rational))
    (items : List α) (location : α → Canonical)
    (contained : ∀ item, (spatialBox site).Contains (location item)) : Type :=
  DependentProduct items (fun index => Lines elimination clearances regular
    (location (items[index.val]'index.isLt))
    (StrictInterior.refines (neighborhood_inAmbient site parameter regular bound _ (contained _))))

namespace Bank

variable {α : Type u}
variable {bound : Data.Gaussian.Norm.Basic.normSq (parameter - criticalValue site) ≤
  (1 / 64 : Fraction.Rational)}
variable {items : List α} {location : α → Canonical}
variable {contained : ∀ item, (spatialBox site).Contains (location item)}

/-- Compute each occurrence's original paired line payload once using the same retained eliminant. -/
def build (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (regular : parameter ≠ criticalValue site)
    (bound : Data.Gaussian.Norm.Basic.normSq (parameter - criticalValue site) ≤
      (1 / 64 : Fraction.Rational))
    (items : List α) (location : α → Canonical)
    (contained : ∀ item, (spatialBox site).Contains (location item)) :
    Bank elimination clearances regular bound items location contained :=
  DependentProduct.ofFn items (fun _index => ⟨Extension.gapLines elimination clearances _ _ _, rfl⟩)

/-- Read the literal original first paired line payload without reconstructing its family. -/
@[expose] def head {item : α} {remaining : List α}
    (bank : Bank elimination clearances regular bound (item :: remaining) location contained) :
    Lines elimination clearances regular (location item)
      (StrictInterior.refines (neighborhood_inAmbient site parameter regular bound _ (contained _))) := bank.1

/-- Read the unchanged paired-line suffix with its original location and containment data. -/
@[expose] def tail {item : α} {remaining : List α}
    (bank : Bank elimination clearances regular bound (item :: remaining) location contained) :
    Bank elimination clearances regular bound remaining location contained := bank.2

/-- Read the literal retained paired line list in original occurrence order. -/
@[expose] def pairs (bank : Bank elimination clearances regular bound items location contained) :
    List (VerticalLine (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)) ×
      HorizontalLine (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :=
  DependentProduct.mapToList items bank (fun _index retained => retained.val)

/-- Read the intersections of those same actual paired line payloads. -/
@[expose] def points (bank : Bank elimination clearances regular bound items location contained) : List Canonical :=
  bank.pairs.map (fun pair => Data.Gaussian.Basic.point pair.1.coordinate pair.2.coordinate)

/-- The cached intersections are the uniform moves of the same original locations in their original order. -/
theorem points_eq (bank : Bank elimination clearances regular bound items location contained) :
    bank.points = items.map (fun item => move elimination regular (location item)) := by
  unfold points pairs
  rewrite [DependentProduct.map_mapToList]
  exact (DependentProduct.mapToList_congr items bank _ _ (fun _index retained => retained.point_eq)).trans
    (DependentProduct.mapToList_items items bank (fun item => move elimination regular (location item)))

/-- Extending the same original grid with the retained pairs includes every moved occurrence. -/
theorem onExtended (bank : Bank elimination clearances regular bound items location contained)
    (base : ClearGrid (Paths.polynomial parameter) (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    ∀ point ∈ bank.points, FromStates.ContainsVertex
      (Extension.extend base (bank.pairs.map Prod.fst) (bank.pairs.map Prod.snd)) point := by
  intro point member
  rcases Data.List.Map.mem_map.mp member with ⟨pair, retained, same⟩
  cases same
  constructor
  · apply Extension.extend_vertical
    exact Data.List.Map.mem_map.mpr ⟨pair.1, Data.List.Map.mem_map.mpr ⟨pair, retained, rfl⟩, rfl⟩
  · apply Extension.extend_horizontal
    exact Data.List.Map.mem_map.mpr ⟨pair.2, Data.List.Map.mem_map.mpr ⟨pair, retained, rfl⟩, rfl⟩

end Bank

end Lines

/-- Build the moved route from the original sharp-clearance cache and literal selected line payloads.

Both inclusions follow from the original chart payment and same radius,
including stationary and coordinate-degenerate routes. No root or signed
sheet is identified merely because these numeric endpoints agree.
-/
def detour {degreeBound : Nat} {ambient : Box}
    (geometry : Geometry reading targetReading regular payment)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    {firstAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    {lastAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (source : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) firstAmbient)
    (target : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) lastAmbient) :
    ClearBoxPaths.Route (Paths.polynomial parameter) (box site parameter quarter first regular)
      source.point target.point :=
  ClearBoxPaths.Route.build geometry.clearance source.point target.point
    source.point_in_source (target.point_in_target first payment)

/-- Split the same moved sharp-clearance route on a supplied original grid.

The two membership witnesses concern the literal cached paired-line
intersections. Endpoint transport uses their original uniform-point laws;
no root, Reading or paid Block is acquired by this numeric operation.
-/
def detourWalk {degreeBound : Nat} {ambient : Box}
    (geometry : Geometry reading targetReading regular payment)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    {firstAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    {lastAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (source : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) firstAmbient)
    (target : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) lastAmbient)
    (grid : ClearGrid (Paths.polynomial parameter) ambient)
    (sourceOn : FromStates.ContainsVertex grid source.point)
    (targetOn : FromStates.ContainsVertex grid target.point) :
    Walks.Walk grid (move elimination regular (coordinate site parameter 2 quarter positive first))
      (move elimination regular (coordinate site parameter 2 quarter positive last)) :=
  let route := geometry.detour elimination clearances source target
  let walk := Walks.splitPath grid route.path
    (Extension.route_vertices grid geometry.clearance _ _ _ _ route rfl sourceOn targetOn)
  walk.castEndpoints source.point_eq target.point_eq

/-- Splitting the actual moved route preserves its complete original integer winding.

The same literal paired-line cache and endpoint equations are consumed.
This is the winding of the retained numeric path, not its sheet closure
or an identification with the original source path.
-/
theorem detourWalk_winding {degreeBound : Nat} {ambient : Box}
    (geometry : Geometry reading targetReading regular payment)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    {firstAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive first)).Refines ambient}
    {lastAmbient : (neighborhood site parameter regular
      (coordinate site parameter 2 quarter positive last)).Refines ambient}
    (source : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive first) firstAmbient)
    (target : Lines elimination clearances regular
      (coordinate site parameter 2 quarter positive last) lastAmbient)
    (grid : ClearGrid (Paths.polynomial parameter) ambient)
    (sourceOn : FromStates.ContainsVertex grid source.point)
    (targetOn : FromStates.ContainsVertex grid target.point) :
    PreparedPathWinding.ClearPath.rawWinding
      (geometry.detourWalk elimination clearances source target grid sourceOn targetOn).path =
      PreparedPathWinding.ClearPath.rawWinding
        (geometry.detour elimination clearances source target).path := by
  unfold detourWalk
  rewrite [Purelib.Polynomial.Geometry.Grid.Winding.Walk.castEndpoints_winding]
  exact Purelib.Polynomial.Geometry.Grid.Winding.splitPath_winding grid _ _

end Geometry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
