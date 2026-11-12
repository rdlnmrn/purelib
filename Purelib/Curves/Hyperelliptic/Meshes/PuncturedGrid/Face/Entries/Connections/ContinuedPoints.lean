module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Selection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.Points
public import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point

/-! # Actual continued Point junctions on two retained regular faces

The original source Point/Entry/join caches remain inputs. A single new
contained trace and Point serve both faces; each new face acquisition is
checked against actual propagated reachability. Coincident source targets
reuse the entire old pair by dependent index transport.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood (Neighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}

/-- A whole original Point keeps its count, neighborhood and actual local containment. -/
abbrev PointData (point : Canonical) :=
  Σ count : Nat, Σ patch : ContinuedNeighborhood curve.polynomial count,
    Σ _sample : ContinuedNeighborhood.Point patch point, {_value : Unit // patch.box.Contains point}

namespace PointData

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)

variable {point : Canonical} (data : PointData (curve := curve) point)

/-- Package one GIVEN actual continued Point with its original count, patch and certified containment. -/
@[expose] def ofPoint {count : Nat} {patch : ContinuedNeighborhood curve.polynomial count}
    (sample : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point) :
    PointData (curve := curve) point :=
  ⟨count, patch, sample, ⟨(), inside⟩⟩

/-- Read the SAME original continued neighborhood. -/
abbrev patch : ContinuedNeighborhood curve.polynomial data.1 := data.2.1

/-- Read the whole original Point, preserving its actual Owner and refinement data. -/
abbrev sample : ContinuedNeighborhood.Point data.patch point := data.2.2.1

/-- The actual Point lies in its retained local neighborhood. -/
theorem inside : data.patch.box.Contains point := data.2.2.2.property

universe u

variable {face : RegularFace bank} {models : FaceModels frames face}
    (insideFace : face.cell.box.Contains point)
    (acquired : Acquisition models insideFace data.sample.owner)
    {columns rows : Nat} {geometry : Geometry columns rows}
    (rectangles : RectangularPatch models.bounds (models.frame.owners acquired.entry.sheet) geometry)

/-- The original two model readings choose their nearest relative sign at the retained Point.

Both readings use the same stored numerical cell, Point patch and original
seeded refinement at depth two. This exact proposition keeps those owners
in callback signatures without expanding their polynomial evaluations.
-/
@[expose] def Nearest (owned : OwnedVertex geometry) : Prop :=
  normSq ((rectangles.models.ready owned.column owned.row).model.value.eval point -
      (data.patch.base.refine 2).value.eval point) ≤
    normSq ((rectangles.models.ready owned.column owned.row).model.value.eval point +
      (data.patch.base.refine 2).value.eval point)

/-- The exact mesh-vertex attachment consumer for one original continued Point and its acquisition.

The stored numerical vertex and transported cell retain their literal
original identities. The callback receives the genuinely continued mesh
Point, the reused target selector and acquisition, and the actual finite
cell-cover comparisons. The optional continuation keeps this same Point
available to later dependent work; its default preserves the original
constant-result callback. No replacement context or owner is introduced.
-/
@[expose] def MeshVertexConsumer
    {triangles : List (ModelTriangle geometry)} (surface : OwnedTriangulation triangles)
    (vertex : VertexLookup surface.mesh.vertices point) (basis : Differential genus)
    (meshCount : Nat) (Result : Type u)
    (afterPoint : TracedPoint models acquired.entry.sheet point
      insideFace meshCount acquired.pointFrame → Type u := fun _ => Result) :=
  (owned : OwnedVertex geometry) →
  owned = surface.owners vertex.index →
  (geometry.box owned.column owned.row).Contains point →
  (cell : TransportedCell models.bounds (models.frame.owners acquired.entry.sheet)
    (geometry.box owned.column owned.row)) →
  cell = rectangles.transported.cell owned.column owned.row →
  (meshPoint : TracedPoint models acquired.entry.sheet point
    insideFace meshCount acquired.pointFrame) →
  meshPoint = TracedPoint.build models acquired.entry.sheet point
    insideFace meshCount acquired.pointFrame →
  meshPoint.frame = acquired.pointFrame →
  (selection : OwnerSelection acquired.pointFrame.owners meshPoint.sample.owner) →
  selection = meshPoint.selectionAt acquired.pointFrame (some ⟨(), meshPoint.frame_eq.symm⟩) →
  HEq selection meshPoint.selected →
  (selectionEq : selection = acquired.pointFrame.select meshPoint.sample.owner) →
  (selected : Acquisition models insideFace meshPoint.sample.owner) →
  selected = acquired.ofSelection meshPoint.sample.owner selection selectionEq →
  (selectedEq : selected = acquired.selectOwner meshPoint.sample.owner) →
  selected.pointFrame = acquired.pointFrame →
  selected.entry.sheet = acquired.entry.sheet →
  selected.selected.index = acquired.selected.index →
  (compared : NamedEquivalent (ownerName meshPoint.sample.owner) (ownerName data.sample.owner)) →
  compared = acquired.equivalentOfEntry meshPoint.sample.owner selected
    selectedEq meshPoint.entry meshPoint.entry_sheet →
  (route : Route curve.polynomial (geometry.box owned.column owned.row)
    (geometry.box owned.column owned.row).anchor point) →
  (covered : CoveredTracedPath route.path cell.aligned.seed.owner) →
  (parents : ParentCache covered basis acquired.entry.sheet) →
  (roots : NamedEquivalent (ownerName covered.traced.finishOwner) data.sample.certificate.value.name) →
  (meshRoots : NamedEquivalent (ownerName covered.traced.finishOwner) (ownerName meshPoint.sample.owner)) →
  meshRoots = roots.trans compared.symm →
  Nearest data insideFace acquired rectangles owned → afterPoint meshPoint

/-- Attach one genuinely face-rooted mesh Point to the same actual supplied physical Point.

Numerical incidence supplies only the original owned-cell containment.
TracedPoint constructs the actual root/Entry lineage in the acquisition's
given complete frame. Its retained selector is reused through the whole
frame readback; only the new round-trip Entry is constructed. The original
rectangular comparison returns the same cell seed, contained cover,
parents and root comparison to the unchanged physical Point. All new
caches are forwarded with their exact equations.
-/
def withMeshVertex
    {triangles : List (ModelTriangle geometry)} (surface : OwnedTriangulation triangles)
    (vertex : VertexLookup surface.mesh.vertices point) (basis : Differential genus)
    (meshCount : Nat) {Result : Type u}
    (consume : MeshVertexConsumer data insideFace acquired rectangles surface vertex basis meshCount Result) :
    Result :=
  let owned := surface.owners vertex.index
  have inside : (geometry.box owned.column owned.row).Contains point :=
    Eq.mp (congrArg (geometry.box owned.column owned.row).Contains vertex.coordinate_eq)
      (surface.owner_inside vertex.index)
  let cell := rectangles.transported.cell owned.column owned.row
  let meshPoint := TracedPoint.build models acquired.entry.sheet point
    insideFace meshCount acquired.pointFrame
  let selection := meshPoint.selectionAt acquired.pointFrame (some ⟨(), meshPoint.frame_eq.symm⟩)
  have selectionEq : selection = acquired.pointFrame.select meshPoint.sample.owner :=
    meshPoint.selectionAt_reuse_eq acquired.pointFrame meshPoint.frame_eq.symm
  let selected := acquired.ofSelection meshPoint.sample.owner selection selectionEq
  have selectedEq : selected = acquired.selectOwner meshPoint.sample.owner :=
    acquired.ofSelection_eq_selectOwner meshPoint.sample.owner selection selectionEq
  have same : selected.entry.sheet = acquired.entry.sheet :=
    (selected.entry.sheet_unique meshPoint.entry insideFace).trans meshPoint.entry_sheet
  have index : selected.selected.index = acquired.selected.index :=
    acquired.selectOwner_index meshPoint.sample.owner selected selectedEq meshPoint.entry meshPoint.entry_sheet
  let compared := acquired.equivalentOfEntry meshPoint.sample.owner selected selectedEq
    meshPoint.entry meshPoint.entry_sheet
  PrimitiveComparison.FaceModels.withRectangularPointComparison (curve := curve)
    (models := models) (patch := data.patch) data.sample insideFace acquired rectangles
    owned.column owned.row basis inside data.inside
    (fun route covered parents roots near =>
      let meshRoots := roots.trans compared.symm
      consume owned rfl inside cell rfl meshPoint rfl meshPoint.frame_eq selection rfl
        (meshPoint.selectionAt_reuse_heq acquired.pointFrame meshPoint.frame_eq.symm) selectionEq selected rfl
        selectedEq
        ((congrArg (fun current : Acquisition models insideFace meshPoint.sample.owner =>
          current.pointFrame) selectedEq).trans (acquired.selectOwner_pointFrame meshPoint.sample.owner))
        same index compared rfl route covered parents roots meshRoots rfl near)

end PointData

/-- Two actual Point/Entry acquisition caches retain their literal operational join at one point.

This is the original tuple container used by a child LowerData. It keeps
both old Points when distinct; no desired child relation or final bound
is a field. The original source joins are actual supplied cached work.
-/
abbrev JunctionData (leftModels : FaceModels frames leftFace) (rightModels : FaceModels frames rightFace)
    {point : Canonical} (leftInside : leftFace.cell.box.Contains point)
    (rightInside : rightFace.cell.box.Contains point) :=
  Σ left : PointData (curve := curve) point, Σ right : PointData (curve := curve) point,
    Acquisition leftModels leftInside left.sample.owner × Acquisition rightModels rightInside right.sample.owner ×
      OwnerJoin left.sample.owner right.sample.owner

namespace JunctionData

variable {first last : Canonical} {firstLeft : leftFace.cell.box.Contains first}
variable {firstRight : rightFace.cell.box.Contains first}
variable (original : JunctionData leftModels rightModels firstLeft firstRight)

/-- Read the whole original left Point/count/patch cache. -/
abbrev left : PointData (curve := curve) first := original.1

/-- Read the independent original right Point/count/patch cache. -/
abbrev right : PointData (curve := curve) first := original.2.1

/-- Read the original left Entry acquisition without replaying its transports or selector. -/
abbrev leftAcquired : Acquisition leftModels firstLeft original.left.sample.owner := original.2.2.1

/-- Read the original right Entry acquisition on its own unchanged Point Owner. -/
abbrev rightAcquired : Acquisition rightModels firstRight original.right.sample.owner := original.2.2.2.1

/-- Read the SAME actual signed source join, preserving both original Point Owners. -/
abbrev joined : OwnerJoin original.left.sample.owner original.right.sample.owner := original.2.2.2.2

/-- Reindex the whole original Point/Entry/join product at the same literal geometric point.

Only the dependent point index and proof spelling change. Both distinct
Points, full acquisitions and the actual old join are transported together;
no Owner identity is inferred between the two Point caches.
-/
def castPoint (equal : last = first) (lastLeft : leftFace.cell.box.Contains last)
    (lastRight : rightFace.cell.box.Contains last) : JunctionData leftModels rightModels lastLeft lastRight := by
  cases equal
  exact original

/-- Whole-product point-index transport retains every original cache. -/
theorem castPoint_heq (equal : last = first) (lastLeft : leftFace.cell.box.Contains last)
    (lastRight : rightFace.cell.box.Contains last) : HEq (original.castPoint equal lastLeft lastRight) original := by
  cases equal
  rfl

/-- Point-index transport preserves the original selected left face sheet. -/
theorem castPoint_left_sheet (equal : last = first) (lastLeft : leftFace.cell.box.Contains last)
    (lastRight : rightFace.cell.box.Contains last) :
    (original.castPoint equal lastLeft lastRight).leftAcquired.entry.sheet = original.leftAcquired.entry.sheet := by
  cases equal
  rfl

/-- Point-index transport preserves the distinct original selected right face sheet. -/
theorem castPoint_right_sheet (equal : last = first) (lastLeft : leftFace.cell.box.Contains last)
    (lastRight : rightFace.cell.box.Contains last) :
    (original.castPoint equal lastLeft lastRight).rightAcquired.entry.sheet = original.rightAcquired.entry.sheet := by
  cases equal
  rfl

section Initial

variable (leftPoint rightPoint : PointData (curve := curve) first)
variable (leftEntry : Entry leftModels first leftPoint.sample.owner)
variable (rightEntry : Entry rightModels first rightPoint.sample.owner)
variable (sourceJoin : OwnerJoin leftPoint.sample.owner rightPoint.sample.owner)

/-- Actual original source Points and Entries acquire only the two missing full acquisition caches once. -/
abbrev Initial :=
  {value : PointData (curve := curve) first × PointData (curve := curve) first ×
      Entry leftModels first leftPoint.sample.owner × Entry rightModels first rightPoint.sample.owner ×
      OwnerJoin leftPoint.sample.owner rightPoint.sample.owner //
    value = (leftPoint, rightPoint, leftEntry, rightEntry, sourceJoin)} ×
  (Σ leftAcquired : {value : Acquisition leftModels firstLeft leftPoint.sample.owner //
      value = Acquisition.build leftModels firstLeft leftPoint.sample.owner},
  Σ rightAcquired : {value : Acquisition rightModels firstRight rightPoint.sample.owner //
      value = Acquisition.build rightModels firstRight rightPoint.sample.owner},
  {value : JunctionData leftModels rightModels firstLeft firstRight //
    value = ⟨leftPoint, rightPoint, leftAcquired.val, rightAcquired.val, sourceJoin⟩})

namespace Initial

/-- Retain both original source preparations and build their two full face acquisitions once.

The original Points, supplied bare Entries and actual source join are not
reacquired. The two new route/frame/selection acquisition caches are genuine
additional work required by the original LowerData interface.
-/
def build : Initial (firstLeft := firstLeft) (firstRight := firstRight)
    leftPoint rightPoint leftEntry rightEntry sourceJoin :=
  let leftAcquired := Acquisition.build leftModels firstLeft leftPoint.sample.owner
  let rightAcquired := Acquisition.build rightModels firstRight rightPoint.sample.owner
  let value : JunctionData leftModels rightModels firstLeft firstRight :=
    ⟨leftPoint, rightPoint, leftAcquired, rightAcquired, sourceJoin⟩
  (⟨(leftPoint, rightPoint, leftEntry, rightEntry, sourceJoin), rfl⟩,
    ⟨⟨leftAcquired, rfl⟩, ⟨rightAcquired, rfl⟩, ⟨value, rfl⟩⟩)

variable {leftPoint rightPoint leftEntry rightEntry sourceJoin}
variable (cached : Initial (firstLeft := firstLeft) (firstRight := firstRight)
  leftPoint rightPoint leftEntry rightEntry sourceJoin)

/-- Read the whole original-source Point/acquisition/join pair retained for all subsequent endpoints. -/
abbrev value : JunctionData leftModels rightModels firstLeft firstRight := cached.2.2.2.val

/-- The genuine left acquisition selects the SAME actual original source Entry sheet. -/
theorem left_sheet : cached.value.leftAcquired.entry.sheet = leftEntry.sheet :=
  (congrArg (fun value : JunctionData leftModels rightModels firstLeft firstRight =>
    value.leftAcquired.entry.sheet) cached.2.2.2.property).trans
    (cached.2.1.val.entry.sheet_unique leftEntry firstLeft)

/-- The genuine right acquisition retains the independent original source Entry sheet. -/
theorem right_sheet : cached.value.rightAcquired.entry.sheet = rightEntry.sheet :=
  (congrArg (fun value : JunctionData leftModels rightModels firstLeft firstRight =>
    value.rightAcquired.entry.sheet) cached.2.2.2.property).trans
    (cached.2.2.1.val.entry.sheet_unique rightEntry firstRight)

end Initial

end Initial

variable (lastLeft : leftFace.cell.box.Contains last) (lastRight : rightFace.cell.box.Contains last) (count : Nat)

/-- A genuine new trace, Point, two face acquisitions and one reflexive actual-owner join retain their full factories.

Both original source caches are retained separately by Continuation. The
new Point is seeded by the SAME traced terminal Owner. Reusing that ONE
Point in both faces is a construction choice, not identification of two
independently acquired roots or old numerical readings.
-/
abbrev Development :=
  Σ route : {value : Route curve.polynomial leftFace.cell.box first last //
    value = Route.build leftFace.clearance first last firstLeft lastLeft},
  Σ traced : {value : TracedPath route.val.path original.left.sample.owner //
    value = TracedPath.build route.val.path route.val.within original.left.sample.owner},
  Σ neighborhood : {value : Neighborhood traced.val count // value = Neighborhood.build traced.val count},
  Σ sample : {value : ContinuedNeighborhood.Point neighborhood.val.patch last //
    value = ContinuedNeighborhood.Point.acquire neighborhood.val.patch last neighborhood.val.center_inside},
  Σ _equivalent : {value : NamedEquivalent (ownerName traced.val.finishOwner) (ownerName sample.val.owner) //
    value = neighborhood.val.pointEquivalent sample.val},
  Σ _leftAcquired : {value : Acquisition leftModels lastLeft sample.val.owner //
    value = Acquisition.build leftModels lastLeft sample.val.owner},
  Σ _rightAcquired : {value : Acquisition rightModels lastRight sample.val.owner //
    value = Acquisition.build rightModels lastRight sample.val.owner},
  {value : OwnerJoin sample.val.owner sample.val.owner // value = OwnerJoin.reflexive sample.val.owner}

namespace Development

/-- The exact retained Point/acquisition suffix on an abstract original trace. -/
private abbrev Tail {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval first)}
    (traced : TracedPath path owner) :=
  Σ neighborhood : {value : Neighborhood traced count // value = Neighborhood.build traced count},
  Σ sample : {value : ContinuedNeighborhood.Point neighborhood.val.patch last //
    value = ContinuedNeighborhood.Point.acquire neighborhood.val.patch last neighborhood.val.center_inside},
  Σ _equivalent : {value : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.val.owner) //
    value = neighborhood.val.pointEquivalent sample.val},
  Σ _leftAcquired : {value : Acquisition leftModels lastLeft sample.val.owner //
    value = Acquisition.build leftModels lastLeft sample.val.owner},
  Σ _rightAcquired : {value : Acquisition rightModels lastRight sample.val.owner //
    value = Acquisition.build rightModels lastRight sample.val.owner},
  {value : OwnerJoin sample.val.owner sample.val.owner // value = OwnerJoin.reflexive sample.val.owner}

/-- Build the exact Point/acquisition suffix from an abstract SAME retained trace. -/
private def finish {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval first)}
    (traced : TracedPath path owner) :
    Tail (leftModels := leftModels) (rightModels := rightModels) lastLeft lastRight count traced :=
  let neighborhood := Neighborhood.build traced count
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch last neighborhood.center_inside
  let equivalent : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.owner) :=
    neighborhood.pointEquivalent sample
  let leftAcquired := Acquisition.build leftModels lastLeft sample.owner
  let rightAcquired := Acquisition.build rightModels lastRight sample.owner
  let joined := OwnerJoin.reflexive sample.owner
  ⟨⟨neighborhood, rfl⟩, ⟨sample, rfl⟩, ⟨equivalent, rfl⟩,
    ⟨leftAcquired, rfl⟩, ⟨rightAcquired, rfl⟩, ⟨joined, rfl⟩⟩

/-- Execute one new contained continuation and its original Point/Entry/join factories in order. -/
def build : Development original lastLeft lastRight count :=
  let route := Route.build leftFace.clearance first last firstLeft lastLeft
  let traced := TracedPath.build route.path route.within original.left.sample.owner
  let tail := finish (leftModels := leftModels) (rightModels := rightModels) lastLeft lastRight count traced
  ⟨⟨route, rfl⟩, ⟨traced, rfl⟩, tail⟩

variable {original lastLeft lastRight count} (cached : Development original lastLeft lastRight count)

/-- Read the whole actual contained source route. -/
abbrev route : Route curve.polynomial leftFace.cell.box first last := cached.1.val

/-- Read the SAME original traced continuation from the original source Point Owner. -/
abbrev traced : TracedPath cached.route.path original.left.sample.owner := cached.2.1.val

/-- Read the terminal-owner-seeded continued neighborhood. -/
abbrev neighborhood : Neighborhood cached.traced count := cached.2.2.1.val

/-- Read the actual once-acquired common Point. -/
abbrev sample : ContinuedNeighborhood.Point cached.neighborhood.patch last := cached.2.2.2.1.val

/-- Read the actual seed/refinement comparison to that SAME Point Owner. -/
abbrev equivalent : NamedEquivalent (ownerName cached.traced.finishOwner) (ownerName cached.sample.owner) :=
  cached.2.2.2.2.1.val

/-- Read the whole genuine new left face acquisition. -/
abbrev leftAcquired : Acquisition leftModels lastLeft cached.sample.owner := cached.2.2.2.2.2.1.val

/-- Read the whole genuine new right face acquisition on the SAME Point Owner. -/
abbrev rightAcquired : Acquisition rightModels lastRight cached.sample.owner := cached.2.2.2.2.2.2.1.val

/-- Read the one genuine new reflexive OwnerJoin and its actual acquired tail/comparison. -/
abbrev joined : OwnerJoin cached.sample.owner cached.sample.owner := cached.2.2.2.2.2.2.2.val

/-- The actual route keeps its whole original clear-face factory. -/
theorem route_eq : cached.route = Route.build leftFace.clearance first last firstLeft lastLeft := cached.1.property

/-- The retained trace keeps the whole original continuation factory. -/
theorem traced_eq : cached.traced =
    TracedPath.build cached.route.path cached.route.within original.left.sample.owner := cached.2.1.property

/-- The retained neighborhood keeps its original terminal-Owner-seeded factory. -/
theorem neighborhood_eq : cached.neighborhood = Neighborhood.build cached.traced count := cached.2.2.1.property

/-- The actual Point keeps its complete original acquisition factory. -/
theorem sample_eq : cached.sample = ContinuedNeighborhood.Point.acquire cached.neighborhood.patch last
    cached.neighborhood.center_inside := cached.2.2.2.1.property

/-- The retained terminal-to-Point comparison uses its actual cached neighborhood and Point. -/
theorem equivalent_eq : cached.equivalent = cached.neighborhood.pointEquivalent cached.sample :=
  cached.2.2.2.2.1.property

/-- The left Entry acquisition retains its whole original once-built result. -/
theorem leftAcquired_eq : cached.leftAcquired = Acquisition.build leftModels lastLeft cached.sample.owner :=
  cached.2.2.2.2.2.1.property

/-- The distinct right Entry acquisition retains its whole original once-built result. -/
theorem rightAcquired_eq : cached.rightAcquired = Acquisition.build rightModels lastRight cached.sample.owner :=
  cached.2.2.2.2.2.2.1.property

/-- The actual new OwnerJoin reuses one acquired tail on both sides of its reflexive comparison. -/
theorem joined_eq : cached.joined = OwnerJoin.reflexive cached.sample.owner := cached.2.2.2.2.2.2.2.property

/-- Both domain roles read the SAME supplied result of the new Point acquisition. -/
def value : JunctionData leftModels rightModels lastLeft lastRight :=
  let point : PointData (curve := curve) last :=
    ⟨count, cached.neighborhood.patch, cached.sample, ⟨(), cached.neighborhood.center_inside⟩⟩
  ⟨point, point, cached.leftAcquired, cached.rightAcquired, cached.joined⟩

/-- The SAME actual route also lies in the second old face, by both original endpoint containments. -/
theorem right_inside : InBox rightFace.cell.box cached.route.path := by
  have firstRefines : (Box.Point.pointBox first).Refines rightFace.cell.box := firstRight
  have lastRefines : (Box.Point.pointBox last).Refines rightFace.cell.box := lastRight
  have inside := InBox.mono (Box.Hull.refines firstRefines lastRefines)
    (Route.build_inBox leftFace.clearance first last firstLeft lastLeft)
  exact Eq.mpr (congrArg (fun route : Route curve.polynomial leftFace.cell.box first last =>
    InBox rightFace.cell.box route.path) cached.route_eq) inside

/-- The genuine new left acquisition selects the original source Entry's sheet. -/
theorem left_sheet : cached.value.leftAcquired.entry.sheet = original.leftAcquired.entry.sheet := by
  let inside := InBox.ofWithin cached.route.path cached.route.within firstLeft
  let carried := (original.leftAcquired.entry.followTrace cached.traced inside).followEquivalent cached.equivalent
  have same := cached.leftAcquired.entry.sheet_unique carried lastLeft
  exact same.trans
    (((original.leftAcquired.entry.followTrace cached.traced inside).followEquivalent_sheet cached.equivalent).trans
      (original.leftAcquired.entry.followTrace_sheet cached.traced inside))

/-- The second original source Entry and join reach the SAME new Point on their own unchanged face sheet. -/
theorem right_sheet : cached.value.rightAcquired.entry.sheet = original.rightAcquired.entry.sheet := by
  let source := original.rightAcquired.entry.followEquivalent original.joined.equivalent.symm
  let carried := (source.followTrace cached.traced cached.right_inside).followEquivalent cached.equivalent
  have same := cached.rightAcquired.entry.sheet_unique carried lastRight
  exact same.trans
    (((source.followTrace cached.traced cached.right_inside).followEquivalent_sheet cached.equivalent).trans
      ((source.followTrace_sheet cached.traced cached.right_inside).trans
        (original.rightAcquired.entry.followEquivalent_sheet original.joined.equivalent.symm)))

end Development

/-- Retain the actual old-cache reuse branch or the complete genuinely new continuation.

The first factor retains BOTH whole original source Point/Entry/join caches.
The geometric branch only chooses whether to reindex that original pair or
execute new trace/Point/acquisition work; it proves no equality of two Owners.
-/
abbrev Continuation :=
  {value : JunctionData leftModels rightModels firstLeft firstRight × Canonical × Nat //
    value = (original, last, count)} ×
  ((Σ equal : {_value : Unit // last = first},
      {value : JunctionData leftModels rightModels lastLeft lastRight //
        value = original.castPoint equal.property lastLeft lastRight}) ⊕
    (Σ _different : {_value : Unit // last ≠ first},
      {value : Development original lastLeft lastRight count //
        value = Development.build original lastLeft lastRight count}))

/-- Reuse the whole old pair at its exact point, otherwise acquire the new common endpoint work once. -/
def continueAt : Continuation original lastLeft lastRight count :=
  if equal : last = first then
    (⟨(original, last, count), rfl⟩,
      Sum.inl ⟨⟨(), equal⟩, ⟨original.castPoint equal lastLeft lastRight, rfl⟩⟩)
  else
    let developed := Development.build original lastLeft lastRight count
    (⟨(original, last, count), rfl⟩, Sum.inr ⟨⟨(), equal⟩, ⟨developed, rfl⟩⟩)

namespace Continuation

variable {original lastLeft lastRight count} (cached : Continuation original lastLeft lastRight count)

/-- Read the actual retained endpoint pair from the chosen cached branch, without rerunning its factory. -/
def value : JunctionData leftModels rightModels lastLeft lastRight :=
  match cached.2 with
  | Sum.inl reused => reused.2.val
  | Sum.inr developed => developed.2.val.value

/-- Both branches preserve the original source's actual left sheet. -/
theorem left_sheet : cached.value.leftAcquired.entry.sheet = original.leftAcquired.entry.sheet := by
  cases branch : cached.2 with
  | inl reused =>
      change (match cached.2 with
        | Sum.inl item => item.2.val
        | Sum.inr item => item.2.val.value).leftAcquired.entry.sheet = _
      rw [branch]
      change reused.2.val.leftAcquired.entry.sheet = _
      exact (congrArg (fun value : JunctionData leftModels rightModels lastLeft lastRight =>
        value.leftAcquired.entry.sheet) reused.2.property).trans
          (original.castPoint_left_sheet reused.1.property lastLeft lastRight)
  | inr developed =>
      change (match cached.2 with
        | Sum.inl item => item.2.val
        | Sum.inr item => item.2.val.value).leftAcquired.entry.sheet = _
      rw [branch]
      exact developed.2.val.left_sheet

/-- Both branches preserve the independent original source's actual right sheet. -/
theorem right_sheet : cached.value.rightAcquired.entry.sheet = original.rightAcquired.entry.sheet := by
  cases branch : cached.2 with
  | inl reused =>
      change (match cached.2 with
        | Sum.inl item => item.2.val
        | Sum.inr item => item.2.val.value).rightAcquired.entry.sheet = _
      rw [branch]
      change reused.2.val.rightAcquired.entry.sheet = _
      exact (congrArg (fun value : JunctionData leftModels rightModels lastLeft lastRight =>
        value.rightAcquired.entry.sheet) reused.2.property).trans
          (original.castPoint_right_sheet reused.1.property lastLeft lastRight)
  | inr developed =>
      change (match cached.2 with
        | Sum.inl item => item.2.val
        | Sum.inr item => item.2.val.value).rightAcquired.entry.sheet = _
      rw [branch]
      exact developed.2.val.right_sheet

end Continuation

end JunctionData

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

end
