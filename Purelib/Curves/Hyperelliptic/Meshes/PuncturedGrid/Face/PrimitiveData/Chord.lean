module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Chord
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.ContinuedPoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Points
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Riemann.Paths.ClearBoxPaths.Chord
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Tactic.Ring
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Readings.RectangularPointReadings.Chord
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Branches.RectangularSheetGauge

/-! # Same-domain Point lifts and primitive readings of an actual chord

The two complete physical Point caches and the original moving crop and
joins remain inputs. One actual interior Entry selects the original face
sheet. Its retained crop derives the last Point Entry; a genuinely new
first-to-corner trace seeds only the new corner Point. All three Entries
belong to that same selected original face-domain owner.

One supplied primitive bank supplies the three numerical values. Its
oriented triangle correction cancels on those SAME values. This operation
does not compare independently normalized primitives or conclude a period
or deformation equality for their physical observations.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Chord

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry
  (Acquisition PointData TracedPoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Branches
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.TracedPrimitiveNeighborhood (Neighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

universe u

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {basis : Differential genus}
    {parent : PreparedEdge curve basis} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {firstInside : face.cell.box.Contains (parent.point lower)}
    {lastInside : face.cell.box.Contains (parent.point upper)}

variable (shared : FaceDomains frames face)
    (geometry : ClearBoxPaths.Chord.Prepared face.clearance face.cell.box_proper
      (parent.point lower) (parent.point upper) firstInside lastInside)
    (first : PointData (curve := curve) (parent.point lower))
    (last : PointData (curve := curve) (parent.point upper))
    {source : Owner (curve.polynomial.eval (parent.point lower))}
    {target : Owner (curve.polynomial.eval (parent.point upper))}
    (moving : OwnerPath curve.polynomial (parent.point lower) source (parent.point upper) target)
    (vertices : moving.vertices = [parent.point upper])
    (sourceJoin : OwnerJoin first.sample.owner source) (targetJoin : OwnerJoin target last.sample.owner)
    (acquired : Acquisition shared.models firstInside first.sample.owner)
    (retainedDomain : PeriodDomain shared.models acquired.entry.sheet) (count : Nat)

/-- Retain the exact original inputs and only the new corner continuation caches.

The last Entry is derived from the original physical crop and supplied
joins. The corner trace begins at the original first Point Owner. The
selected domain is forced once from the original FaceDomains cache; no
second endpoint Point, face model bank or source query is acquired.
-/
@[expose] def Lifted :=
  {value : FaceDomains frames face ×
      ClearBoxPaths.Chord.Prepared face.clearance face.cell.box_proper
        (parent.point lower) (parent.point upper) firstInside lastInside ×
      PointData (curve := curve) (parent.point lower) × PointData (curve := curve) (parent.point upper) ×
      OwnerPath curve.polynomial (parent.point lower) source (parent.point upper) target ×
      OwnerJoin first.sample.owner source × OwnerJoin target last.sample.owner ×
      Acquisition shared.models firstInside first.sample.owner × PeriodDomain shared.models acquired.entry.sheet //
    value = (shared, geometry, first, last, moving, sourceJoin, targetJoin, acquired, retainedDomain)} ×
  (Σ _keptDomain : {value : PeriodDomain shared.models acquired.entry.sheet // value = retainedDomain},
  Σ route : {value : Route curve.polynomial face.cell.box (parent.point lower)
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper)) //
    value = Route.build face.clearance (parent.point lower)
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper))
      firstInside (ClearBoxPaths.Chord.corner_inside firstInside lastInside)},
  Σ traced : {value : TracedPath route.val.path first.sample.owner //
    value = TracedPath.build route.val.path route.val.within first.sample.owner},
  Σ neighborhood : {value : Neighborhood traced.val count // value = Neighborhood.build traced.val count},
  Σ sample : {value : ContinuedNeighborhood.Point neighborhood.val.patch
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper)) //
    value = ContinuedNeighborhood.Point.acquire neighborhood.val.patch _ neighborhood.val.center_inside},
  Σ equivalent : {value : NamedEquivalent (ownerName traced.val.finishOwner) (ownerName sample.val.owner) //
    value = neighborhood.val.pointEquivalent sample.val},
  {value : Entry shared.models (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper))
      sample.val.owner //
    value = (acquired.entry.followTrace traced.val
      (Polynomial.Geometry.ClearPath.InBox.ofWithin route.val.path route.val.within firstInside)).followEquivalent
        equivalent.val} ×
  {value : Entry shared.models (parent.point upper) last.sample.owner //
    value = ((acquired.entry.followJoin sourceJoin).followQueryCrop parent lower upper
      lowerInside upperInside moving vertices firstInside lastInside).followJoin targetJoin})

/-- Assemble unchanged original inputs and abstract corner caches without unfolding their factories. -/
private def assemble
    (route : Route curve.polynomial face.cell.box (parent.point lower)
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper)))
    (routeEq : route = Route.build face.clearance (parent.point lower)
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper))
      firstInside (ClearBoxPaths.Chord.corner_inside firstInside lastInside))
    (traced : TracedPath route.path first.sample.owner)
    (tracedEq : traced = TracedPath.build route.path route.within first.sample.owner)
    (neighborhood : Neighborhood traced count)
    (neighborhoodEq : neighborhood = Neighborhood.build traced count)
    (sample : ContinuedNeighborhood.Point neighborhood.patch
      (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper)))
    (sampleEq : sample = ContinuedNeighborhood.Point.acquire neighborhood.patch _ neighborhood.center_inside)
    (equivalent : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.owner))
    (equivalentEq : equivalent = neighborhood.pointEquivalent sample)
    (cornerEntry : Entry shared.models (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper))
      sample.owner)
    (cornerEq : cornerEntry = (acquired.entry.followTrace traced
      (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within firstInside)).followEquivalent equivalent)
    (lastEntry : Entry shared.models (parent.point upper) last.sample.owner)
    (lastEq : lastEntry = ((acquired.entry.followJoin sourceJoin).followQueryCrop parent lower upper
      lowerInside upperInside moving vertices firstInside lastInside).followJoin targetJoin) :
    Lifted (parent := parent) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      (firstInside := firstInside) (lastInside := lastInside)
      shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count :=
  ⟨⟨(shared, geometry, first, last, moving, sourceJoin, targetJoin, acquired, retainedDomain), rfl⟩,
    ⟨⟨retainedDomain, rfl⟩, ⟨route, routeEq⟩, ⟨traced, tracedEq⟩, ⟨neighborhood, neighborhoodEq⟩,
      ⟨sample, sampleEq⟩, ⟨equivalent, equivalentEq⟩, ⟨cornerEntry, cornerEq⟩, ⟨lastEntry, lastEq⟩⟩⟩

/-- Consume one actual first-Point acquisition and construct the same-domain corner lift once. -/
def ofAcquired : Lifted (parent := parent) (lower := lower) (upper := upper)
    (lowerInside := lowerInside) (upperInside := upperInside)
    (firstInside := firstInside) (lastInside := lastInside)
    shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count :=
  let route := Route.build face.clearance (parent.point lower)
    (ClearBoxPaths.Chord.corner (parent.point lower) (parent.point upper))
    firstInside (ClearBoxPaths.Chord.corner_inside firstInside lastInside)
  let traced := TracedPath.build route.path route.within first.sample.owner
  let neighborhood := Neighborhood.build traced count
  let sample := ContinuedNeighborhood.Point.acquire neighborhood.patch _ neighborhood.center_inside
  let equivalent : NamedEquivalent (ownerName traced.finishOwner) (ownerName sample.owner) :=
    neighborhood.pointEquivalent sample
  let cornerEntry := (acquired.entry.followTrace traced
    (Polynomial.Geometry.ClearPath.InBox.ofWithin route.path route.within firstInside)).followEquivalent equivalent
  let lastEntry := ((acquired.entry.followJoin sourceJoin).followQueryCrop parent lower upper
    lowerInside upperInside moving vertices firstInside lastInside).followJoin targetJoin
  assemble shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count
    route rfl traced rfl neighborhood rfl sample rfl equivalent rfl cornerEntry rfl lastEntry rfl

namespace Lifted

variable {shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count}
    (lifted : Lifted (parent := parent) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      (firstInside := firstInside) (lastInside := lastInside)
      shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count)

/-- Read all complete original inputs together, including both unchanged endpoint Points and joins. -/
abbrev originals := lifted.1.val

/-- Read the SAME once-forced original selected-sheet domain. -/
abbrev domain := lifted.2.1.val

/-- Read the genuine first-to-corner route without preparing it again. -/
abbrev route := lifted.2.2.1.val

/-- Read the SAME trace beginning at the original physical first Point Owner. -/
abbrev traced := lifted.2.2.2.1.val

/-- Read the actual traced-finish-seeded continued neighborhood. -/
abbrev neighborhood := lifted.2.2.2.2.1.val

/-- Read only the genuinely new corner Point; both physical endpoint Points stay in originals. -/
abbrev sample := lifted.2.2.2.2.2.1.val

/-- Read the original seed/refinement comparison for the same corner Point. -/
abbrev equivalent := lifted.2.2.2.2.2.2.1.val

/-- Read the corner Entry derived through the actual stored trace and root comparison. -/
abbrev cornerEntry := lifted.2.2.2.2.2.2.2.1.val

/-- Read the last physical Point Entry derived through the SAME original crop and joins. -/
abbrev lastEntry := lifted.2.2.2.2.2.2.2.2.val

/-- All complete original caches remain literally unchanged in the returned lift. -/
theorem originals_eq : lifted.originals =
    (shared, geometry, first, last, moving, sourceJoin, targetJoin, acquired, retainedDomain) := lifted.1.property

/-- The whole domain is the SAME supplied retained cache, without a new lookup or preparation. -/
theorem domain_eq : lifted.domain = retainedDomain := lifted.2.1.property

/-- The actual corner Point is its original one-time center acquisition. -/
theorem sample_eq : lifted.sample = ContinuedNeighborhood.Point.acquire lifted.neighborhood.patch _
    lifted.neighborhood.center_inside := lifted.2.2.2.2.2.1.property

/-- The actual corner Point Entry retains the original first Point's selected face sheet. -/
theorem corner_sheet : lifted.cornerEntry.sheet = acquired.entry.sheet := by
  let contained := Polynomial.Geometry.ClearPath.InBox.ofWithin lifted.route.path lifted.route.within firstInside
  let arrived := acquired.entry.followTrace lifted.traced contained
  have equal := congrArg Entry.sheet lifted.2.2.2.2.2.2.2.1.property
  have same := (arrived.followEquivalent_sheet lifted.equivalent).trans
    (acquired.entry.followTrace_sheet lifted.traced contained)
  exact equal.trans same

/-- The unchanged last physical Point lies on the SAME original face sheet through its actual crop lineage. -/
theorem last_sheet : lifted.lastEntry.sheet = acquired.entry.sheet := by
  have equal := congrArg Entry.sheet lifted.2.2.2.2.2.2.2.2.property
  exact equal.trans
    ((((acquired.entry.followJoin sourceJoin).followQueryCrop parent lower upper
      lowerInside upperInside moving vertices firstInside lastInside).followJoin_sheet
      targetJoin).trans
      (((acquired.entry.followJoin sourceJoin).followQueryCrop_sheet parent lower upper
        lowerInside upperInside moving vertices firstInside lastInside).trans
        (acquired.entry.followJoin_sheet sourceJoin)))

/-- The exact first-endpoint attachment consumer, retaining the original whole physical lift.

The remaining cache contract is the original PointData mesh-vertex
consumer on the same supplied first Point, acquisition and patch. Its
optional Point-indexed continuation forwards the original callback tail;
the default retains the same constant-result contract.
-/
@[expose] def FirstVertexConsumer
    {triangles : List (ModelTriangle lifted.domain.geometry)}
    (surface : OwnedTriangulation triangles)
    (vertex : VertexLookup surface.mesh.vertices (parent.point lower))
    (meshCount : Nat) (Result : Type u)
    (afterPoint : TracedPoint shared.models acquired.entry.sheet (parent.point lower)
      firstInside meshCount acquired.pointFrame → Type u := fun _ => Result) :=
  (kept : Lifted (parent := parent) (lower := lower) (upper := upper)
    (lowerInside := lowerInside) (upperInside := upperInside)
    (firstInside := firstInside) (lastInside := lastInside)
    shared geometry first last moving vertices sourceJoin targetJoin acquired retainedDomain count) →
  kept = lifted →
  PointData.MeshVertexConsumer (curve := curve) (models := shared.models)
    (geometry := lifted.domain.geometry) first firstInside acquired lifted.domain.patch surface vertex basis
    meshCount Result (afterPoint := afterPoint)

/-- Attach the original chord's first Point through the same retained PointData construction. -/
def withFirstMeshVertex
    {triangles : List (ModelTriangle lifted.domain.geometry)}
    (surface : OwnedTriangulation triangles)
    (vertex : VertexLookup surface.mesh.vertices (parent.point lower))
    (meshCount : Nat) {Result : Type u}
    (consume : FirstVertexConsumer lifted surface vertex meshCount Result) : Result :=
  PointData.withMeshVertex (curve := curve) (models := shared.models) (geometry := lifted.domain.geometry)
    first firstInside acquired lifted.domain.patch surface vertex basis meshCount (consume lifted rfl)

variable {differential : Differential genus} {index : Nat}
variable (data : DomainPrimitives lifted.domain differential index)

/-- Read three primitive values once on the GIVEN retained domain's original primitive bank.

The old anchors, offsets, primitive polynomials and constants are not
rebuilt. All three literal occurrences remain, even at coincident points.
-/
def readPrimitives : data.PointBank (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
    (ClearBoxPaths.Chord.coordinate_inside firstInside lastInside) :=
  data.readPoints (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
    (ClearBoxPaths.Chord.coordinate_inside firstInside lastInside)

variable {data lifted}
variable (observed : data.PointBank (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
  (ClearBoxPaths.Chord.coordinate_inside firstInside lastInside))

/-- Read one oriented increment from the SAME retained three primitive values. -/
def increment (edge : OrientedEdge 3) : Canonical :=
  observed.readings.values edge.finish - observed.readings.values edge.start

/-- Reversing a literal occurrence negates that same retained increment. -/
theorem increment_reverse (edge : OrientedEdge 3) : increment observed edge.reverse = -increment observed edge := by
  unfold increment
  rewrite [OrientedEdge.reverse_start, OrientedEdge.reverse_finish]
  ring1

/-- The entire actual triangle correction cancels on these SAME three primitive values. -/
theorem triangle_zero : SewingRetraction.faceValue ClearBoxPaths.Chord.faces (increment observed)
    ClearBoxPaths.Chord.incidence.correction = 0 := by
  rewrite [ClearBoxPaths.Chord.incidence_correction]
  change ((1 : Int) : Canonical) *
    SewingRetraction.wordValue (increment observed) (ClearBoxPaths.Chord.faces 0).boundary + 0 = 0
  rewrite [ClearBoxPaths.Chord.faces_zero]
  change ((1 : Int) : Canonical) *
    ((observed.readings.values 1 - observed.readings.values 0) +
      ((observed.readings.values 2 - observed.readings.values 1) +
        ((observed.readings.values 0 - observed.readings.values 2) + 0))) + 0 = 0
  ring1

/-- The physical chord increment equals its oriented axis route on the SAME retained primitive bank.

The actual geometric EdgeRoute supplies the full face correction, and
triangle_zero derives its cancellation. This compares these shared values;
it asserts no equality with independent physical primitive observations.
-/
theorem replacement : increment observed ⟨1, 2⟩ =
    SewingRetraction.wordValue (increment observed) ClearBoxPaths.Chord.incidence.path := by
  have actual := ClearBoxPaths.Chord.incidence.value_eq (increment observed) (increment_reverse observed)
  rewrite [triangle_zero observed, Basic.add_zero] at actual
  exact actual

/-- Compare an actual chord's retained triangle readings with one cell of its original numerator primitive bank.

The numerical bank may use any polynomial numerator on the same actual
face and sheet domain. Its primitives, anchors and offsets remain supplied
original caches. The finite comparison pays the endpoint cell discrepancy;
the two-leg route is the original signed chord incidence.
-/
def compareNumeratorCell {numerator : Polynomial}
    {bounds : PrimitiveOverlapBounds face.clearance numerator} {targetBound : Rational}
    (request : GridPrimitiveAccuracy bounds lifted.domain.steps targetBound)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (lifted.domain.patch.sheets.refine request.index).transitions
        (lifted.domain.patch.sheets.refine request.index).gauge) numerator)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (targetReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper)))
    (column row : Fin (lifted.domain.steps + 1))
    (firstCell : (lifted.domain.geometry.box column row).Contains (parent.point lower))
    (lastCell : (lifted.domain.geometry.box column row).Contains (parent.point upper)) :
    {fixed : PointReadings anchors offsets
        (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper)) //
      fixed = PointReadings.inCell anchors offsets column row
        (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
        (ClearBoxPaths.Chord.coordinate_inside firstCell lastCell) ∧
      Norm.Basic.normSq
        (((primitives.dense column row).value.eval (parent.point upper) -
          (primitives.dense column row).value.eval (parent.point lower)) -
            SewingRetraction.wordValue
              (fun edge : OrientedEdge 3 => targetReadings.values edge.finish - targetReadings.values edge.start)
              ClearBoxPaths.Chord.incidence.path) ≤ 16 * request.globalBound} :=
  RectangularPointReadings.Chord.compareCell
    (bank := lifted.domain.patch.models)
    (transitions := (lifted.domain.patch.sheets.refine request.index).transitions)
    (gauge := (lifted.domain.patch.sheets.refine request.index).gauge)
    request primitives anchors offsets targetReadings lifted.domain.patch.cell_refines
    column row firstCell lastCell

section Accuracy

variable {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
    {targetBound : Rational} (request : GridPrimitiveAccuracy bounds lifted.domain.steps targetBound)
    (targetData : DomainPrimitives lifted.domain differential request.index)
    (targetReadings : targetData.PointBank (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
      (ClearBoxPaths.Chord.coordinate_inside firstInside lastInside))

/-- Read one actual primitive cell at the chord slots and pay its comparison to the SAME retained triangle bank.

The returned numerical bank is constructed once on the original cell.
Its common offset cancels exactly inside the raw increment. The existing
same-data overlap comparison pays the two independently retained endpoint
locations. The original triangle replacement then supplies the exact
signed route, including its full correction and all repeated slots.
No physical Point, Entry, primitive polynomial or constant is replaced.
-/
def compareCell (column row : Fin (lifted.domain.steps + 1))
    (firstCell : (lifted.domain.geometry.box column row).Contains (parent.point lower))
    (lastCell : (lifted.domain.geometry.box column row).Contains (parent.point upper)) :
    {fixed : PointReadings targetData.anchors targetData.offsets
        (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper)) //
      fixed = PointReadings.inCell targetData.anchors targetData.offsets column row
        (ClearBoxPaths.Chord.coordinate (parent.point lower) (parent.point upper))
        (ClearBoxPaths.Chord.coordinate_inside firstCell lastCell) ∧
      Norm.Basic.normSq
        (((targetData.primitives.dense column row).value.eval (parent.point upper) -
          (targetData.primitives.dense column row).value.eval (parent.point lower)) -
            SewingRetraction.wordValue (increment targetReadings) ClearBoxPaths.Chord.incidence.path) ≤
        16 * request.globalBound} :=
  compareNumeratorCell (lifted := lifted) (numerator := differentialNumerator differential)
    request targetData.primitives targetData.anchors targetData.offsets targetReadings.readings
    column row firstCell lastCell

end Accuracy

end Lifted

/-- Acquire only the missing first interior Entry and retain the complete actual lift for its consumer.

The supplied endpoint Points, original moving crop, joins and geometry
remain whole caches. The original selected domain is forced once and
forwarded with the acquisition and lift. Existing domains instead use
ofAcquired directly; no Point, query or source preparation is replayed.
-/
def withLift {Result : Type u}
    (consume : (actual : Acquisition shared.models firstInside first.sample.owner) →
      (domain : PeriodDomain shared.models actual.entry.sheet) →
      Lifted (parent := parent) (lower := lower) (upper := upper)
        (lowerInside := lowerInside) (upperInside := upperInside)
        (firstInside := firstInside) (lastInside := lastInside)
        shared geometry first last moving vertices sourceJoin targetJoin actual domain count → Result) : Result :=
  let actual := Acquisition.build shared.models firstInside first.sample.owner
  let domain := shared.domain actual.entry.sheet
  let lifted := ofAcquired (parent := parent) (lower := lower) (upper := upper)
    (lowerInside := lowerInside) (upperInside := upperInside)
    (firstInside := firstInside) (lastInside := lastInside)
    shared geometry first last moving vertices sourceJoin targetJoin actual domain count
  consume actual domain lifted

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Chord

end
