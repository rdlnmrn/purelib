module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Intersections.Sources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Points
import Purelib.Tactic.Ring
import Purelib.Topology.Mesh.TriangleCut
public import Purelib.Topology.Mesh.TriangleCut.Routes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

/-! # Retained analytic readings at the actual five signed cut-source slots

Both complete cut Point/Entry caches and the original primitive bank are
retained. One finite location/evaluation bank reads all five literal slots.
Its internal primitive cancellation uses these SAME cached values; old
mesh readings and independent primitive constants stay separate inputs.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} {retained : CellRows old face coarse cuts}
variable {models : FaceModels frames face} {base : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor base}
variable {member : FromStates.ContainsVertex retained.grid base}
variable {oldCount : Nat} {oldNeighborhood : ContinuedNeighborhood curve.polynomial oldCount}
variable {oldSample : ContinuedNeighborhood.Point oldNeighborhood base}
variable {classified : retained.PointEntry models stem member oldSample}
variable {located : ClearGrid.CornerLocation retained.grid base} {vertices : VertexBank retained.grid}
variable (lifted : classified.CellLift located vertices)

variable {lineFirst lineLast : Canonical} {triangle : CoordinateTriangle}
variable {apex : AffineCut.Apex lineFirst lineLast triangle}
variable (crossing : AffineCut.CrossingCache lineFirst lineLast triangle apex) (position : Fin 2)
variable (factory : triangle =
  ⟨vertices.coordinate (lifted.cell.quad.faces position).first,
    vertices.coordinate (lifted.cell.quad.faces position).second,
    vertices.coordinate (lifted.cell.quad.faces position).third⟩)

section

include lifted factory

/-- The literal five coordinate slots lie in the SAME actual original regular face.

The three corner incidences are read through the original indexed fine
triangle. The two intermediate incidences use the actual retained cut
fractions; no root or Entry equality is inferred from these inequalities.
-/
theorem source_inside (slot : Fin 5) : face.cell.box.Contains (crossing.coordinate slot) := by
  have corners (corner : Fin 3) : face.cell.box.Contains (AffineCut.corner crossing.original corner) :=
    Eq.mpr (congrArg face.cell.box.Contains
      (crossing.original_corner vertices.coordinate (lifted.cell.quad.faces position) factory corner))
      (vertices.coordinate_onGrid (SewnPrimitiveFaces.corner (lifted.cell.quad.faces position)
        (AffineCut.cornerIndex apex.1 corner))).inside
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))))) slot
  · exact Eq.mpr (congrArg face.cell.box.Contains crossing.coordinate_zero)
      (Eq.mp (congrArg face.cell.box.Contains (AffineCut.corner_zero crossing.original)) (corners 0))
  · exact Eq.mpr (congrArg face.cell.box.Contains crossing.coordinate_one)
      (lifted.cut_inside crossing position factory 0)
  · exact Eq.mpr (congrArg face.cell.box.Contains crossing.coordinate_two)
      (Eq.mp (congrArg face.cell.box.Contains (AffineCut.corner_one crossing.original)) (corners 1))
  · exact Eq.mpr (congrArg face.cell.box.Contains crossing.coordinate_three)
      (Eq.mp (congrArg face.cell.box.Contains (AffineCut.corner_two crossing.original)) (corners 2))
  · exact Eq.mpr (congrArg face.cell.box.Contains crossing.coordinate_four)
      (lifted.cut_inside crossing position factory 1)

end

variable (firstAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 0).finish))
variable (lastAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 1).finish))
variable (count : Nat)
variable (first : lifted.Resolved crossing position factory 0 firstAvailable count)
variable (last : lifted.Resolved crossing position factory 1 lastAvailable count)

namespace SourceBank

variable {lifted crossing position factory firstAvailable lastAvailable count first last}
variable (cached : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last)

section Core

variable {domain : PeriodDomain models classified.entry.sheet} {differential : Differential genus} {index : Nat}
variable (data : DomainPrimitives domain differential index)

/-- Retain the complete actual signed cut-source cache, old primitives and genuinely new finite numerical readings.

Both strict/unit Point caches remain in the original SourceBank. The old
four-corner readings, polynomials, anchors and offsets remain the exact
supplied DomainPrimitives. Only new locations and values are materialized.
-/
abbrev PrimitiveReadings :=
  {value : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last //
    value = cached} ×
  {value : DomainPrimitives domain differential index // value = data} ×
  {value : data.PointBank crossing.coordinate (lifted.source_inside crossing position factory) //
    value = data.readPoints crossing.coordinate (lifted.source_inside crossing position factory)}

/-- Locate and evaluate the actual five retained source occurrences once on their SAME old-sheet primitive data. -/
def readPrimitives : cached.PrimitiveReadings data :=
  let observed := data.readPoints crossing.coordinate (lifted.source_inside crossing position factory)
  (⟨cached, rfl⟩, ⟨data, rfl⟩, ⟨observed, rfl⟩)

namespace PrimitiveReadings

variable {cached data} (observed : cached.PrimitiveReadings data)

/-- Read the whole actual source/Point/Entry bank without replaying a resolution or preparation. -/
def original : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last :=
  observed.1.val

/-- Read the whole old primitive bank, preserving every original constant and old corner reading. -/
def primitives : DomainPrimitives domain differential index := observed.2.1.val

/-- Read the one actual new location/evaluation cache at the literal five slots. -/
def numerical : data.PointBank crossing.coordinate (lifted.source_inside crossing position factory) := observed.2.2.val

/-- Read the original numerical PointReadings carrying the actual selected cell owners and values. -/
def readings : PointReadings data.anchors data.offsets crossing.coordinate := observed.numerical.readings

/-- The source/Point/Entry bank remains the SAME whole original execution result. -/
theorem original_eq : observed.original = cached := observed.1.property

/-- The entire old primitive bank, including old corner values, is retained literally. -/
theorem primitives_eq : observed.primitives = data := observed.2.1.property

/-- The new numerical bank has the complete original finite location/evaluation factory. -/
theorem numerical_eq : observed.numerical =
    data.readPoints crossing.coordinate (lifted.source_inside crossing position factory) := observed.2.2.property

/-- Read the actual old-face Entry of this same original signed source-slot Owner. -/
def entry (slot : Fin 5) : Entry models (crossing.coordinate slot) (observed.original.vertex slot).1 :=
  (observed.original.vertex slot).2.val

/-- Every literal signed source occurrence uses the sheet of the actual supplied primitive domain. -/
theorem entry_sheet (slot : Fin 5) : (observed.entry slot).sheet = classified.entry.sheet :=
  (observed.original.vertex slot).2.property

/-- Compute one oriented primitive increment using the SAME cached values at the actual cut-word slots. -/
def increment (edge : OrientedEdge 5) : Canonical :=
  observed.readings.values edge.finish - observed.readings.values edge.start

/-- The oriented increment reads its two literal cached source-slot observations. -/
theorem increment_eq (edge : OrientedEdge 5) : observed.increment edge =
    observed.readings.values edge.finish - observed.readings.values edge.start := by rfl

/-- Reversing an indexed occurrence reverses its actual cached primitive increment. -/
theorem increment_reverse (edge : OrientedEdge 5) : observed.increment edge.reverse = -observed.increment edge := by
  unfold increment
  rewrite [OrientedEdge.reverse_start, OrientedEdge.reverse_finish]
  ring1

/-- The actual two child-seam occurrences have opposite increments in this SAME retained numerical bank.

This is an exact cancellation of cached primitive differences. It does
not identify independently prepared paths, observations or primitive data
on the second old face.
-/
theorem seam_increments (seam : Fin 2) :
    observed.increment ((TriangleCut.seamSources seam).2.project TriangleCut.faces) =
      -observed.increment ((TriangleCut.seamSources seam).1.project TriangleCut.faces) :=
  (congrArg observed.increment (TriangleCut.seamSources_opposite seam)).trans
    (observed.increment_reverse _)

/-- The first side's two literal partial occurrences telescope through the SAME retained cut reading. -/
theorem first_side : observed.increment ⟨0, 1⟩ + observed.increment ⟨1, 2⟩ =
    observed.readings.values 2 - observed.readings.values 0 := by
  unfold increment
  ring1

/-- The last side retains its literal reverse orientation and the SAME trailing cut reading. -/
theorem last_side : observed.increment ⟨3, 4⟩ + observed.increment ⟨4, 0⟩ =
    observed.readings.values 0 - observed.readings.values 3 := by
  unfold increment
  ring1

/-- The retained first-child face correction cancels on the same five cached primitive values. -/
private theorem packaged_chord_face_zero :
    SewingRetraction.faceValue TriangleCut.faces observed.increment TriangleCut.chordRoute.correction = 0 := by
  rewrite [TriangleCut.chordRoute_correction]
  change ((1 : Int) : Canonical) *
    SewingRetraction.wordValue observed.increment (TriangleCut.faces 0).boundary + 0 = 0
  rewrite [TriangleCut.faces_zero]
  change ((1 : Int) : Canonical) *
    (observed.increment ⟨0, 1⟩ +
      (observed.increment ⟨1, 4⟩ + (observed.increment ⟨4, 0⟩ + 0))) + 0 = 0
  unfold increment
  ring1

/-- The retained first-child face correction cancels on the same five cached primitive values. -/
theorem chord_face_zero :
    SewingRetraction.faceValue TriangleCut.faces observed.increment TriangleCut.chordRoute.correction = 0 :=
  packaged_chord_face_zero observed

/-- The actual cut-chord increment equals the supported apex route in this same retained reading bank.

The indexed EdgeRoute supplies the complete oriented face correction.
Its cancellation is derived from these same cached values, preserving the
actual signed cut-source owners and their original primitive domain.
This does not compare an independent physical crop or old primitive bank.
-/
theorem chord_replacement : observed.increment ⟨1, 4⟩ =
    SewingRetraction.wordValue observed.increment TriangleCut.chordRoute.path := by
  have retained := TriangleCut.chordRoute.value_eq observed.increment observed.increment_reverse
  rewrite [observed.chord_face_zero, Basic.add_zero] at retained
  exact retained

end PrimitiveReadings

end Core

section Accuracy

variable {domain : PeriodDomain models classified.entry.sheet} {differential : Differential genus}
variable {bounds : PrimitiveOverlapBounds face.clearance (differentialNumerator differential)}
variable {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
variable {data : DomainPrimitives domain differential request.index}
variable (observed : cached.PrimitiveReadings data)

/-- The actual source-slot increment compares to another retained same-data increment with paid endpoint jumps.

The two original point incidences are required. They establish only the
analytic endpoint locations, while the source Point/Entry owners remain
in the same complete SourceBank and are never equated to numerical owners.
-/
theorem PrimitiveReadings.increment_le {otherCount : Nat} {otherPoints : Fin otherCount → Canonical}
    (other : PointReadings data.anchors data.offsets otherPoints) (edge : OrientedEdge 5)
    (first last : Fin otherCount) (firstEq : crossing.coordinate edge.start = otherPoints first)
    (lastEq : crossing.coordinate edge.finish = otherPoints last) :
    Norm.Basic.normSq (observed.increment edge - (other.values last - other.values first)) ≤
      16 * request.globalBound :=
  DomainPrimitives.PointBank.increment_le request observed.numerical other edge.start edge.finish
    first last firstEq lastEq

end Accuracy

end SourceBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
