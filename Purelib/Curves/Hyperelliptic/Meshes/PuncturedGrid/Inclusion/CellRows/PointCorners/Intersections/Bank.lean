module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Intersections.Readings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Bank.Sources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Bank.Paths

/-! # Actual strict-cut source segments in two retained primitive domains

The first strict cut supplies its already materialized TracedPoint. Two
independent old primitive-reading banks supply the literal five-slot
endpoint positions. The original clear axis segment is a geometry input;
no arbitrary diagonal is replaced by an L-route. One common subdivision
and one source-bank acquisition are retained before packing AtSegment.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)

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

variable (firstAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 0).finish))
variable (lastAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 1).finish))
variable (count : Nat)
variable (strict : Σ _ : {_value : Unit // crossing.time 0 < 1},
  {value : lifted.PreparedSide crossing position factory 0 count //
    value = lifted.prepareSide crossing position factory 0 count})
variable (last : lifted.Resolved crossing position factory 1 lastAvailable count)

namespace SourceBank.PrimitiveReadings

variable (cached : lifted.SourceBank crossing position factory firstAvailable lastAvailable count (Sum.inl strict) last)
variable {leftDomain rightDomain : PeriodDomain models classified.entry.sheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable (leftReadings : cached.PrimitiveReadings leftData)
variable (rightReadings : cached.PrimitiveReadings rightData)
variable (finish : Fin 5)
variable (source : ClearSegment curve.polynomial face.cell.box (crossing.point 0) (crossing.coordinate finish))
variable (request : AccuracyRequest)

/-- Retain both old banks, the actual strict result, original segment and the three new whole factory results.

Only the existing tuple/subtype containers are used. The result preserves
independent old primitives, anchors, offsets and boundary-tie reading
owners. The source-bank acquisition contains genuinely new joins and
child preparations; it does not repeat the strict Point acquisition.
-/
@[expose] def FirstStrictSegment :=
  {value : cached.PrimitiveReadings leftData × cached.PrimitiveReadings rightData //
    value = (leftReadings, rightReadings)} ×
  {value : lifted.Resolved crossing position factory 0 firstAvailable count // value = Sum.inl strict} ×
  {value : ClearSegment curve.polynomial face.cell.box (crossing.point 0) (crossing.coordinate finish) //
    value = source} ×
  (Σ divided : {value : Subdivision leftData rightData source leftReadings.readings rightReadings.readings
      1 finish 1 finish crossing.coordinate_one rfl crossing.coordinate_one rfl //
    value = Subdivision.build leftData rightData source leftReadings.readings rightReadings.readings
      1 finish 1 finish crossing.coordinate_one rfl crossing.coordinate_one rfl},
  Σ acquired : {value : Subdivision.Bank.TracedSource strict.2.val.prepared divided.val request //
    value = Subdivision.Bank.acquireTracedSource strict.2.val.prepared divided.val request},
  {value : Subdivision.Bank.AtSegment leftReadings.readings rightReadings.readings source 1 finish 1 finish //
    value = Subdivision.Bank.AtSegment.ofAcquisition
      (leftOld := leftReadings.readings) (rightOld := rightReadings.readings) (segment := source)
      crossing.coordinate_one rfl crossing.coordinate_one rfl
      (Subdivision.Bank.pointData strict.2.val.prepared) (Subdivision.Bank.pointData strict.2.val.prepared)
      strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
      strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
      acquired.val.joined divided.val request acquired.val.acquisition})

/-- Build the common subdivision and one original source bank, then pack the SAME acquisition at the actual slots.

The old reading banks and original strict/cache/segment inputs are only
retained. The initial source join is genuinely new work with its own
root-expression observation boundary; no primitive constants are equated.
Reverse or stationary source segments remain distinct original inputs.
-/
def firstStrictSegment : FirstStrictSegment lifted crossing position factory firstAvailable lastAvailable count
    strict last cached leftReadings rightReadings finish source request :=
  let divided := Subdivision.build leftData rightData source leftReadings.readings rightReadings.readings
    1 finish 1 finish crossing.coordinate_one rfl crossing.coordinate_one rfl
  let acquired := Subdivision.Bank.acquireTracedSource strict.2.val.prepared divided request
  let segment := Subdivision.Bank.AtSegment.ofAcquisition
    (leftOld := leftReadings.readings) (rightOld := rightReadings.readings) (segment := source)
    crossing.coordinate_one rfl crossing.coordinate_one rfl
    (Subdivision.Bank.pointData strict.2.val.prepared) (Subdivision.Bank.pointData strict.2.val.prepared)
    strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
    strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
    acquired.joined divided request acquired.acquisition
  (⟨(leftReadings, rightReadings), rfl⟩,
    ⟨cached.resolved.1, congrArg Prod.fst cached.resolved_eq⟩, ⟨source, rfl⟩,
    ⟨⟨divided, rfl⟩, ⟨acquired, rfl⟩, ⟨segment, rfl⟩⟩)

namespace FirstStrictSegment

variable (stored : FirstStrictSegment lifted crossing position factory firstAvailable lastAvailable count
  strict last cached leftReadings rightReadings finish source request)

/-- Read both complete original primitive-reading caches without rebuilding either old bank. -/
def originals : cached.PrimitiveReadings leftData × cached.PrimitiveReadings rightData := stored.1.val

/-- The two complete independent old reading caches are unchanged. -/
theorem originals_eq : stored.originals = (leftReadings, rightReadings) := stored.1.property

/-- Read the actual retained strict result from the old source-bank cache. -/
def resolved : lifted.Resolved crossing position factory 0 firstAvailable count := stored.2.1.val

/-- The old source bank's actual resolved result is the SAME strict payload used by this acquisition. -/
theorem resolved_eq : stored.resolved = Sum.inl strict := stored.2.1.property

/-- Read the SAME original oriented clear axis segment. -/
def originalSegment : ClearSegment curve.polynomial face.cell.box
    (crossing.point 0) (crossing.coordinate finish) := stored.2.2.1.val

/-- The whole original segment is retained, including its endpoint order and line clearance. -/
theorem originalSegment_eq : stored.originalSegment = source := stored.2.2.1.property

/-- Read the once-built common subdivision with both independent domain outcomes and reading vectors. -/
abbrev subdivision : Subdivision leftData rightData source leftReadings.readings rightReadings.readings
    1 finish 1 finish crossing.coordinate_one rfl crossing.coordinate_one rfl := stored.2.2.2.1.val

/-- The whole common subdivision retains its original factory on these actual four endpoint positions. -/
theorem subdivision_eq : stored.subdivision =
    Subdivision.build leftData rightData source leftReadings.readings rightReadings.readings
      1 finish 1 finish crossing.coordinate_one rfl crossing.coordinate_one rfl := stored.2.2.2.1.property

/-- Original endpoint owners discharge the two-domain geometric coverage requests internally. -/
theorem coverage_requests_nil : stored.subdivision.common.requests = [] := stored.subdivision.requests_nil

/-- Read the actual once-built source acquisition with its literal old strict Point and newly retained join. -/
abbrev acquired : Subdivision.Bank.TracedSource strict.2.val.prepared stored.subdivision request :=
  stored.2.2.2.2.1.val

/-- The complete acquisition retains its original source factory on the SAME stored subdivision. -/
theorem acquired_eq : stored.acquired =
    Subdivision.Bank.acquireTracedSource strict.2.val.prepared stored.subdivision request := stored.2.2.2.2.1.property

/-- Read the complete AtSegment consuming that SAME retained acquisition and both original reading banks. -/
abbrev segment : Subdivision.Bank.AtSegment leftReadings.readings rightReadings.readings source 1 finish 1 finish :=
  stored.2.2.2.2.2.val

/-- The whole AtSegment is exactly the original packer on the SAME retained Point, join and acquisition. -/
theorem segment_eq : stored.segment = Subdivision.Bank.AtSegment.ofAcquisition
    (leftOld := leftReadings.readings) (rightOld := rightReadings.readings) (segment := source)
    crossing.coordinate_one rfl crossing.coordinate_one rfl
    (Subdivision.Bank.pointData strict.2.val.prepared) (Subdivision.Bank.pointData strict.2.val.prepared)
    strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
    strict.2.val.prepared.entry strict.2.val.prepared.entry_sheet
    stored.acquired.joined stored.subdivision request stored.acquired.acquisition := stored.2.2.2.2.2.property

/-- The source acquisition retains the whole SAME original strict TracedPoint. -/
theorem pointCache_eq : stored.acquired.original = strict.2.val.prepared := stored.acquired.original_eq

/-- The actual source-segment increment is paid by its original finite child comparison bank. -/
theorem increment_le : Norm.Basic.normSq stored.segment.increment ≤ stored.segment.charge :=
  stored.segment.increment_le

/-- Both independent old primitive increments use exactly the signed source-slot endpoint occurrences. -/
theorem increment_eq : stored.segment.increment =
    leftReadings.increment ⟨1, finish⟩ - rightReadings.increment ⟨1, finish⟩ :=
  (Subdivision.Bank.AtSegment.increment_eq stored.segment).trans
    (congrArg₂ (fun left right : Canonical => left - right)
      (SourceBank.PrimitiveReadings.increment_eq leftReadings ⟨1, finish⟩).symm
      (SourceBank.PrimitiveReadings.increment_eq rightReadings ⟨1, finish⟩).symm)

/-- The actual two independent old signed source increments satisfy the retained finite common-child allowance. -/
theorem source_increment_le : Norm.Basic.normSq
    (leftReadings.increment ⟨1, finish⟩ - rightReadings.increment ⟨1, finish⟩) ≤ stored.segment.charge :=
  Eq.mp (congrArg (fun value : Canonical => Norm.Basic.normSq value ≤ stored.segment.charge) stored.increment_eq)
    stored.increment_le

end FirstStrictSegment

end SourceBank.PrimitiveReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
