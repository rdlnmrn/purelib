module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Approximation.Gaussian.Equivalence

/-! # Existing Point caches at literal signed vertex occurrences

The original PointEntry is retained whole at its original nominal point.
Its actual stored selection identifies one literal signed bank index.
Reading the Point at a cut endpoint only reindexes this SAME cache; it
performs no Point, frame, query, row, selection or join acquisition.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} (retained : CellRows old face coarse cuts)
variable (models : FaceModels frames face) (vertices : VertexBank retained.grid) (index : Fin vertices.count)

/-- Retain an original Point/classification cache at one actual signed bank index.

The index law refers to the actual stored selector result. No operational
root relation is accepted as a constructor argument. The original point,
stem, member, count and continued neighborhood remain nominal inputs.
-/
abbrev VertexPoint :=
  Σ vertex : {point : Canonical // FromStates.ContainsVertex retained.grid point},
  Σ count : Nat, Σ neighborhood : ContinuedNeighborhood curve.polynomial count,
  Σ sample : ContinuedNeighborhood.Point neighborhood vertex.val,
  Σ stem : Walks.Walk retained.grid face.cell.box.anchor vertex.val,
  {classified : retained.PointEntry models stem vertex.property sample //
    vertices.index vertex.val vertex.property classified.selected.index = index}

namespace VertexPoint

variable {retained models vertices index} (cached : retained.VertexPoint models vertices index)

/-- Read the exact original nominal point. -/
@[expose] def point : Canonical := cached.1.val

/-- Read its original grid membership. -/
theorem member : FromStates.ContainsVertex retained.grid cached.point := cached.1.property

/-- Read the original neighborhood's numerical count, without upgrading it. -/
@[expose] def count : Nat := cached.2.1

/-- Read the whole original continued neighborhood. -/
@[expose] def neighborhood : ContinuedNeighborhood curve.polynomial cached.count := cached.2.2.1

/-- Read the whole original Point, including its actual Owner and cached parameter norm. -/
@[expose] def sample : ContinuedNeighborhood.Point cached.neighborhood cached.point := cached.2.2.2.1

/-- Read the literal old ordered stem, preserving repeats and stationary branches. -/
@[expose] def stem : Walks.Walk retained.grid face.cell.box.anchor cached.point := cached.2.2.2.2.1

/-- Read the entire old PointEntry, including its original selection and Entry. -/
def classified : retained.PointEntry models cached.stem cached.member cached.sample := cached.2.2.2.2.2.val

/-- The actual old selector reads the literal requested signed vertex. -/
theorem index_eq : vertices.index cached.point cached.member cached.classified.selected.index = index :=
  cached.2.2.2.2.2.property

/-- The actual bank coordinate is the same original Point coordinate. -/
theorem point_eq : vertices.coordinate index = cached.point :=
  (congrArg vertices.coordinate cached.index_eq).symm.trans
    (vertices.coordinate_index cached.point cached.member cached.classified.selected.index)

/-- The actual cached selection compares the indexed bank Owner to the original Point Owner.

Both original Owners remain. The relation comes from the SAME retained
PointEntry selection and its literal index law, never coordinate equality.
-/
def equivalent : NamedEquivalent (ownerName (vertices.owner retained.localFrames index))
    (ownerName cached.sample.owner) :=
  NamedEquivalent.transport
    (congrArg (fun value => ownerName (vertices.owner retained.localFrames value)) cached.index_eq) rfl
    (cached.classified.selected_equivalent vertices).symm

/-- Reindex the SAME retained Point to an actual cut endpoint with this literal signed index. -/
def atPoint {point : Canonical} (same : point = vertices.coordinate index) :
    ContinuedNeighborhood.Point cached.neighborhood point :=
  ContinuedNeighborhood.Point.castPoint (same.trans cached.point_eq) cached.sample

/-- Endpoint reading uses the whole original point transport, not another acquisition. -/
theorem atPoint_eq {point : Canonical} (same : point = vertices.coordinate index) :
    cached.atPoint same = ContinuedNeighborhood.Point.castPoint (same.trans cached.point_eq) cached.sample := by rfl

/-- The endpoint-reindexed Point retains its original root name. -/
theorem atPoint_name {point : Canonical} (same : point = vertices.coordinate index) :
    (cached.atPoint same).certificate.value.name = cached.sample.certificate.value.name :=
  ContinuedNeighborhood.Point.castPoint_name (same.trans cached.point_eq) cached.sample

/-- Carry the SAME retained selector comparison to the endpoint-reindexed Point. -/
def atPointEquivalent {point : Canonical} (same : point = vertices.coordinate index) :
    NamedEquivalent (ownerName (vertices.owner retained.localFrames index))
      (ownerName (cached.atPoint same).owner) :=
  NamedEquivalent.transport rfl (cached.atPoint_name same).symm cached.equivalent

/-- Transport the original selector through the SAME Point factory and equality of the whole target frame.

The coordinate equation only reindexes the old Point and old frame. The
complete Point factory and frame equation are required; another Owner at
this coordinate cannot be substituted. No classification executes here.
-/
def selectionAt {next : Canonical} (same : next = cached.point)
    (target : OwnerFrame (curve.polynomial.eval next))
    (frameEq : target = RootFrames.RootFrameEntry.frameAt
      ⟨cached.point, retained.localFrames.frameAt cached.point cached.member⟩ next same.symm)
    (sample : ContinuedNeighborhood.Point cached.neighborhood next)
    (sampleEq : sample = ContinuedNeighborhood.Point.castPoint same cached.sample) :
    OwnerSelection target.owners sample.owner := by
  cases same
  cases sampleEq
  cases frameEq
  exact cached.classified.selected

/-- Whole-frame and whole-Point reindexing preserve this SAME complete original selected value. -/
theorem selectionAt_heq {next : Canonical} (same : next = cached.point)
    (target : OwnerFrame (curve.polynomial.eval next))
    (frameEq : target = RootFrames.RootFrameEntry.frameAt
      ⟨cached.point, retained.localFrames.frameAt cached.point cached.member⟩ next same.symm)
    (sample : ContinuedNeighborhood.Point cached.neighborhood next)
    (sampleEq : sample = ContinuedNeighborhood.Point.castPoint same cached.sample) :
    HEq (cached.selectionAt same target frameEq sample sampleEq) cached.classified.selected := by
  cases same
  cases sampleEq
  cases frameEq
  rfl

end VertexPoint

namespace PointEntry.CellLift

variable {retained models vertices} {point : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor point}
variable {member : FromStates.ContainsVertex retained.grid point}
variable {count : Nat} {neighborhood : ContinuedNeighborhood curve.polynomial count}
variable {sample : ContinuedNeighborhood.Point neighborhood point}
variable {classified : retained.PointEntry models stem member sample}
variable {located : ClearGrid.CornerLocation retained.grid point}
variable (lifted : classified.CellLift located vertices) (index : Fin vertices.count)
variable (incidence : lifted.cell.quad.corner lifted.corner = index)

/-- Retain an EXISTING corner PointEntry at its actual signed bank occurrence.

The original corner-index theorem derives the index law from the actual
prefix/inverse row maps and stored selection. The supplied incidence is
literal signed-index equality; it is not a root comparison premise.
-/
@[expose] def vertexPoint : retained.VertexPoint models vertices index :=
  ⟨⟨point, member⟩, count, neighborhood, sample, stem,
    ⟨lifted.original, lifted.corner_index.symm.trans incidence⟩⟩

/-- The retained endpoint cache keeps the complete original PointEntry unchanged. -/
theorem vertexPoint_classified : (lifted.vertexPoint index incidence).classified = lifted.original := by rfl

/-- The retained endpoint cache keeps the complete original Point unchanged. -/
theorem vertexPoint_sample : (lifted.vertexPoint index incidence).sample = sample := by rfl

end PointEntry.CellLift

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

end
