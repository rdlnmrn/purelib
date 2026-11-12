module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Intersections.Sides
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Strict/unit results on the actual first and second cut occurrences

Successful results retain their full actual Point/Entry/connection work.
A missing old endpoint remains a typed request with the original attempted
Option and count. The original endpoint is never silently reacquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

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

variable (side : Fin 2)
variable (available : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) side).finish))

/-- Retain the actual old endpoint Point, its pure transport, and its SAME cached signed selection. -/
abbrev EndpointAt (atEnd : crossing.time side = 1) :=
  Σ original : {value : retained.VertexPoint models vertices
      (apex.edge (lifted.cell.quad.faces position) side).finish // available = some value},
  Σ sample : {value : ContinuedNeighborhood.Point original.val.neighborhood (crossing.point side) //
    value = original.val.atPoint (lifted.cut_endpoint crossing position factory side atEnd)},
  {value : NamedEquivalent
      (ownerName (vertices.owner retained.localFrames (apex.edge (lifted.cell.quad.faces position) side).finish))
      (ownerName sample.val.owner) //
    value = NamedEquivalent.transport rfl
      (congrArg (fun value : ContinuedNeighborhood.Point original.val.neighborhood (crossing.point side) =>
        ownerName value.owner) sample.property).symm
      (original.val.atPointEquivalent (lifted.cut_endpoint crossing position factory side atEnd))}

/-- Reuse one supplied endpoint execution without new frame, Point, selector, trace or join work.

The comparison is indexed by the same Point readback stored in the result;
its original selector and numerical observations remain retained.
-/
def reuseAt (atEnd : crossing.time side = 1)
    (original : retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) side).finish)
    (found : available = some original) : lifted.EndpointAt crossing position factory side available atEnd :=
  let sample := original.atPoint (lifted.cut_endpoint crossing position factory side atEnd)
  let sampleEq : sample = original.atPoint (lifted.cut_endpoint crossing position factory side atEnd) := rfl
  let equivalent := NamedEquivalent.transport rfl
    (congrArg (fun value : ContinuedNeighborhood.Point original.neighborhood (crossing.point side) =>
      ownerName value.owner) sampleEq).symm
    (original.atPointEquivalent (lifted.cut_endpoint crossing position factory side atEnd))
  ⟨⟨original, found⟩, ⟨sample, sampleEq⟩, ⟨equivalent, rfl⟩⟩

/-- The precise unresolved unit-cut input at this literal original signed endpoint.

The whole original quad/cut and attempted count/cache are retained. This
request asserts absence of supplied preparation, not invalid geometry or
a global impossibility. An actual VertexPoint resolves it directly.
-/
abbrev MissingAt (count : Nat) :=
  {value : classified.CellLift located vertices × AffineCut.CrossingCache lineFirst lineLast triangle apex //
    value = (lifted, crossing)} × {_value : Unit // crossing.time side = 1} ×
  {value : Nat // value = count} ×
  {value : Option
      (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) side).finish) //
    value = available ∧ value = none}

/-- A successful cut retains either complete new strict work or its complete old endpoint cache.

No signed relation is a constructor premise. The strict factory consumes
the actual retained corner Entries; endpoint reuse consumes an original
PointEntry and its actual cached selector.
-/
abbrev Resolved (count : Nat) :=
  (Σ _ : {_value : Unit // crossing.time side < 1},
    {value : lifted.PreparedSide crossing position factory side count //
      value = lifted.prepareSide crossing position factory side count}) ⊕
  (Σ atEnd : {_value : Unit // crossing.time side = 1},
    lifted.EndpointAt crossing position factory side available atEnd.property)

/-- Execute the actual strict/unit branch once on either source-side occurrence.

Only strict fractions acquire new work. Unit fractions consume the actual
supplied cache or return its precise missing-data request. Original side
orientation and both old source Owners are preserved in every result.
-/
def attemptSide (count : Nat) : lifted.Resolved crossing position factory side available count ⊕
    lifted.MissingAt crossing position side available count :=
  match crossing.pointCase side with
  | .inl strict =>
      let prepared := lifted.prepareSide crossing position factory side count
      .inl (.inl ⟨strict, ⟨prepared, rfl⟩⟩)
  | .inr atEnd =>
      match available with
      | some original => .inl (.inr ⟨atEnd,
          lifted.reuseAt crossing position factory side (some original) atEnd.property original rfl⟩)
      | none => .inr (⟨(lifted, crossing), rfl⟩, atEnd, ⟨count, rfl⟩, ⟨none, rfl, rfl⟩)

/-- Retain both complete attempts, in first-cut then second-cut order, with their whole factory equations.

Repeated coordinates do not merge these two original occurrences. A later
neighbor consumer reuses a resolved value through exact indexed edge
identity; it does not call attemptSide again to recover its cache.
-/
def attemptBoth (firstAvailable : Option
    (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 0).finish))
    (lastAvailable : Option
      (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 1).finish))
    (count : Nat) :
    {value : lifted.Resolved crossing position factory 0 firstAvailable count ⊕
        lifted.MissingAt crossing position 0 firstAvailable count //
      value = lifted.attemptSide crossing position factory 0 firstAvailable count} ×
    {value : lifted.Resolved crossing position factory 1 lastAvailable count ⊕
        lifted.MissingAt crossing position 1 lastAvailable count //
      value = lifted.attemptSide crossing position factory 1 lastAvailable count} :=
  let first := lifted.attemptSide crossing position factory 0 firstAvailable count
  let last := lifted.attemptSide crossing position factory 1 lastAvailable count
  (⟨first, rfl⟩, ⟨last, rfl⟩)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
