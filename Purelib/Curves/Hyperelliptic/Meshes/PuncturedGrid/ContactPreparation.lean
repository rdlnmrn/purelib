module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DiagonalContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# Total preparation of every positive lifted-grid contact

Diagonal contacts reuse exact corner cancellation. Side contacts retain one
covered segment, seeded by the existing vertex owner, for both face entries.
Generated preparations may supply those same checked caches directly; the
default producer requires no cover or successful-search premise.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}

set_option genInjectivity false in
/-- The two constructors retain the actual geometric reason for accuracy:
exact cancellation, or one common prepared path with checked face entries. -/
inductive ContactPreparation (contact : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact
  mesh.triangulation.faces)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) where
  /-- Retain the original located diagonal contact whose opposite corner increments cancel exactly. -/ | diagonal
    (located : Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact)
      (kind : located.left.kind = .upDiagonal ∨ located.left.kind = .downDiagonal)
  /-- Retain one original covered side segment and both actual entered-face comparisons. -/ | segment (located :
    Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact) {ambient :
    Rational.Box}
      {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient
        (vertices.coordinate (contact.left.project mesh.triangulation.faces).start)
        (vertices.coordinate (contact.left.project mesh.triangulation.faces).finish)}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval (vertices.coordinate
        (contact.left.project mesh.triangulation.faces).start))}
      (piece : Paths.PreparedPathDecomposition.CoveredSegment segment owner) (parentSheet : Fin 2)
      (compared : Hyperelliptic.Meshes.PuncturedGrid.SegmentContactRequests.SegmentContact (located.firstPlacement
        segment) (located.lastPlacement segment) piece differential parentSheet domains)

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity ContactPreparation

namespace ContactPreparation

variable {contact : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces} {differential
  : Hyperelliptic.Differentials.Basic.Differential genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}

/-- Transport the original clear segment and ambient containment along exact endpoint equalities. -/
@[expose] public def atEndpoints {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient :
  Rational.Box}
    {first last start finish : Gaussian.Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      first last)
    (within : segment.WithinAmbient) (startEq : first = start) (finishEq : last = finish) :
    {result : Geometry.ClearPath.ClearSegment polynomial ambient start finish // result.WithinAmbient} := by
  cases startEq
  cases finishEq
  exact ⟨segment, within⟩

/-- The side's retained clear-line certificate is transported only by exact
endpoint equations. No root owner or line-clearance search is repeated. -/
@[expose] def sideSegment (located : Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact)
  (side : Meshes.GridLiftedDualSteps.GridSide) (kind : located.left.kind = side.kind) :
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)
      (vertices.coordinate (contact.left.project mesh.triangulation.faces).start)
      (vertices.coordinate (contact.left.project mesh.triangulation.faces).finish) // segment.WithinAmbient} := by
  have coordinates := located.left.corner_coordinates
  rw [Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.edge_coordinates, kind] at coordinates
  let edge := located.left.face.side side
  exact atEndpoints edge.segment
    edge.withinAmbient (congrArg Prod.fst coordinates) (congrArg Prod.snd coordinates)

/-- Prepare the original side contact once using its retained initial vertex owner and shared parent cache. -/
@[expose] def ofSide (located : Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact contact) (side :
  Meshes.GridLiftedDualSteps.GridSide) (kind : located.left.kind = side.kind)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    ContactPreparation contact differential domains :=
  let segment := sideSegment located side kind
  let owner := vertices.owner frames (contact.left.project mesh.triangulation.faces).start
  let piece := Paths.PreparedPathDecomposition.CoveredSegment.build segment.val segment.property owner
  let cache := Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache.build piece.path differential 0
  .segment located piece 0 (located.prepare piece differential 0 domains cache ⟨NamedEquivalent.refl
    (Paths.OwnerTraceReadings.ownerName owner)⟩)

/-- Locate the original positive contact and prepare its exact diagonal cancellation or common side-path comparison. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces) (contact :
  Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
    (positive : Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive contact.left mesh.triangulation.faces ∧
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive contact.right mesh.triangulation.faces)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    ContactPreparation contact differential domains :=
  let located := Hyperelliptic.Meshes.PuncturedGrid.SourceContactRequests.LocatedContact.build mesh contact positive.1
    positive.2
  match kind : located.left.kind with
  | .bottom => ofSide located .bottom kind
    differential domains
  | .right => ofSide located .right kind
    differential domains
  | .top => ofSide located .top kind
    differential domains
  | .left => ofSide located .left kind
    differential domains
  | .upDiagonal => .diagonal located (Or.inl kind)
  | .downDiagonal => .diagonal located (Or.inr kind)

/-- All scalar choices are made before a numerical face bank is sampled. -/
@[expose] def Budget : ContactPreparation contact differential
  domains → Normalization.InverseRootPolynomial.Coordinate → Type
  | .diagonal _ _, _ => PUnit
  | .segment _ _ _ compared, target => Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget
    compared.left.entered compared.right.entered target

/-- Prepare the original side-contact accuracy budget, retaining the trivial budget for exact diagonal cancellation. -/
@[expose] def budget (prepared : ContactPreparation contact
  differential domains) (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    prepared.Budget target :=
  match prepared with
  | .diagonal _ _ => ⟨⟩
  | .segment _ _ _ compared => compared.budget target positive

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation in
/-- Read the original side-comparison stage, or zero for exact diagonal cancellation. -/
@[expose] def budgetIndex : (prepared : ContactPreparation contact
  differential domains) → {target : Normalization.InverseRootPolynomial.Coordinate} → prepared.Budget target → Nat
  | .diagonal _ _, _, _ => 0
  | .segment _ _ _ _, _, budget => budget.index

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation in
/-- At the retained sufficient stage, the original triangle contact mismatch is below the requested positive tolerance.
-/
theorem accurate (prepared : ContactPreparation contact
  differential domains) {target : Normalization.InverseRootPolynomial.Coordinate}
    (positive : 0 < target) (budget : prepared.Budget target) {index : Nat} (later : prepared.budgetIndex budget ≤
      index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    contact.mismatch readings.values < target := by
  cases prepared with
  | diagonal located kind =>
      have zero := kind.elim
        (fun kind => Hyperelliptic.Meshes.PuncturedGrid.DiagonalContacts.LocatedContact.upDiagonal_zero located kind
          readings)
        (fun kind => Hyperelliptic.Meshes.PuncturedGrid.DiagonalContacts.LocatedContact.downDiagonal_zero located kind
          readings)
      exact zero ▸ positive
  | segment located piece parentSheet compared => exact located.mismatch_accurate compared budget later readings

end ContactPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
