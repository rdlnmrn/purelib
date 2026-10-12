module
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# The actual exterior component uses one signed regular primitive

Read the parity-selected cap evaluations already held by the shared surface.
Their parent certificates concatenate independently of local request budgets.
The original component's root chain identifies all signs, including the
cross-segment terms in the full area.
-/

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open CapRequest.Evaluation

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.SideBank.Regular
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open
  ExteriorProgram.SurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Integration.Path

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapPreparation
  CapRequest)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment
    curve.polynomial (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Purelib.Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
    placement piece differential parentSheet}

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation
  regular compared} {target areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {request :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
    prepared target areaTarget floor} {index depth readingIndex : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
namespace Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- The stored odd-degree certificate excludes the ramified case when the curve has even degree. No new request or
numerical evaluation is selected. -/
theorem regular_witnesses (evaluated : CapRequest.Evaluation request sample depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ paths, evaluated.capPath = paths.flatten ∧
      Nonempty (Charts.Reciprocal.Disk.RegularWitnesses sample depth prepared.path.bank paths) := by
  cases request with
  | regular request =>
      refine ⟨evaluated.data.cap.parents.pairs.map Prod.snd, ?_, ⟨Results.witnesses evaluated.data.cap.parents⟩⟩
      change evaluated.paths.2 = _
      rw [evaluated.paths_eq]
      rfl
  | ramified odd request =>
      have impossible : False := by omega
      exact impossible.elim

end Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
namespace Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest in
/-- For even degree, the retained cap area equals the complete original unsigned regular primitive path area. -/
theorem regular_area_unsigned (evaluated : CapRequest.Evaluation request sample depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    evaluated.right.area = IncrementArea.pathArea (SideBank.regularPrimitivePaths sample.primitive.value depth
      prepared.path.bank).flatten := by
  obtain ⟨paths, equal, ⟨witnesses⟩⟩ := evaluated.regular_witnesses degree
  rw [evaluated.right.area_eq, equal]
  exact witnesses.area_unsigned prepared.path.links

end Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.SideBank.Regular
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open ExteriorProgram.SurfacePreparation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
open Purelib.Integration.Path
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (SampledEntry)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars}
  {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Grouping certificates is proof-side only. The actual flattened cap paths and their numerical summaries stay in the
supplied surface samples. -/
theorem
  SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_witnesses
    (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea floor))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ paths, (values.map (fun value => value.evaluated.capPath)).flatten = paths.flatten ∧
      Nonempty (Charts.Reciprocal.Disk.RegularWitnesses sample depth
        (SurfaceOccurrence.capSpine (values.map (fun value => value.entry.occurrence))).bank paths) := by
  induction values with
  | nil => exact ⟨[], rfl, ⟨.nil⟩⟩
  | cons head tail ih =>
      obtain ⟨first, firstEq, ⟨firstWitnesses⟩⟩ := head.evaluated.regular_witnesses degree
      obtain ⟨last, lastEq, ⟨lastWitnesses⟩⟩ := ih
      refine ⟨first ++ last, ?_, ⟨firstWitnesses.append lastWitnesses⟩⟩
      simp only [List.map_cons, List.flatten_cons, Flatten.flatten_append, -eq_self, -iff_self]
      rw [firstEq, lastEq]

/-- Exact component-wide area identity, including all cross-segment terms. The signs come from the original operational
root chain. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.regular_cap_area
  {program : PeriodPrograms.ExteriorProgram lifted differential}
    (prepared : ExteriorProgram.SurfacePreparation regular domains program)
    (values : List (AllSurfacePreparation.SampledEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea floor))
    (occurrences : values.map (fun value => value.entry.occurrence) = prepared.occurrences)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    IncrementArea.pathArea (values.map (fun value => value.evaluated.capPath)).flatten =
      IncrementArea.pathArea (SideBank.regularPrimitivePaths sample.primitive.value depth (SurfaceOccurrence.capSpine
        prepared.occurrences).bank).flatten := by
  obtain ⟨paths, pathsEq, witnesses⟩ :=
    SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_witnesses
    values degree
  rw [occurrences] at witnesses
  obtain ⟨witnesses⟩ := witnesses
  let joined := JoinedCap.build prepared
  have links : SideBank.Links (SurfaceOccurrence.capSpine prepared.occurrences).bank := by
    rw [← joined.spine_eq]
    exact joined.links
  rw [pathsEq]
  exact witnesses.area_unsigned links

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
