module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# One triangle-value bank for actual periods and sewn cut surfaces

The source list retains the original routed edge occurrences and their
orientations. Its increments equal the whole-period comparison value.
Sewing consumes those very local values and retains all resulting errors;
it does not identify sewn jumps with periods by dropping seam corrections.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
    {ambient : Rational.Box}

/-- Read the original ordered and oriented triangle-edge occurrences from the retained segment assignment. -/
@[expose] def sourceEdges : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared},
    Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces → List
      (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons placement remaining => placement.location.sourceEdge ::
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges remaining

/-- Projecting the retained triangle-edge occurrences gives the exact original assigned edge list. -/
theorem sourceEdges_project : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
    (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces),
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges assigned).map (fun source =>
      source.project mesh.triangulation.faces) = assigned.indexed
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons placement remaining =>
      congrArg₂ List.cons placement.location.sourceEdge_project
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges_project
        remaining)

/-- The original triangle-edge readings equal the retained corner increments entry by entry. -/
theorem sourceEdges_increments {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  faces.regulars} {differential : Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat}
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
        Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}
      (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces),
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges assigned).map (fun source
        => source.increment readings.values) =
        Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements shared assigned
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons placement remaining =>
      congrArg₂ List.cons (readings.route_increment placement.location)
        (sourceEdges_increments
        readings remaining)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source}
  {bank : Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank prepared} {differential : Fin genus} {comparison :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank bank differential}
  {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat}

/-- The original whole-period comparison value equals the sum of the retained triangle-edge increments. -/
theorem value_eq_triangles (result :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings result.locals.numerics
      lifted.mesh) :
    result.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges bank.assigned).map
      (fun source => source.increment readings.values)) :=
  result.value_eq_corners.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges_increments readings
      bank.assigned)).symm

set_option genInjectivity false in
/-- The local triangle bank and sewn values are both retained executable
data. A caller sharing several periods may reuse the same triangle bank. -/
structure Sewn (result : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod
  comparison target minimumStage) (patch : Topology.Surface.Sewing.SewingTree.SewnPatch lifted.mesh.triangulation.faces)
  where
  /-- The actual original triangle readings of the retained period's numerical primitive bank. -/ triangles :
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings result.locals.numerics lifted.mesh
  /-- The sewn sample constructed from those exact retained triangle values. -/ surface :
    Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample patch triangles.values

constructive_injectivity Sewn

/-- Construct the sewn sample using the supplied original triangle-value bank without reacquiring its readings. -/
@[expose] def sewWith (result :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage) (patch : Topology.Surface.Sewing.SewingTree.SewnPatch lifted.mesh.triangulation.faces)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings result.locals.numerics
      lifted.mesh) : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result patch :=
  ⟨triangles, Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample.build patch triangles.values⟩

/-- Acquire the original triangle-value bank once and retain it in the sewn sample. -/
@[expose] def sew (result :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
  minimumStage) (patch : Topology.Surface.Sewing.SewingTree.SewnPatch lifted.mesh.triangulation.faces) :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result patch :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.sewWith result patch
    (Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.build result.locals.numerics
    lifted.mesh)

namespace Sewn

variable {result : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod
  comparison target minimumStage} {patch : Topology.Surface.Sewing.SewingTree.SewnPatch lifted.mesh.triangulation.faces}

/-- The retained triangle-edge sum approximates the original scheduled period-program sample within its target. -/
theorem program_accurate (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result
  patch) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges bank.assigned).map
      (fun source => source.increment sample.triangles.values)) -
        ((prepared.program differential).integral.model result.sample.stage).integralSample) < target := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.value_eq_triangles result
    sample.triangles]
  exact result.program_accurate

/-- The retained sewn-face squared errors are at most twice their total allowance. -/
theorem face_errors (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result
  patch) : sample.surface.faces.squaredErrors ≤ 2 * sample.surface.faces.totalAllowance :=
  sample.surface.face_errors

end Sewn
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod
