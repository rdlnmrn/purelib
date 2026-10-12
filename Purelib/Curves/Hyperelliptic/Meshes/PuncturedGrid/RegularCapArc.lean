module
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalArc
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Requested inverse arcs for actual shared-grid cap comparisons

Reuse the regular cap request and its cached source parents. The selected
minimum arc depth pays both preparation meshes and the full path refinement
error. A later common energy depth changes only the polynomial subdivision.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularUniform.Path
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
open Purelib.Integration.Path
open Purelib.Data.Rat

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
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Riemann.Meshes.GridLiftedMesh.LiftedMesh
    vertices edges faces}
  {start finish : Data.Gaussian.Basic.Canonical} {segment : Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
    (Curves.Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
    differential parentSheet}

namespace RegularCapRequest

variable {prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular
  compared} {target areaTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest
    prepared target areaTarget floor}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {sample :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest
  in
set_option genInjectivity false in
/-- The retained uniform inverse-arc request attached to the original regular cap comparison.

Its minimum polynomial depth pays the original segment mesh and both uniform preparation refinements. -/
structure ArcRequest (request : SegmentComparison.RegularCapRequest prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) (arcTarget : InverseRootPolynomial.Coordinate) where
  /-- The original uniform area request on the retained prepared cap path and exact supplied cap sample. -/ uniform :
    Path.UniformAreaRequest prepared.path sample arcTarget 0
  /-- The cached complete polynomial arc depth required by the original segment and uniform request. -/ minimumDepth :
    Nat
  /-- The minimum depth is exactly the original segment mesh depth plus the retained uniform coarse and fine depths. -/
    minimumDepth_eq : minimumDepth = piece.mesh.depth + uniform.coarseDepth + uniform.depth

constructive_injectivity ArcRequest

namespace ArcRequest

variable {arcTarget : Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Prepare the inverse-arc comparison from the existing cap polynomial bounds and cache its complete original minimum
depth. -/
@[expose] def build (request : SegmentComparison.RegularCapRequest prepared target areaTarget floor)
    (bounds : Charts.Reciprocal.Cap.EnergyBounds sample) (arcTarget : InverseRootPolynomial.Coordinate) (positive : 0 <
      arcTarget) :

      RegularCapRequest.ArcRequest
      request sample arcTarget :=
  let uniform := UniformAreaRequest.build prepared.path bounds arcTarget positive 0
  ⟨uniform, piece.mesh.depth + uniform.coarseDepth + uniform.depth, rfl⟩

/-- Raise the original cached minimum by only the additional shared fine subdivision. The caller may synchronize this
value across all occurrences. -/
@[expose] def minimumAt (arc :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.ArcRequest
  request sample arcTarget) (fine : Nat) : Nat :=
  arc.minimumDepth + (fine - arc.uniform.depth)

set_option genInjectivity false in
/-- The original cap evaluation is an input, so surface aggregation keeps its exact source, root readings, and area
cache. -/
structure Evaluation (arc :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.ArcRequest
  request sample arcTarget) {fine readingIndex : Nat}
    (original : RegularCapRequest.Evaluation request sample fine readingIndex) (energyDepth : Nat) where
  /-- The original acquired cap subdivision pays the retained uniform fine-depth request. -/ fine_later :
    arc.uniform.depth ≤ fine
  /-- The supplied energy subdivision pays the original minimum and actual extra fine subdivision. -/ depth_later :
    arc.minimumAt fine ≤ energyDepth
  /-- The actual uniform comparison consuming the original cap cache at the retained shifted energy depth. -/ uniform :
    UniformAreaRequest.Evaluation arc.uniform original.cap (energyDepth - piece.mesh.depth)
  /-- The cached actual full inverse-arc value on the original physical segment. -/ value :
    Data.Gaussian.Basic.Canonical
  /-- The arc cache equals the original cap polynomial's complete inverse-arc area at the retained energy depth. -/
    value_eq : value = ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth start finish
  /-- The full original arc minus its signed endpoint term is strictly close to the actual retained cap area. -/
    cap_close : Data.Gaussian.Norm.Basic.normSq (value - BoundaryRibbon.area
    (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) - original.cap.cap.area) < arcTarget

constructive_injectivity Evaluation

/-- Evaluate the retained uniform request against the supplied original cap cache at the paid common energy depth, then
retain its full inverse-arc readback. -/
@[expose] def evaluate (arc :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.ArcRequest
  request sample arcTarget) {fine readingIndex : Nat}
    (original : RegularCapRequest.Evaluation request sample fine readingIndex) (energyDepth : Nat)
    (fineLater : arc.uniform.depth ≤ fine) (depthLater : arc.minimumAt fine ≤ energyDepth) :
      Evaluation
      arc original energyDepth := by
  have minimumEq := arc.minimumDepth_eq
  have paid : arc.minimumDepth + (fine - arc.uniform.depth) ≤ energyDepth := depthLater
  have enough : piece.mesh.depth + arc.uniform.coarseDepth + fine ≤ energyDepth := by omega
  have coarseLater : arc.uniform.coarseDepth + fine ≤ energyDepth - piece.mesh.depth := by omega
  have sourceLater : piece.mesh.depth ≤ energyDepth := by omega
  let uniform := arc.uniform.evaluate original.cap (energyDepth - piece.mesh.depth) fineLater coarseLater
  let endpointArea := BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹)
  let value := uniform.summary.area + endpointArea
  have areaEq := uniform.area_eq_arc
  rw [Data.Nat.Subtraction.add_sub_of_le sourceLater] at areaEq
  have valueEq : value = ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth start finish := by
    dsimp only [value, endpointArea]
    rw [areaEq]
    ring1
  refine ⟨fineLater, depthLater, uniform, value, valueEq, ?_⟩
  change Data.Gaussian.Norm.Basic.normSq ((uniform.summary.area + endpointArea) - endpointArea -
    original.cap.cap.area) < arcTarget
  rw [add_sub_cancel_right]
  exact uniform.area_error

/-- The opposite arc is the orientation used by the existing energy fan. Both the open endpoint term and the actual
cached cap area retain their signs. -/
theorem Evaluation.opposite_close {arc :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RegularCapRequest.ArcRequest
  request sample arcTarget} {energyDepth fine readingIndex : Nat}
    {original : RegularCapRequest.Evaluation request sample fine readingIndex}
    (evaluated :
      Evaluation
      arc original energyDepth) :
    Data.Gaussian.Norm.Basic.normSq (ReciprocalRadialGeometry.arcArea sample.primitive.value.eval energyDepth
      finish start +
      BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) +
      original.cap.cap.area) < arcTarget := by
  rw [ReciprocalRadialGeometry.arcArea_reverse, ← evaluated.value_eq]
  have reversed : -evaluated.value +
      BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) +
      original.cap.cap.area = -(evaluated.value -
        BoundaryRibbon.area (sample.primitive.value.eval start⁻¹) (sample.primitive.value.eval finish⁻¹) -
        original.cap.cap.area) := by ring1
  rw [reversed, Data.Gaussian.Norm.Basic.normSq_neg]
  exact evaluated.cap_close

end ArcRequest
end RegularCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
