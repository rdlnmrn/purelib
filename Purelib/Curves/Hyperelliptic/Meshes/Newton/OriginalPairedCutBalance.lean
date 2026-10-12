module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-! The selected original branch region with two actual sewn primitives.
Its inner boundary and all cut corrections remain in the comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
open Purelib.Integration.Path
open Purelib.Integration.Path.PairedOccurrenceArea
open _root_.Purelib.Integration.Path renaming PairedOccurrenceArea -> PairedOccurrenceArea
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.PrimitiveJumps
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (OriginalCutBalance)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Integration.Path (PairedOccurrenceArea)

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {outer : OriginalAnnularFaces grid index} {annulus :
    AnnularFaces grid index}
  {region : Lifted annulus current}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {leftDifferential rightDifferential :
    Differential genus}
  {geometry : IncludedHoleSewing bank grid.shrunk.included index domains leftDifferential}
  {leftValues rightValues : Fin current.mesh.triangles.length →
    PrimitiveValues 3}

/-- The components retain their distinct sewn-surface owners. -/
@[expose] def pairedValues (left : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftValues)
    (right : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues) : Fin
      current.cutPolygon.patch.cut.count → PrimitivePoint :=
  fun vertex => ⟨left.sewn.values vertex, right.sewn.values vertex⟩

set_option genInjectivity false in
/-- The paired area sample of an original selected branch region.

Distinct left and right sewn surfaces supply the paired primitive values; all inner-boundary, pairing and occurrence
corrections remain retained. -/
structure PairedSample (balance : OriginalCutBalance outer region geometry left)
    (right : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues) where
  /-- The actual primitive sample for each retained projected cut-edge pair. -/ pairing :
    ProjectedEdgePairing.PrimitiveSample balance.complete.pairing (pairedValues left right)
  /-- The paired occurrence-area readback on the original cut-word edges. -/ readback :
    Integration.Path.PairedOccurrenceArea (pairedValues left right) geometry.word.edges
  /-- The cached paired inner-boundary area. -/ inner : Data.Gaussian.Basic.Canonical
  /-- The inner cache equals the area of the retained inner word. -/ inner_eq : inner = edgeListArea (pairedValues left
    right) balance.inner.word.edges
  /-- The cached paired area of the selected original triangles. -/ area : Data.Gaussian.Basic.Canonical
  /-- The area cache equals the boundary edge-list area of the selected triangles. -/ area_eq : area = edgeListArea
    (pairedValues left right) (balance.selected.triangles.flatMap OrientedTriangle.boundary)

constructive_injectivity PairedSample

namespace PairedSample

variable {left : CachedSample current.cutPolygon.patch leftValues}
  {right : CachedSample current.cutPolygon.patch rightValues}
  {balance : OriginalCutBalance outer region geometry left}

/-- Cache the complete paired region sample using the original left balance and supplied right surface. -/
@[expose] def build (balance : OriginalCutBalance outer region geometry left)
    (right : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues) : PairedSample balance right :=
  ⟨PrimitiveSample.build balance.complete.pairing (pairedValues left right),
    PairedOccurrenceArea.build (pairedValues left right) geometry.word.edges,
    edgeListArea (pairedValues left right) balance.inner.word.edges, rfl,
    edgeListArea (pairedValues left right) (balance.selected.triangles.flatMap OrientedTriangle.boundary), rfl⟩

/-- The retained sum of inner-boundary, cut-jump, pairing-defect and occurrence corrections. -/
@[expose] def correction (sample : PairedSample balance right) : Gaussian :=
  sample.inner + sample.pairing.jumpSum + sample.pairing.defectSum + sample.readback.correction

/-- The selected paired area splits into the raw cut readback, inner boundary, jumps and defects. -/
theorem area_balance (sample : PairedSample balance right) :
    sample.area = sample.readback.raw + sample.inner + sample.pairing.jumpSum + sample.pairing.defectSum := by
  have equal := (congrArg (edgeListArea (pairedValues left right)) balance.edges_eq).symm.trans
    (balance.complete.area_eq_jumps_defects (pairedValues left right) sample.pairing)
  rw [edgeListArea_append, WitnessReadbacks.reverse_area, edgeListArea_append, ← sample.area_eq,
    ← sample.readback.raw_eq, ← sample.inner_eq] at equal
  calc
    sample.area = (sample.area + -(sample.readback.raw + sample.inner)) + (sample.readback.raw + sample.inner) := by
      ring1
    _ = _ := by rw [equal]; ring1

/-- Removing all retained corrections leaves exactly the corrected paired occurrence readback. -/
theorem corrected_area (sample : PairedSample balance right) :
    sample.area - sample.correction = sample.readback.raw - sample.readback.correction := by
  rw [sample.area_balance]
  unfold correction
  ring1

/-- The comparison uses the actual doubled original-cell word. It does not erase the inner boundary or replace the
doubled word by a single based lap. -/
theorem canonical_accurate {leftFixed : FaceMagnitudeBank domains leftDifferential}
    {rightFixed : FaceMagnitudeBank domains rightDifferential} {error : Rational} {floor : Nat}
    (request : PairedRequest geometry leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values)
    {balance : OriginalCutBalance outer region geometry leftSurface}
    (sample : PairedSample balance rightSurface) (later : request.index ≤ stage) :
    let walk := grid.shrunk.included.resplit (bank.rows.get index).boundary
      ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))
    Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction -
      PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨edgeValuation current.mesh leftReadings.values edge,
          CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ : PrimitivePoint)))) ≤ error := by
  rw [sample.corrected_area]
  exact PairedRequest.accurate
    request (SourceChartComparison.PairedReadings.ofReadings
      (owner := SourceChartComparison.ownerFromMesh
        current.mesh)
      leftReadings rightReadings) leftSurface rightSurface sample.readback later

end PairedSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
