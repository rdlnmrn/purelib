module
meta import Purelib.Elab.ConstructiveInjectivity
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
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleSewing
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing
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

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib

public section

/-! Conjugate energy on an original branch region retains the actual inner
boundary and all cut corrections in its doubled-boundary comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (OriginalCutBalance)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedHoleSewing (PairedRequest)
open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {outer : OriginalAnnularFaces grid index} {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid
    index}
  {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus current}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}
  {geometry : IncludedHoleSewing bank grid.shrunk.included index domains leftDifferential}
  {leftValues rightValues : Fin current.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
    3}

set_option genInjectivity false in
/-- The actual conjugate sample on an original branch-region cut balance.

It retains the complete projected pairing, original occurrence readback and cached inner and selected region areas. -/
structure ConjugateSample (balance : OriginalCutBalance outer region geometry left)
    (right : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right) where
  /-- The actual primitive sample on the complete original projected pairing. -/ pairing :
    Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample balance.complete.pairing pair.values
  /-- The retained paired occurrence readback on the original hole word. -/ readback :
    Integration.Path.PairedOccurrenceArea pair.values geometry.word.edges
  /-- The cached original inner boundary area. -/ inner : Gaussian.Basic.Canonical
  /-- The inner area is exactly the value on the retained inner word. -/ inner_eq : inner = edgeListArea pair.values
    balance.inner.word.edges
  /-- The cached selected original region area. -/ area : Gaussian.Basic.Canonical
  /-- The area is exactly the full original selected triangle boundary value. -/ area_eq : area = edgeListArea
    pair.values (balance.selected.triangles.flatMap OrientedTriangle.boundary)

constructive_injectivity ConjugateSample

namespace ConjugateSample

variable {left : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftValues}
  {right : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues}
  {balance : OriginalCutBalance outer region geometry left}
  {pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right}

/-- Cache the original conjugate pairing, occurrence readback and both region areas without changing their cut owners.
-/
@[expose] def build (balance : OriginalCutBalance outer region geometry left)
    (right : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightValues)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right) : ConjugateSample balance right pair
      :=
  ⟨Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample.build balance.complete.pairing pair.values,
    Integration.Path.PairedOccurrenceArea.build pair.values geometry.word.edges,
    edgeListArea pair.values balance.inner.word.edges, rfl,
    edgeListArea pair.values (balance.selected.triangles.flatMap OrientedTriangle.boundary), rfl⟩

/-- The original inner boundary, jump, defect and occurrence-offset correction. -/
@[expose] def correction (sample : ConjugateSample balance right pair) : Gaussian :=
  sample.inner + sample.pairing.jumpSum + sample.pairing.defectSum + sample.readback.correction

/-- The actual selected region area equals the retained raw hole, inner boundary, jump and defect contributions. -/
theorem area_balance (sample : ConjugateSample balance right pair) :
    sample.area = sample.readback.raw + sample.inner + sample.pairing.jumpSum + sample.pairing.defectSum := by
  have equal := (congrArg (edgeListArea pair.values) balance.edges_eq).symm.trans
    (balance.complete.area_eq_jumps_defects pair.values sample.pairing)
  rw [edgeListArea_append, Topology.Polygon.WitnessReadbacks.reverse_area, edgeListArea_append, ← sample.area_eq,
    ← sample.readback.raw_eq, ← sample.inner_eq] at equal
  calc
    sample.area = (sample.area + -(sample.readback.raw + sample.inner)) + (sample.readback.raw + sample.inner) := by
      ring1
    _ = _ := by rw [equal]; ring1

/-- Subtracting the complete original correction leaves exactly the retained occurrence's corrected raw area. -/
theorem corrected_area (sample : ConjugateSample balance right pair) :
    sample.area - sample.correction = sample.readback.raw - sample.readback.correction := by
  rw [sample.area_balance]
  unfold correction
  ring1

/-- The comparison uses the actual doubled original-cell word. It does not
erase the inner boundary or replace the doubled word by a single based lap. -/
theorem canonical_accurate {leftFixed : FaceMagnitudeBank domains leftDifferential}
    {rightFixed : FaceMagnitudeBank domains rightDifferential} {error : Rational} {floor : Nat}
    (request : PairedRequest geometry leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      rightReadings.values)
    {balance : OriginalCutBalance outer region geometry leftSurface}
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (sample : ConjugateSample balance rightSurface pair) (later : request.index ≤ stage) :
    let walk := grid.shrunk.included.resplit (bank.rows.get index).boundary
      ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))
    Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction -
      Path.PairedIncrementArea.area ((current.edges.indexedEdges current.vertices (walk.append walk) 0).map (fun edge =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh leftReadings.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
            PrimitivePoint)))) ≤ error := by
  rw [sample.corrected_area]
  exact Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateHoleSewing.PairedRequest.conjugate_accurate
    request leftReadings rightReadings leftSurface rightSurface pair sample.readback later

end ConjugateSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalConjugateCutBalance
