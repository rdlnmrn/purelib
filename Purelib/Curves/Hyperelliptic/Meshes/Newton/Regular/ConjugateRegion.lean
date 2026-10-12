module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
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

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
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

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

public section

/-! The actual conjugate regular-region area retains both sheet polygons
and all cached cut corrections. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces hiding Coordinate

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)

open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion (PairedRegionRequest)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {face : RegularFace original}
  {lifted : LiftedPuncturedGrid grid.punctured}
  {leftValues rightValues : Fin lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
    3}

set_option genInjectivity false in
/-- The actual conjugate area of an original selected regular region.

It retains the original cut balance, conjugate projected pairing, both sheet occurrence readbacks and the cached
selected area. -/
structure ConjugateRegionSample (region : OriginalRegularFaces grid face) (words :
  Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted)
    (left : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch leftValues) (right :
      Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch rightValues)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right) where
  /-- The original regular-region cut balance on the left sewn surface. -/ balance :
    CutBalance region words left
  /-- The complete original projected pairing evaluated on the retained conjugate primitive values. -/ pairing :
    Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample balance.complete.pairing pair.values
  /-- The original sheet-zero conjugate occurrence area and offset correction. -/ zero :
    Integration.Path.PairedOccurrenceArea pair.values words.zero.edges
  /-- The original sheet-one conjugate occurrence area and offset correction. -/ one :
    Integration.Path.PairedOccurrenceArea pair.values words.one.edges
  /-- The cached actual conjugate selected region area. -/ area : Gaussian.Basic.Canonical
  /-- The area uses the retained conjugate primitive values on the original selected triangle boundaries. -/ area_eq :
    area = edgeListArea pair.values (balance.selected.triangles.flatMap OrientedTriangle.boundary)

constructive_injectivity ConjugateRegionSample

namespace ConjugateRegionSample

variable {region : OriginalRegularFaces grid face} {words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords
  face lifted}
  {left : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch leftValues} {right :
    Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch rightValues}
  {pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right}

/-- Cache the original selected conjugate area, pairing and both sheet readbacks from the supplied sewn conjugate pair.
-/
@[expose] def build (region : OriginalRegularFaces grid face) (words :
  Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted)
    (left : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch leftValues) (right :
      Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch rightValues)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair left right) :
    ConjugateRegionSample region words left right pair :=
  let balance := CutBalance.build region words left
  let values := pair.values
  ⟨balance, Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample.build balance.complete.pairing
    values,
    Integration.Path.PairedOccurrenceArea.build values words.zero.edges,
      Integration.Path.PairedOccurrenceArea.build values words.one.edges,
    edgeListArea values (balance.selected.triangles.flatMap OrientedTriangle.boundary), rfl⟩

/-- The complete original conjugate jump, defect and both occurrence-offset correction. -/
@[expose] def correction (sample : ConjugateRegionSample region words left right pair) : Gaussian :=
  sample.pairing.jumpSum + sample.pairing.defectSum + sample.zero.correction + sample.one.correction

/-- The selected paired area has the same geometric cancellation certificate
as the original region, evaluated at the actual paired primitives. -/
theorem area_balance (sample : ConjugateRegionSample region words left right pair) :
    sample.area = sample.zero.raw + sample.one.raw + sample.pairing.jumpSum + sample.pairing.defectSum := by
  have equal := (congrArg (edgeListArea pair.values) sample.balance.edges_eq).symm.trans
    (sample.balance.complete.area_eq_jumps_defects pair.values sample.pairing)
  rw [edgeListArea_append, Topology.Polygon.WitnessReadbacks.reverse_area,
    Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.edges, edgeListArea_append,
    ← sample.area_eq, ← sample.zero.raw_eq, ← sample.one.raw_eq] at equal
  calc
    sample.area = (sample.area + -(sample.zero.raw + sample.one.raw)) + (sample.zero.raw + sample.one.raw) := by ring1
    _ = _ := by rw [equal]; ring1

/-- The corrected original conjugate region area is exactly the sum of its two corrected sheet areas. -/
theorem corrected_area (sample : ConjugateRegionSample region words left right pair) :
    sample.area - sample.correction =
      (sample.zero.raw - sample.zero.correction) + (sample.one.raw - sample.one.correction) := by
  rw [sample.area_balance]
  unfold correction
  ring1

end ConjugateRegionSample

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  grid.faces.regulars}
  {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The canonical polygon keeps the conjugate of the actual first edge
reading, without introducing a conjugate holomorphic differential. -/
@[expose] def conjugatePolygon (face : RegularFace original) (lifted : LiftedPuncturedGrid grid.punctured)
    (leftValues rightValues : Fin lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
      3) (sheet : Fin 2) : Gaussian :=
  Path.PairedIncrementArea.area ((lifted.edges.indexedEdges lifted.vertices
    (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet).map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
        leftValues edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightValues edge⟩ :
          PrimitivePoint)))

namespace PairedRegionRequest

variable {words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {error : Rational} {floor : Nat}

/-- Both original sheet polygons are compared at the existing common tail.
No sheet polygon, cut jump, defect or offset correction is discarded. -/
theorem conjugate_sheets_accurate (request : PairedRegionRequest words leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank lifted.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      lifted.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    {region : OriginalRegularFaces grid face} (sample : ConjugateRegionSample region words leftSurface rightSurface
      pair)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction -
      (conjugatePolygon face lifted leftReadings.values rightReadings.values 0 +
        conjugatePolygon face lifted leftReadings.values rightReadings.values 1)) ≤ 4 * (error / 32) := by
  have zero := Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing.PairedSheetRequest.conjugate_corrected_accurate
    request.zero leftReadings rightReadings leftSurface rightSurface
    ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans later)) pair sample.zero
  have one := Hyperelliptic.Meshes.Newton.Regular.ConjugateSewing.PairedSheetRequest.conjugate_corrected_accurate
    request.one leftReadings rightReadings leftSurface rightSurface
    ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _ _).trans later)) pair sample.one
  have equal : sample.area - sample.correction -
      (conjugatePolygon face lifted leftReadings.values rightReadings.values 0 +
        conjugatePolygon face lifted leftReadings.values rightReadings.values 1) =
      ((sample.zero.raw - sample.zero.correction) - conjugatePolygon face lifted leftReadings.values
        rightReadings.values 0) +
      ((sample.one.raw - sample.one.correction) - conjugatePolygon face lifted leftReadings.values rightReadings.values
        1) := by
    rw [sample.corrected_area]
    ring1
  rw [equal]
  exact ((Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct zero one)
      (by decide))).trans_eq (by ring1)

/-- The two actual conjugate canonical sheet polygons differ by at most ten times the retained local allowance. -/
private theorem conjugate_canonical_difference (request : PairedRegionRequest words leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank lifted.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      lifted.mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (conjugatePolygon face lifted leftReadings.values rightReadings.values 0 -
      conjugatePolygon face lifted leftReadings.values rightReadings.values 1) ≤ 10 * (error / 32) := by
  have zeroLater := (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  have oneLater := (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_left _ _).trans later)
  let oppositeComparison := request.opposite.realizeConjugate leftReadings rightReadings ((Nat.Order.le_max_right _
    _).trans later) 0 1 (by decide)
  have opposite := oppositeComparison.pay
  rw [oppositeComparison.residual_readback] at opposite
  let zeroComparison := request.zero.chart.realizeSupplied .conjugate leftReadings rightReadings
    ((Nat.Order.le_max_right _ _).trans zeroLater) oppositeComparison.leftSources
  have zero := zeroComparison.pay
  rw [zeroComparison.residual_readback] at zero
  let oneComparison := request.one.chart.realizeSupplied .conjugate leftReadings rightReadings ((Nat.Order.le_max_right
    _ _).trans oneLater) oppositeComparison.rightSources
  have one := oneComparison.pay
  rw [oneComparison.residual_readback] at one
  let polygon := conjugatePolygon face lifted leftReadings.values rightReadings.values
  let source := fun sheet => Path.PairedIncrementArea.area ((words.paired.sources sheet).map (fun source =>
    (⟨Data.Gaussian.Basic.conj (source.increment leftReadings.values), source.increment rightReadings.values⟩ :
      PrimitivePoint)))
  have readback (sheet : Fin 2) :
      Path.PairedIncrementArea.area ((words.paired.sources sheet).map (fun source =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          leftReadings.values (source.project lifted.mesh.triangulation.faces)),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values
            (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint))) =
      polygon sheet := by
    unfold polygon conjugatePolygon
    rw [← words.paired.sources_project sheet, List.Map.map_map]
    rfl
  change Data.Gaussian.Norm.Basic.normSq (source 0 - Path.PairedIncrementArea.area
      ((words.paired.sources 0).map (fun source =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          leftReadings.values (source.project lifted.mesh.triangulation.faces)),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values
            (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 32 / 4 at zero
  rw [readback 0] at zero
  change Data.Gaussian.Norm.Basic.normSq (source 1 - Path.PairedIncrementArea.area
      ((words.paired.sources 1).map (fun source =>
        (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          leftReadings.values (source.project lifted.mesh.triangulation.faces)),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh rightReadings.values
            (source.project lifted.mesh.triangulation.faces)⟩ : PrimitivePoint)))) ≤ error / 32 / 4 at one
  rw [readback 1] at one
  have partNonnegative := (Fraction.Order.Field.div_pos_direct request.positive (by
      decide +kernel : (0 : Rational) < 32)).le
  have smaller : error / 32 / 4 ≤ error / 32 := Fraction.Order.Field.divide_le_self partNonnegative (by decide)
  have reversed : Data.Gaussian.Norm.Basic.normSq (polygon 0 - source 0) ≤ error / 32 := by
    rw [show polygon 0 - source 0 = -(source 0 - polygon 0) by ring1,
      Gaussian.Norm.Basic.normSq_neg]
    exact zero.trans smaller
  have middle : Data.Gaussian.Norm.Basic.normSq (source 0 - polygon 1) ≤ 2 * (error / 32 + error / 32) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_via (source 0) (source 1) (polygon 1)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct opposite
        (one.trans smaller)) (by decide))
  exact ((Gaussian.Norm.Bounds.normSq_sub_le_via (polygon 0) (source 0) (polygon 1)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct reversed
      middle) (by decide))).trans_eq (by ring1)

section

/-- Two sheets have a positive literal finite bound. -/
local instance : NeZero (2 : Nat) := ⟨by decide +kernel⟩

/-- The compiler may arrive on either sheet. Both chart errors and the
opposite-sheet source comparison are paid on the same retained samples. -/
theorem conjugate_accurate (request : PairedRegionRequest words leftFixed rightFixed error floor) (sheet : Fin 2)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage
      domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank lifted.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      lifted.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      leftReadings.values)
    (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
      rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    {region : OriginalRegularFaces grid face} (sample : ConjugateRegionSample region words leftSurface rightSurface
      pair)
    (later : request.index ≤ stage) :
    let polygon := conjugatePolygon face lifted leftReadings.values rightReadings.values sheet
    Data.Gaussian.Norm.Basic.normSq (sample.area - sample.correction - (polygon + polygon)) ≤ error := by
  intro polygon
  let canonical := conjugatePolygon face lifted leftReadings.values rightReadings.values
  have sumBound := conjugate_sheets_accurate request leftReadings rightReadings leftSurface rightSurface pair sample
    later
  have difference := conjugate_canonical_difference request leftReadings rightReadings later
  have either : ∀ sheet : Fin 2, Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical sheet +
    canonical sheet)) ≤ 10 * (error / 32) := by
    intro position
    refine Fin.cases_induction ?_ (fun next => ?_) position
    · change Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical 0 + canonical 0)) ≤ 10 * (error
        / 32)
      rw [show canonical 0 + canonical 1 - (canonical 0 + canonical 0) = -(canonical 0 - canonical 1) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
      exact difference
    · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
      change Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical 1 + canonical 1)) ≤ 10 * (error
        / 32)
      rw [show canonical 0 + canonical 1 - (canonical 1 + canonical 1) = canonical 0 - canonical 1 by ring1]
      exact difference
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via (sample.area - sample.correction)
    (canonical 0 + canonical 1) (canonical sheet + canonical sheet)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sumBound
        (either sheet)) (by decide))
  have partNonnegative := (Fraction.Order.Field.div_pos_direct request.positive (by
      decide +kernel : (0 : Rational) < 32)).le
  have paid : 2 * (4 * (error / 32) + 10 * (error / 32)) ≤ error := by
    calc
      _ = 28 * (error / 32) := by ring1
      _ ≤ 32 * (error / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        partNonnegative
      _ = error := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  exact estimate.trans paid

end

end PairedRegionRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion
