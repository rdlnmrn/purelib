module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.Sewing
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
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
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The actual original regular-cell cut area agrees, after its explicit
cut corrections, with twice either retained canonical boundary polygon. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {face :
    Meshes.PuncturedGridFaces.RegularFace original}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A paid comparison of the original regular-cell cut with both retained canonical boundary sheets.

It retains both sewing requests and their opposite-sheet comparison, with a common sufficient stage. -/
structure AreaRequest (words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential)
    (error : Fraction.Rational) (floor : Nat) where
  /-- The requested whole regular-region error is positive. -/ positive : 0 < error
  /-- The original retained sewing data. -/ sewing : Hyperelliptic.Meshes.Newton.Regular.Sewing.SewingData domains
    differential
  /-- The original sheet-zero sewing request at one thirty-second of the target. -/ zero :
    Hyperelliptic.Meshes.Newton.Regular.Sewing.SheetRequest words 0 words.zero sewing fixed (error / 32) floor
  /-- The original sheet-one sewing request at the same local allowance. -/ one :
    Hyperelliptic.Meshes.Newton.Regular.Sewing.SheetRequest words 1 words.one sewing fixed (error / 32) floor
  /-- The retained comparison of the two original sheet areas. -/ opposite :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests.AreaRequest fixed words.paired (error / 32)
  /-- The cached common sufficient stage. -/ index : Nat
  /-- The stage is exactly the maximum of the two sewing requests and opposite-sheet request. -/ index_eq : index = max
    (max zero.index one.index) opposite.index

constructive_injectivity AreaRequest

namespace AreaRequest

variable {words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted} {fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential}
  {error : Fraction.Rational} {floor : Nat}

/-- Prepare the original two sheet sewing requests and their opposite-sheet comparison with one sufficient stage. -/
def build (words : Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
      AreaRequest words fixed error floor :=
  let sewing := Hyperelliptic.Meshes.Newton.Regular.Sewing.SewingData.build domains differential
  have partPositive : 0 < error / 32 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let zero := Hyperelliptic.Meshes.Newton.Regular.Sewing.SheetRequest.build words 0 words.zero sewing fixed (error / 32)
    partPositive floor
  let one := Hyperelliptic.Meshes.Newton.Regular.Sewing.SheetRequest.build words 1 words.one sewing fixed (error / 32)
    partPositive floor
  let opposite := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests.AreaRequest.build fixed words.paired (error
    / 32) partPositive
  ⟨positive, sewing, zero, one, opposite, max (max zero.index one.index) opposite.index, rfl⟩

open Purelib.Integration in
/-- The actual canonical boundary areas on the two original sheets differ by at most ten times the retained local
allowance. -/
private theorem canonical_difference (request : AreaRequest words fixed
  error floor)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : request.index ≤ stage) :
    let walk := grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)
    Data.Gaussian.Norm.Basic.normSq (Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices walk 0) -
      Topology.Mesh.RetracingWords.wordArea (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
        lifted.mesh readings.values) (lifted.edges.indexedEdges lifted.vertices walk 1)) ≤ 10 * (error / 32) := by
  intro walk
  have zeroLater := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸
    later))
  have oneLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸
    later))
  have oppositeLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have zero := request.zero.chart.accurate readings
    ((Data.Nat.Order.le_max_right _ _).trans (request.zero.index_eq ▸ zeroLater))
  have one := request.one.chart.accurate readings
    ((Data.Nat.Order.le_max_right _ _).trans (request.one.index_eq ▸ oneLater))
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.sources_project words.paired] at zero one
  have opposite := request.opposite.accurate readings oppositeLater 0 1 (by decide)
  let left := Topology.Mesh.RetracingWords.wordArea
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (lifted.edges.indexedEdges lifted.vertices walk 0)
  let right := Topology.Mesh.RetracingWords.wordArea
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (lifted.edges.indexedEdges lifted.vertices walk 1)
  let leftSource := Path.IncrementArea.pathArea ((words.paired.sources 0).map (fun source => source.increment
    readings.values))
  let rightSource := Path.IncrementArea.pathArea ((words.paired.sources 1).map (fun source => source.increment
    readings.values))
  have partNonnegative := (Fraction.Order.Field.div_pos_direct request.positive (by
      decide +kernel : (0 : Fraction.Rational) < 32)).le
  have smaller : error / 32 / 4 ≤ error / 32 := Fraction.Order.Field.divide_le_self partNonnegative (by decide)
  have oldBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have reversed : Data.Gaussian.Norm.Basic.normSq (left - leftSource) ≤ error / 32 := by
    rw [show left - leftSource = -(leftSource - left) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact oldBound (zero.trans smaller)
  have middle : Data.Gaussian.Norm.Basic.normSq (leftSource - right) ≤ 2 * (error / 32 + error / 32) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_via leftSource rightSource right).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (oldBound
        opposite) (oldBound (one.trans smaller))) (by decide))
  exact ((Gaussian.Norm.Bounds.normSq_sub_le_via left leftSource right).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct reversed
      middle) (by decide))).trans_eq (by ring1)

/-- The original compiler may arrive on either new-grid sheet. Opposite
sheet comparison is paid, rather than identifying the two polygon areas. -/
theorem accurate (request : AreaRequest words fixed error floor) (sheet
  : Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values)
      {region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face}
    (balance : CutBalance region words surface)
    (sample : Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample balance.complete.pairing
      surface.energyValues)
    (zero : Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback words.zero surface.sewn.values)
    (one : Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback words.one surface.sewn.values) (later :
      request.index ≤ stage) :
    let polygon := Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)
    Data.Gaussian.Norm.Basic.normSq ((balance.selected.area - sample.jumpSum - sample.defectSum - zero.correction -
      one.correction) -
      (polygon + polygon)) ≤ error := by
  intro polygon
  rw [balance.corrected_area sample zero one]
  have zeroLater := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸
    later))
  have oneLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸
    later))
  have zeroBound := request.zero.accurate readings surface zero zeroLater
  have oneBound := request.one.accurate readings surface one oneLater
  let canonical := fun sheet => Topology.Mesh.RetracingWords.wordArea
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
    (lifted.edges.indexedEdges lifted.vertices
    (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)
  have sumBound : Data.Gaussian.Norm.Basic.normSq ((zero.raw - zero.correction) + (one.raw - one.correction) -
    (canonical 0 + canonical 1)) ≤
      4 * (error / 32) := by
    have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct zeroBound
        oneBound) (by decide))
    rw [show (zero.raw - zero.correction - canonical 0) + (one.raw - one.correction - canonical 1) =
      (zero.raw - zero.correction) + (one.raw - one.correction) - (canonical 0 + canonical 1) by ring1] at estimate
    exact estimate.trans_eq (by ring1)
  have difference := request.canonical_difference readings later
  have either : ∀ sheet : Fin 2, Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical sheet +
    canonical sheet)) ≤ 10 * (error / 32) := by
    refine Data.Fin.casesByRecursion ?_ (Data.Fin.casesByRecursion ?_ (fun empty => Fin.elim0 empty))
    · change Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical 0 + canonical 0)) ≤ 10 * (error
        / 32)
      rw [show canonical 0 + canonical 1 - (canonical 0 + canonical 0) = -(canonical 0 - canonical 1) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
      exact difference
    · change Data.Gaussian.Norm.Basic.normSq (canonical 0 + canonical 1 - (canonical 1 + canonical 1)) ≤ 10 * (error
        / 32)
      rw [show canonical 0 + canonical 1 - (canonical 1 + canonical 1) = canonical 0 - canonical 1 by ring1]
      exact difference
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via ((zero.raw - zero.correction) + (one.raw - one.correction))
    (canonical 0 + canonical 1) (canonical sheet + canonical sheet)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sumBound
        (either sheet)) (by decide))
  have partNonnegative := (Fraction.Order.Field.div_pos_direct request.positive (by
      decide +kernel : (0 : Fraction.Rational) < 32)).le
  have paid : 2 * (4 * (error / 32) + 10 * (error / 32)) ≤ error := by
    calc
      _ = 28 * (error / 32) := by ring1
      _ ≤ 32 * (error / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        partNonnegative
      _ = error := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  exact estimate.trans paid

end AreaRequest

namespace AreaRequest

/-- The original regular region consumes an entirely constructed sewing
comparison, pairing sample and both offset readbacks. -/
theorem area_accurate (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (sheet : Fin
      2)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let words := Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.build face lifted
    let request := build words fixed error positive floor
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch readings.values),
        request.index ≤ stage →
      let balance := CutBalance.build region words surface
      let sample := Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample.build
        balance.complete.pairing surface.energyValues
      let zero := Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback.build words.zero surface.sewn.values
      let one := Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback.build words.one surface.sewn.values
      let polygon := Topology.Mesh.RetracingWords.wordArea
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
        (lifted.edges.indexedEdges lifted.vertices
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)
      Data.Gaussian.Norm.Basic.normSq ((balance.selected.area - sample.jumpSum - sample.defectSum - zero.correction
        - one.correction) -
        (polygon + polygon)) ≤ error := by
  intro words request stage shared readings surface later balance sample zero one polygon
  exact request.accurate sheet readings surface balance sample zero one later

end AreaRequest

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular
