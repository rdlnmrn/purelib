module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
public import Purelib.Integration.Path.IncrementAreaReplacement
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

/-!
# Chart polygons inside the actual corrected cap blocks

Restore the original raw endpoint totals with two certified small edges.
The existing incoming connector and endpoint corrections are then retained
literally. The whole corrected block has exactly its original total; its
full area difference is paid independently of the incoming connector.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells (CorrectedCell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target
    floor}
  {charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh request.mesh capSample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

/-- The two endpoint-correction edges fit the retained slope-scaled tolerance budget when tolerance is at most one. -/
theorem correction_cost {slope tolerance : InverseRootPolynomial.Coordinate} (slopeNonnegative : 0 ≤ slope)
    (nonnegative : 0 ≤ tolerance) (small : tolerance ≤ 1) :
    24 * (4 * tolerance) * (2 * (slope + 16)) + 16 * (4 * tolerance) ^ 2 ≤
      512 * (slope + 16) * tolerance := by
  have first : 0 ≤ 64 * tolerance * (5 * slope + 76) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
      nonnegative)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 5)
      slopeNonnegative)
      (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 76))
  have second : 0 ≤ 256 * tolerance * (1 - tolerance) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 256)
      nonnegative)
    (Fraction.Order.Arithmetic.sub_nonneg_direct small)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg first second).trans_eq (by ring1)

/-- The original chart request's paid cost bounds the retained endpoint-correction coefficient. -/
theorem cost_lower (request : ChartAreaRequest.AreaRequest comparison owners target floor) :
    512 * (request.spatial.bounds.slope + 16) ≤ request.cost := by
  have countPositive : 0 < request.count := by rw [request.count_eq]; exact Nat.pow_pos (by decide)
  have countLe : (1 : InverseRootPolynomial.Coordinate) ≤ (request.count : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct countPositive
  have powerLe : (1 : InverseRootPolynomial.Coordinate) ≤ (request.count : InverseRootPolynomial.Coordinate) ^ 4 := by
    simpa only [one_pow, -eq_self, -iff_self] using Fraction.Order.Arithmetic.pow_le_pow_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) countLe 4
  have nonnegative : 0 ≤ 512 * (request.spatial.bounds.slope + 16) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 512) (add_nonneg
      request.spatial.bounds.slope_nonnegative (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16))
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerLe nonnegative
  calc
    _ = (512 * (request.spatial.bounds.slope + 16)) * 1 := by ring1
    _ ≤ (512 * (request.spatial.bounds.slope + 16)) * (request.count : InverseRootPolynomial.Coordinate) ^ 4 :=
      multiplied
    _ = request.cost := by rw [request.cost_eq]; ring1

/-- The already paid chart tolerance is below the original cell allowance. -/
theorem tolerance_le_target (request : ChartAreaRequest.AreaRequest comparison owners target floor) : request.tolerance
  ≤ target := by
  have shifted : (16 : InverseRootPolynomial.Coordinate) ≤ request.spatial.bounds.slope + 16 := le_add_of_nonneg_left
    request.spatial.bounds.slope_nonnegative
  have oneLe : (1 : InverseRootPolynomial.Coordinate) ≤ request.cost :=
    (show (1 : InverseRootPolynomial.Coordinate) ≤ 512 * 16 by decide +kernel).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct shifted (by decide +kernel)).trans (cost_lower
        request))
  have quarter : request.tolerance < target / 4 :=
    ((show request.tolerance = 1 * request.tolerance by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe request.positive.le)).trans_lt request.paid
  have targetNonnegative : 0 ≤ target / 4 := request.positive.le.trans quarter.le
  have enlarged : target / 4 ≤ target := by
    exact ((show target / 4 = (target / 4) * 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4) targetNonnegative)).trans_eq
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  exact quarter.le.trans enlarged

/-- The original cap summary total equals the exact retained last-minus-first source values. -/
theorem raw_total (evaluated : AreaRequest.Evaluation charts original stage) :
    original.capSummary.total = evaluated.vertices.last.sourceValue - evaluated.vertices.first.sourceValue := by
  rw [original.cap_total, original.sample.increment_eq, original.sample.firstValue_eq, original.sample.lastValue_eq,
    evaluated.vertices.first.source_eq, evaluated.vertices.last.source_eq]

/-- The actual chart-path total satisfies the retained source-slope and unit-tolerance magnitude ceiling. -/
theorem chart_total_bound (evaluated : AreaRequest.Evaluation charts original stage) :
    Data.Gaussian.Norm.Basic.normSq evaluated.vertices.path.chart.total ≤ 2 * (request.spatial.bounds.slope +
      16) := by
  let segment := Segment.build evaluated.vertices.first evaluated.vertices.last cell.ordered.le
  have sourceBound := Segment.source_bound segment request.spatial.bounds source
  change Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.last.sourceValue -
    evaluated.vertices.first.sourceValue) ≤ request.spatial.bounds.slope at sourceBound
  rw [← raw_total evaluated] at sourceBound
  have errorLe : Data.Gaussian.Norm.Basic.normSq (original.capSummary.total -
    evaluated.vertices.path.chart.total) ≤ 16 :=
    evaluated.total_error.le.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.small (by
      decide)).trans_eq
      (Fraction.Field.mul_one_direct _))
  rw [show evaluated.vertices.path.chart.total = original.capSummary.total -
    (original.capSummary.total - evaluated.vertices.path.chart.total) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add sourceBound errorLe) (by decide))

set_option genInjectivity false in
/-- The actual chart polygon bracketed by two retained endpoint correction edges.

Its total is exactly the original cap total, while the additional full-area discrepancy is paid by the original chart
request. -/
structure Restored (evaluated : AreaRequest.Evaluation charts original stage) where
  /-- The actual correction from the original first source value to the first cached chart value. -/ first :
    InverseRootPolynomial.Gaussian
  /-- The first correction is exactly the retained chart-minus-source endpoint difference. -/ first_eq : first =
    evaluated.vertices.first.chartValue - evaluated.vertices.first.sourceValue
  /-- The actual correction from the last cached chart value to the original last source value. -/ last :
    InverseRootPolynomial.Gaussian
  /-- The last correction is exactly the retained source-minus-chart endpoint difference. -/ last_eq : last =
    evaluated.vertices.last.sourceValue - evaluated.vertices.last.chartValue
  /-- The cached complete bracketed increment-path summary. -/ summary : IncrementArea.Summary (first ::
    (evaluated.vertices.path.chartPath ++ [last]))
  /-- The summary is exactly the bracket operation on the retained inner summary and endpoint corrections. -/ summary_eq
    : summary = IncrementAreaReplacement.bracket evaluated.vertices.path.chart first last
  /-- The corrected summary preserves the exact total of its original retained cap block. -/ total_eq : summary.total =
    original.capSummary.total
  /-- The two retained endpoint corrections change the chart area by less than one quarter of the original target. -/
    correction_error : Data.Gaussian.Norm.Basic.normSq (summary.area - evaluated.vertices.path.chart.area) <
    target / 4
  /-- The full corrected area differs from the original cap block within the paid combined chart and endpoint budget. -/
    area_error : Data.Gaussian.Norm.Basic.normSq (original.capSummary.area - summary.area) < 2 * (target +
    target / 4)

constructive_injectivity Restored

namespace Restored

/-- Cache both actual endpoint corrections and their bracketed chart summary, retaining exact original total and paid
area bounds. -/
@[expose] def build (evaluated : AreaRequest.Evaluation charts original stage) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored evaluated := by
  let first := evaluated.vertices.first.chartValue - evaluated.vertices.first.sourceValue
  let last := evaluated.vertices.last.sourceValue - evaluated.vertices.last.chartValue
  let summary := IncrementAreaReplacement.bracket evaluated.vertices.path.chart first last
  have firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ 4 * request.tolerance := by
    change Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.first.chartValue -
      evaluated.vertices.first.sourceValue) ≤ _
    rw [show evaluated.vertices.first.chartValue - evaluated.vertices.first.sourceValue =
      -(evaluated.vertices.first.sourceValue - evaluated.vertices.first.chartValue) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
    exact evaluated.vertices.first.accurate.le
  have lastBound : Data.Gaussian.Norm.Basic.normSq last ≤ 4 * request.tolerance :=
    evaluated.vertices.last.accurate.le
  have correction : Data.Gaussian.Norm.Basic.normSq (summary.area - evaluated.vertices.path.chart.area) <
    target / 4 :=
    (((IncrementAreaReplacement.bracket_area_error evaluated.vertices.path.chart first last firstBound lastBound
      (chart_total_bound evaluated)).trans
      (correction_cost request.spatial.bounds.slope_nonnegative request.positive.le request.small)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (cost_lower request) request.positive.le)).trans_lt
        request.paid
  have totalEq : summary.total = original.capSummary.total := by
    rw [IncrementAreaReplacement.bracket_total, evaluated.vertices.path.chart_total, raw_total evaluated]
    dsimp only [first, last]
    ring1
  have reversed : Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.path.chart.area - summary.area) < target
    / 4 := by
    rw [show evaluated.vertices.path.chart.area - summary.area = -(summary.area - evaluated.vertices.path.chart.area) by
      ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact correction
  have areaError := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via original.capSummary.area
    evaluated.vertices.path.chart.area summary.area).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct evaluated.area_error reversed))
  exact ⟨first, rfl, last, rfl, summary, rfl, totalEq, correction, areaError⟩

variable {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts
  original stage} {pairTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {pairFloor : Nat}
  {pairRequest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest owners.bounds pairTarget
    pairFloor}
  {reading : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation pairRequest
    original.sample stage} {entry : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

set_option genInjectivity false in
/-- The restored chart path inside the original corrected cap block.

The original incoming connector and endpoint correction are retained exactly, so full-area replacement costs no
additional incoming-connector allowance. -/
structure Corrected (restored : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored evaluated)
  (originalBlock : CorrectedCells.CorrectedCell original reading entry) where
  /-- The cached complete bracketed increment-path summary. -/ summary : IncrementArea.Summary (originalBlock.first ::
    ((restored.first :: (evaluated.vertices.path.chartPath ++ [restored.last])) ++ [originalBlock.last]))
  /-- The summary is exactly the bracket operation on the retained inner summary and endpoint corrections. -/ summary_eq
    : summary = IncrementAreaReplacement.bracket restored.summary originalBlock.first originalBlock.last
  /-- The corrected summary preserves the exact total of its original retained cap block. -/ total_eq : summary.total =
    originalBlock.summary.total
  /-- The full corrected area differs from the original cap block within the paid combined chart and endpoint budget. -/
    area_error : Data.Gaussian.Norm.Basic.normSq (originalBlock.summary.area - summary.area) < 2 * (target +
    target / 4)

constructive_injectivity Corrected

/-- Bracket the restored chart summary with the original block's exact corrections while preserving its total and paid
area bound. -/
@[expose] def correct (restored : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored evaluated)
  (originalBlock : CorrectedCells.CorrectedCell original reading entry) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored.Corrected restored originalBlock := by
  let summary := IncrementAreaReplacement.bracket restored.summary originalBlock.first originalBlock.last
  have originalEq : originalBlock.summary = IncrementAreaReplacement.bracket original.capSummary originalBlock.first
    originalBlock.last := originalBlock.summary_eq
  have totalEq : summary.total = originalBlock.summary.total := by
    rw [originalEq, IncrementAreaReplacement.bracket_total, IncrementAreaReplacement.bracket_total, restored.total_eq]
  refine ⟨summary, rfl, totalEq, ?_⟩
  rw [originalEq]
  change Data.Gaussian.Norm.Basic.normSq ((IncrementAreaReplacement.bracket original.capSummary
    originalBlock.first originalBlock.last).area -
    (IncrementAreaReplacement.bracket restored.summary originalBlock.first originalBlock.last).area) < _
  rw [IncrementAreaReplacement.bracket_area_difference _ _ restored.total_eq.symm]
  exact restored.area_error

end Restored
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells
