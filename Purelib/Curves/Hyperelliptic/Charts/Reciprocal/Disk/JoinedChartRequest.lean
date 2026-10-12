module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

public section

/-!
# Requested chart comparison for an actual joined exterior parent

All cell counts and source and spatial floors are paid before sampling.
One later chart stage supplies both the polygon vertices and the original
joined endpoint readings. The complete corrected parent meets the requested
source total and area bounds, without a caller-supplied path equality.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

set_option genInjectivity false in
/-- A paid chart replacement of the original joined exterior parent.

Retain both original requests, their common model stage and the required spatial depth. -/
structure JoinedChartRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular
  cover) (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original join request with the retained total target and quarter area target. -/ joined :
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent.JoinedRequest prepared totalTarget (areaTarget / 4) floor
  /-- The original chart replacement request with its quarter area target. -/ replacement :
    ChartReplacementRequest prepared (areaTarget / 4) floor
  /-- The common model stage for the original join and replacement charts. -/ index : Nat
  /-- The model stage is exactly the maximum of the two original requirements. -/ index_eq : index = max joined.index
    replacement.charts.maximum
  /-- The original chart replacement's required spatial depth. -/ depth : Nat
  /-- The retained depth equals the actual replacement-chart maximum. -/ depth_eq : depth =
    replacement.charts.depthMaximum

-- Preserve the original constructor API on this nominal parent.

constructive_injectivity JoinedChartRequest

namespace JoinedChartRequest

/-- Allocate the positive area target between the original join and chart replacement, then retain their shared stage
and depth.

Each original request receives the same quarter area target. The retained
maximum model stage pays both requests, while the replacement charts determine
the required spatial depth. -/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
    JoinedChartRequest prepared totalTarget areaTarget floor :=
      by
  have quarterPositive := Fraction.Order.Field.div_pos_direct areaPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  let joined := Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent.JoinedRequest.build prepared totalTarget (areaTarget /
    4) totalPositive quarterPositive floor
  let replacement := ChartReplacementRequest.build prepared
    (areaTarget / 4) quarterPositive floor
  exact ⟨joined, replacement, max joined.index replacement.charts.maximum, rfl, replacement.charts.depthMaximum, rfl⟩

variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {totalTarget
  areaTarget : Normalization.InverseRootPolynomial.Coordinate} {floor index minimum : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {request : JoinedChartRequest prepared
    totalTarget areaTarget floor}

/-- The retained common model stage meets the original requested floor. -/
theorem floor_le (request : JoinedChartRequest prepared
  totalTarget areaTarget floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact request.joined.floor_le.trans (Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- The actual replacement chart plans for the supplied original cap sample and a sufficient shared reading stage. -/
structure Plan (request : JoinedChartRequest prepared
  totalTarget areaTarget floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (minimum : Nat) where
  /-- The actual original chart plans for the retained cap sample. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum request.replacement.charts
  /-- The common numerical reading stage. -/ stage : Nat
  /-- The retained stage is exactly the maximum of the joined reading requirement and original chart maximum. -/
    stage_eq : stage = max request.joined.readingIndex charts.maximum

-- Preserve the original constructor API on this nominal parent.

constructive_injectivity Plan

namespace Plan

/-- Prepare the original replacement charts once and retain a reading stage sufficient for both charts and joined
endpoints.

The supplied cap sample and minimum are used by the original chart-plan
builder. The shared maximum stage also pays the joined endpoint request. -/
@[expose] def build (request : JoinedChartRequest prepared
  totalTarget areaTarget floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (minimum : Nat) :
      Plan request capSample minimum :=
  let charts := Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.build capSample minimum
    request.replacement.charts
  ⟨charts, max request.joined.readingIndex charts.maximum, rfl⟩

variable {depth readingIndex : Nat} {originalTarget : Normalization.InverseRootPolynomial.Coordinate}
  {original : Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Cover.AreaRequest cover depth originalTarget}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential original.index box}

set_option genInjectivity false in
/-- The complete original joined-parent comparison with its actual replacement vertices.

Retain shared endpoint-reading identities and the paid total and area bounds. -/
structure Evaluation (original : Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Cover.AreaRequest cover depth
  originalTarget)
    {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential original.index box}
    (plan : Plan request capSample minimum)
      (readingIndex : Nat) where
  /-- The original joined-parent evaluation with its retained source polynomial cells. -/ compared :
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent.JoinedRequest.Evaluation request.joined original capSample
    readingIndex
  /-- The actual replacement vertices read from those original cells. -/ vertices :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData readingIndex plan.charts
    compared.polynomial.cells
  /-- The retained source model is late enough for the original endpoint requests. -/ model_later :
    request.joined.endpoints.maximum ≤ original.index
  /-- The retained reading stage is late enough for the original endpoint requests. -/ reading_later :
    request.joined.endpoints.readingMaximum ≤ readingIndex
  /-- The retained reading stage is late enough for the original junction requests. -/ junction_later :
    request.joined.junctions.maximum ≤ readingIndex
  /-- The joined comparison uses exactly the retained chart endpoint readings. -/ readings_eq : compared.readings =
    plan.charts.endpointReadings compared.polynomial.cells vertices request.joined.endpoints
    model_later reading_later
  /-- The actual chart replacement on the original polynomial cells, vertices and endpoint readings. -/ replacement :
    Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement plan.charts compared.polynomial.cells vertices
    request.joined.endpoints
    compared.readings compared.firstValue
  /-- The original source total and actual replacement total differ by less than the retained total target. -/
    total_close : Data.Gaussian.Norm.Basic.normSq (compared.polynomial.left.total - replacement.summary.total) <
    totalTarget
  /-- The original source area and actual replacement area differ by less than the retained area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (compared.polynomial.left.area - replacement.summary.area) < areaTarget

-- Preserve the original constructor API on this nominal parent.

constructive_injectivity Evaluation

/-- Evaluate the complete retained parent at any later certified source,
fine-mesh and reading stage. Every joining equality is constructed internally. -/
@[expose] def evaluate (plan : Plan request
  capSample minimum)
    (later : request.index ≤ original.index) (fineLater : request.depth ≤ depth)
    (readingIndex : Nat) (readingLater : plan.stage ≤ readingIndex) :
      Evaluation original plan
      readingIndex := by
  have indices := request.index_eq.ge.trans later
  have joinedLater := (Data.Nat.Order.le_max_left _ _).trans indices
  have joinedIndices := request.joined.index_eq.ge.trans joinedLater
  have stages := plan.stage_eq.ge.trans readingLater
  have joinedReadingLater := (Data.Nat.Order.le_max_left _ _).trans stages
  have pairReadingLater := (Data.Nat.Order.le_max_left _ _).trans (request.joined.readingIndex_eq.ge.trans
    joinedReadingLater)
  let polynomial := request.joined.polynomial.evaluate original capSample ((Data.Nat.Order.le_max_left _ _).trans
    joinedIndices)
  let vertices := plan.charts.evaluate polynomial.cells ((Data.Nat.Order.le_max_right _ _).trans indices)
    (request.depth_eq.ge.trans fineLater) ((Data.Nat.Order.le_max_right _ _).trans stages)
  let readings := plan.charts.endpointReadings polynomial.cells vertices request.joined.endpoints
    ((Data.Nat.Order.le_max_right _ _).trans joinedIndices) pairReadingLater
  let joined := request.joined.evaluateWithReadings polynomial readings joinedReadingLater
  let replacement := Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts.Replacement.build plan.charts polynomial.cells
    vertices request.joined.endpoints readings joined.firstValue
  have replacementError : Data.Gaussian.Norm.Basic.normSq (joined.joined.summary.area - replacement.summary.area) <
    areaTarget / 4 := by
    rw [show joined.joined.summary.area - replacement.summary.area =
      -(replacement.summary.area - joined.joined.summary.area) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact (replacement.area_error joined.joined).trans_lt request.replacement.paid
  refine ⟨joined, vertices, (Data.Nat.Order.le_max_right _ _).trans joinedIndices, pairReadingLater,
    (Data.Nat.Order.le_max_right _ _).trans (request.joined.readingIndex_eq.ge.trans joinedReadingLater), rfl,
      replacement, ?_, ?_⟩
  · rw [replacement.total_preserved joined.joined]
    exact joined.total_close
  · exact (Gaussian.Norm.Bounds.normSq_sub_le_via polynomial.left.area joined.joined.summary.area
      replacement.summary.area).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct joined.area_close replacementError)).trans_eq (by
        rw [show 2 * (areaTarget / 4 + areaTarget / 4) = areaTarget / 4 * 4 by ring1]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Plan
end JoinedChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
