import FTA.ExactIsolation
import FTA.CCLBoundaryStrictCell
import FTA.CCLMetricTrack

/-!
# Metric CCL states for the finite isolated root family

Exact isolation returns exactly the requested number of pairwise separated
winding-one tracks.  This module equips each initial track with the revised
metric CCL state and computes an explicit rational projective gap for every
pair.  The same stored gap is transported through arbitrary later box and
cylinder refinements and feeds the controller-level keep-apart theorem.
-/

namespace FTA
namespace CCLMetricFamily

open CCL
open FTA.CCLMetricTrack

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The coarse metric CCL state attached to one exactly isolated winding-one
root track.  Its initial word is empty and its cylinder radius is the universal
unit bound. -/
def initialStateAt
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (index : Fin count) :
    CCLMetricTrack.State p ambient :=
  CCLMetricTrack.State.ofCore
    (CCLCoupledTrack.PersistentState.ofWindingOne
      (output.trackAt index).initial)

theorem initialStateAt_word_nil
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (index : Fin count) :
    (initialStateAt output index).core.word = [] := by
  rfl

theorem initialStateAt_cylinderRadiusSq
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (index : Fin count) :
    (initialStateAt output index).cylinder.radiusSq = 1 := by
  rfl

/-- Materialize the proposition-level box separation from exact isolation as
the executable rational gap consumed by the metric invariant. -/
def initialGap
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) :
    RegionGap (initialStateAt output left).core.numerical.box
      (initialStateAt output right).core.numerical.box := by
  apply RegionGap.compute
  change (output.trackAt left).initial.box.Separated
    (output.trackAt right).initial.box
  exact output.trackAt_pairwiseSeparated left right distinct

/-- Preserve the initially computed pair gap through arbitrary independent
metric-state refinements. -/
def refinedGap
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (leftIndex rightIndex : Fin count)
    (distinct : leftIndex ≠ rightIndex)
    {left right : CCLMetricTrack.State p ambient}
    (leftRefines : left.Refines (initialStateAt output leftIndex))
    (rightRefines : right.Refines (initialStateAt output rightIndex)) :
    RegionGap left.core.numerical.box right.core.numerical.box :=
  (initialGap output leftIndex rightIndex distinct).refine
    leftRefines.1 rightRefines.1

theorem affineWeightBound_le_of_refines
    {small large : RatBox} (refines : small.Refines large) :
    CCLChordalEnvelope.affineWeightBound small ≤
      CCLChordalEnvelope.affineWeightBound large := by
  have radiusLe := CCLBoundaryStrictCell.RatBox.coordinateRadius_le_of_refines
    refines
  have squareLe : small.coordinateRadius ^ 2 ≤ large.coordinateRadius ^ 2 :=
    (sq_le_sq₀ small.coordinateRadius_nonneg
      large.coordinateRadius_nonneg).2 radiusLe
  unfold CCLChordalEnvelope.affineWeightBound
  linarith

/-- Refining either affine box can only improve the rational projective gap
obtained from a fixed coordinate separation. -/
theorem chordalGapSq_le_of_refines
    {smallLeft largeLeft smallRight largeRight : RatBox}
    (leftRefines : smallLeft.Refines largeLeft)
    (rightRefines : smallRight.Refines largeRight)
    (coordinateGap : ℚ) :
    CCLChordalEnvelope.chordalGapSq largeLeft largeRight coordinateGap ≤
      CCLChordalEnvelope.chordalGapSq smallLeft smallRight coordinateGap := by
  have leftWeight := affineWeightBound_le_of_refines leftRefines
  have rightWeight := affineWeightBound_le_of_refines rightRefines
  have denominatorLe :
      CCLChordalEnvelope.affineWeightBound smallLeft *
          CCLChordalEnvelope.affineWeightBound smallRight ≤
        CCLChordalEnvelope.affineWeightBound largeLeft *
          CCLChordalEnvelope.affineWeightBound largeRight :=
    mul_le_mul leftWeight rightWeight
      (CCLChordalEnvelope.affineWeightBound_pos smallRight).le
      (CCLChordalEnvelope.affineWeightBound_pos largeLeft).le
  unfold CCLChordalEnvelope.chordalGapSq
  exact div_le_div_of_nonneg_left (sq_nonneg coordinateGap)
    (mul_pos (CCLChordalEnvelope.affineWeightBound_pos smallLeft)
      (CCLChordalEnvelope.affineWeightBound_pos smallRight)) denominatorLe

/-- Positive per-state component-error budget computed once from the initial
pair of isolated regions.  The factor `32` leaves a strict factor-two margin
after summing the two states and applying the square-root-free triangle bound. -/
def pairComponentErrorRequest
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) : ℚ :=
  CCLChordalEnvelope.chordalGapSq
      (initialStateAt output left).core.numerical.box
      (initialStateAt output right).core.numerical.box
      (initialGap output left right distinct).coordinateGap / 32

theorem pairComponentErrorRequest_pos
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) :
    0 < pairComponentErrorRequest output left right distinct := by
  exact div_pos
    (CCLChordalEnvelope.chordalGapSq_pos _ _
      (initialGap output left right distinct).positive) (by norm_num)

/-- Positive box accuracy used to spend at most half of one pair budget on
the squared winding-box diagonal.  `min 1` avoids any square-root operation. -/
def pairBoxAccuracyRequest
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) : ℚ :=
  min 1 (pairComponentErrorRequest output left right distinct / 2)

/-- The other half of the pair budget is assigned directly to the squared
chordal cylinder radius. -/
def pairCylinderAccuracyRequest
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) : ℚ :=
  pairComponentErrorRequest output left right distinct / 2

theorem pairBoxAccuracyRequest_pos
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) :
    0 < pairBoxAccuracyRequest output left right distinct := by
  apply lt_min
  · norm_num
  · exact div_pos (pairComponentErrorRequest_pos output left right distinct)
      (by norm_num)

theorem pairCylinderAccuracyRequest_pos
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) :
    0 < pairCylinderAccuracyRequest output left right distinct :=
  div_pos (pairComponentErrorRequest_pos output left right distinct)
    (by norm_num)

private theorem min_one_half_sq_add_half_le
    {budget : ℚ} (positive : 0 < budget) :
    min 1 (budget / 2) ^ 2 + budget / 2 ≤ budget := by
  have halfPositive : 0 < budget / 2 := div_pos positive (by norm_num)
  by_cases halfLeOne : budget / 2 ≤ 1
  · rw [min_eq_right halfLeOne]
    nlinarith [sq_nonneg (budget / 2),
      mul_nonneg (by linarith : 0 ≤ budget / 2)
        (by linarith : 0 ≤ 1 - budget / 2)]
  · have oneLeHalf : 1 ≤ budget / 2 :=
      (le_of_lt (lt_of_not_ge halfLeOne))
    rw [min_eq_left oneLeHalf]
    norm_num
    linarith

/-- Meeting the two square-root-free accuracy requests is sufficient for one
state's full component error to fit below its stored pair budget. -/
theorem componentError_le_pairComponentErrorRequest
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (left right : Fin count)
    (distinct : left ≠ right) (state : CCLMetricTrack.State p ambient)
    (boxAccurate : state.core.numerical.box.diagonalSq ≤
      pairBoxAccuracyRequest output left right distinct ^ 2)
    (cylinderAccurate : state.cylinder.radiusSq ≤
      pairCylinderAccuracyRequest output left right distinct) :
    state.componentError ≤
      pairComponentErrorRequest output left right distinct := by
  unfold CCLMetricTrack.State.componentError
  apply (add_le_add boxAccurate cylinderAccurate).trans
  exact min_one_half_sq_add_half_le
    (pairComponentErrorRequest_pos output left right distinct)

/-- The precomputed initial request remains below the available projective
gap after arbitrary independent box and cylinder refinements. -/
theorem refined_error_sum_lt_gap_of_componentError_le_request
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : CCLMetricTrack.State p ambient}
    (leftRefines : left.Refines (initialStateAt output leftIndex))
    (rightRefines : right.Refines (initialStateAt output rightIndex))
    (leftError : left.componentError ≤
      pairComponentErrorRequest output leftIndex rightIndex distinct)
    (rightError : right.componentError ≤
      pairComponentErrorRequest output leftIndex rightIndex distinct) :
    8 * (left.componentError + right.componentError) <
      CCLChordalEnvelope.chordalGapSq left.core.numerical.box
        right.core.numerical.box
        (refinedGap output leftIndex rightIndex distinct leftRefines
          rightRefines).coordinateGap := by
  let initialProjectiveGap := CCLChordalEnvelope.chordalGapSq
    (initialStateAt output leftIndex).core.numerical.box
    (initialStateAt output rightIndex).core.numerical.box
    (initialGap output leftIndex rightIndex distinct).coordinateGap
  have initialProjectiveGapPositive : 0 < initialProjectiveGap :=
    CCLChordalEnvelope.chordalGapSq_pos _ _
      (initialGap output leftIndex rightIndex distinct).positive
  have errorSum : left.componentError + right.componentError ≤
      2 * (initialProjectiveGap / 32) := by
    calc
      left.componentError + right.componentError ≤
          pairComponentErrorRequest output leftIndex rightIndex distinct +
            pairComponentErrorRequest output leftIndex rightIndex distinct :=
        add_le_add leftError rightError
      _ = 2 * (initialProjectiveGap / 32) := by
        simp only [pairComponentErrorRequest, initialProjectiveGap]
        ring
  have scaledError : 8 * (left.componentError + right.componentError) <
      initialProjectiveGap := by
    calc
      8 * (left.componentError + right.componentError) ≤
          8 * (2 * (initialProjectiveGap / 32)) :=
        mul_le_mul_of_nonneg_left errorSum (by norm_num)
      _ < initialProjectiveGap := by
        linarith
  exact scaledError.trans_le
    (chordalGapSq_le_of_refines leftRefines.1 rightRefines.1
      (initialGap output leftIndex rightIndex distinct).coordinateGap)

/-- Pairwise keep-apart for two later states in the exact isolated family.
Only the explicit rational component-error comparison remains to be checked. -/
theorem represented_points_not_equivalent_of_refined_error_lt_gap
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count) (leftIndex rightIndex : Fin count)
    (distinct : leftIndex ≠ rightIndex)
    {left right : CCLMetricTrack.State p ambient}
    (leftRefines : left.Refines (initialStateAt output leftIndex))
    (rightRefines : right.Refines (initialStateAt output rightIndex))
    (thin :
      let gap := refinedGap output leftIndex rightIndex distinct
        leftRefines rightRefines
      8 * (left.componentError + right.componentError) <
        CCLChordalEnvelope.chordalGapSq left.core.numerical.box
          right.core.numerical.box gap.coordinateGap)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented left.core.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented right.core.word rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  exact represented_points_not_equivalent_of_component_error_lt_gap
    (refinedGap output leftIndex rightIndex distinct leftRefines rightRefines)
    thin leftRepresented rightRepresented

/-- Computed-request form of pairwise keep-apart: once both independently
refined states meet the stored per-pair component budget, no extra numerical
inequality is required from the caller. -/
theorem represented_points_not_equivalent_of_componentError_le_request
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : CCLMetricTrack.State p ambient}
    (leftRefines : left.Refines (initialStateAt output leftIndex))
    (rightRefines : right.Refines (initialStateAt output rightIndex))
    (leftError : left.componentError ≤
      pairComponentErrorRequest output leftIndex rightIndex distinct)
    (rightError : right.componentError ≤
      pairComponentErrorRequest output leftIndex rightIndex distinct)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented left.core.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented right.core.word
      rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  apply represented_points_not_equivalent_of_refined_error_lt_gap output
    leftIndex rightIndex distinct leftRefines rightRefines
  · exact refined_error_sum_lt_gap_of_componentError_le_request output
      leftIndex rightIndex distinct leftRefines rightRefines leftError
        rightError
  · exact leftRepresented
  · exact rightRepresented

/-- Direct request-facing keep-apart theorem.  Independent total box and
cylinder contractions at the two computed rational accuracies suffice to keep
all represented rational realizations projectively distinct. -/
theorem represented_points_not_equivalent_of_pair_accuracy_requests
    {p : GaussianPolynomial} {ambient : RatBox} {count : ℕ}
    (output : ExactIsolation.Output p ambient count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : CCLMetricTrack.State p ambient}
    (leftRefines : left.Refines (initialStateAt output leftIndex))
    (rightRefines : right.Refines (initialStateAt output rightIndex))
    (leftBoxAccurate : left.core.numerical.box.diagonalSq ≤
      pairBoxAccuracyRequest output leftIndex rightIndex distinct ^ 2)
    (leftCylinderAccurate : left.cylinder.radiusSq ≤
      pairCylinderAccuracyRequest output leftIndex rightIndex distinct)
    (rightBoxAccurate : right.core.numerical.box.diagonalSq ≤
      pairBoxAccuracyRequest output leftIndex rightIndex distinct ^ 2)
    (rightCylinderAccurate : right.cylinder.radiusSq ≤
      pairCylinderAccuracyRequest output leftIndex rightIndex distinct)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented left.core.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented right.core.word
      rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  apply represented_points_not_equivalent_of_componentError_le_request output
    leftIndex rightIndex distinct leftRefines rightRefines
  · exact componentError_le_pairComponentErrorRequest output leftIndex
      rightIndex distinct left leftBoxAccurate leftCylinderAccurate
  · exact componentError_le_pairComponentErrorRequest output leftIndex
      rightIndex distinct right rightBoxAccurate rightCylinderAccurate
  · exact leftRepresented
  · exact rightRepresented

end CCLMetricFamily
end FTA
