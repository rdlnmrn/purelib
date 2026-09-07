import FTA.CCLBoundaryNeighborhood
import FTA.CCLRationalBoundaryProjection
import FTA.CentralBandGrid
import FTA.ConstructiveTrack

/-!
# Finite strict cells from quantitative CCL boundary exclusion

The completed clearance branch excludes every planned rational boundary from
one neighbourhood of its guarded winding box.  Rational boundary projection
turns failure of an interval sign check on a sufficiently small refinement
into a forbidden nearby exact boundary point.  All radii below are explicit
rational expressions.
-/

namespace FTA
namespace CCLBoundaryStrictCell

open CCL CCL.GaussianRat
open FTA.CCLBoundaryNeighborhood
open FTA.CCLBranchController
open FTA.CCLBranchEvidence
open FTA.CCLBranchPlan
open FTA.CCLBranchPartition
open FTA.CCLClearanceExclusion
open FTA.CCLCoupledController
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLHermitianBox
open FTA.CCLIntersectionSampler
open FTA.CCLRationalBoundaryProjection
open FTA.CCLRationalBoundaryProjection.PlannedBoundarySource
open FTA.AxisSafeCuts
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-! ## Box geometry and interval residuals -/

def strictInteriorMargin (inner outer : RatBox) : ℚ :=
  min (inner.xLower - outer.xLower)
    (min (outer.xUpper - inner.xUpper)
      (min (inner.yLower - outer.yLower)
        (outer.yUpper - inner.yUpper)))

theorem strictInteriorMargin_pos
    {inner outer : RatBox} (strict : StrictInterior inner outer) :
    0 < strictInteriorMargin inner outer := by
  unfold strictInteriorMargin
  apply lt_min
  · linarith [strict.left]
  · apply lt_min
    · linarith [strict.right]
    · apply lt_min <;> linarith [strict.bottom, strict.top]

theorem strictInteriorMargin_le_left (inner outer : RatBox) :
    strictInteriorMargin inner outer ≤ inner.xLower - outer.xLower := by
  exact min_le_left _ _

theorem strictInteriorMargin_le_right (inner outer : RatBox) :
    strictInteriorMargin inner outer ≤ outer.xUpper - inner.xUpper := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem strictInteriorMargin_le_bottom (inner outer : RatBox) :
    strictInteriorMargin inner outer ≤ inner.yLower - outer.yLower := by
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem strictInteriorMargin_le_top (inner outer : RatBox) :
    strictInteriorMargin inner outer ≤ outer.yUpper - inner.yUpper := by
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

private theorem abs_coordinate_sub_lt
    {point witness : QI} {margin : ℚ} (marginPositive : 0 < margin)
    (distance : normSq (point - witness) < margin ^ 2) :
    |point.re - witness.re| < margin ∧
      |point.im - witness.im| < margin := by
  have realSq : (point.re - witness.re) ^ 2 < margin ^ 2 := by
    dsimp only [normSq, sub_re, sub_im] at distance
    nlinarith [sq_nonneg (point.im - witness.im)]
  have imagSq : (point.im - witness.im) ^ 2 < margin ^ 2 := by
    dsimp only [normSq, sub_re, sub_im] at distance
    nlinarith [sq_nonneg (point.re - witness.re)]
  rw [← sq_abs] at realSq imagSq
  constructor <;> nlinarith [abs_nonneg (point.re - witness.re),
    abs_nonneg (point.im - witness.im)]

/-- A point closer than the squared strict-interior margin to an inner-box
member remains in the outer box. -/
theorem contains_of_normSq_sub_lt_strictInteriorMargin_sq
    {inner outer : RatBox} (strict : StrictInterior inner outer)
    {point witness : QI} (witnessInside : inner.Contains witness)
    (distance : normSq (point - witness) <
      strictInteriorMargin inner outer ^ 2) :
    outer.Contains point := by
  let margin := strictInteriorMargin inner outer
  have marginPositive : 0 < margin := strictInteriorMargin_pos strict
  rcases abs_coordinate_sub_lt marginPositive distance with
    ⟨realDifference, imagDifference⟩
  rcases abs_lt.mp realDifference with ⟨realLower, realUpper⟩
  rcases abs_lt.mp imagDifference with ⟨imagLower, imagUpper⟩
  have leftGap := strictInteriorMargin_le_left inner outer
  have rightGap := strictInteriorMargin_le_right inner outer
  have bottomGap := strictInteriorMargin_le_bottom inner outer
  have topGap := strictInteriorMargin_le_top inner outer
  exact ⟨by linarith [witnessInside.1],
    by linarith [witnessInside.2.1],
    by linarith [witnessInside.2.2.1],
    by linarith [witnessInside.2.2.2]⟩

theorem refines_trans_strictInterior
    {inner middle outer : RatBox} (refines : inner.Refines middle)
    (strict : StrictInterior middle outer) : StrictInterior inner outer :=
  ⟨strict.left.trans_le refines.1,
    refines.2.1.trans_lt strict.right,
    strict.bottom.trans_le refines.2.2.1,
    refines.2.2.2.trans_lt strict.top⟩

theorem RatBox.coordinateRadius_le_of_refines
    {small large : RatBox} (refines : small.Refines large) :
    small.coordinateRadius ≤ large.coordinateRadius := by
  let lower : QI := ⟨small.xLower, small.yLower⟩
  let upper : QI := ⟨small.xUpper, small.yUpper⟩
  have lowerInside : large.Contains lower :=
    ⟨refines.1, small.x_valid.trans refines.2.1,
      refines.2.2.1, small.y_valid.trans refines.2.2.2⟩
  have upperInside : large.Contains upper :=
    ⟨refines.1.trans small.x_valid, refines.2.1,
      refines.2.2.1.trans small.y_valid, refines.2.2.2⟩
  have lowerBounds := large.abs_coordinates_le_radius lowerInside
  have upperBounds := large.abs_coordinates_le_radius upperInside
  unfold RatBox.coordinateRadius
  exact max_le (max_le lowerBounds.1 upperBounds.1)
    (max_le lowerBounds.2 upperBounds.2)

theorem variationMajorant_le_of_refines
    (form : HermitianForm) {small large : RatBox}
    (refines : small.Refines large) :
    variationMajorant form small ≤ variationMajorant form large := by
  have radiusLe := RatBox.coordinateRadius_le_of_refines refines
  have radialCoefficient : 0 ≤ 2 * |form.radial| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have radialLe :
      2 * |form.radial| * small.coordinateRadius ≤
        2 * |form.radial| * large.coordinateRadius :=
    mul_le_mul_of_nonneg_left radiusLe radialCoefficient
  unfold variationMajorant
  exact max_le_max le_rfl (by linarith)

theorem boxVariation_sq_le_two_majorant_sq_mul_diagonalSq
    (form : HermitianForm) (box : RatBox) :
    boxVariation form box ^ 2 ≤
      2 * variationMajorant form box ^ 2 * box.diagonalSq := by
  have widths :
      (box.widthX + box.widthY) ^ 2 ≤
        2 * (box.widthX ^ 2 + box.widthY ^ 2) := by
    nlinarith [sq_nonneg (box.widthX - box.widthY)]
  have majorantSqNonnegative :
      0 ≤ variationMajorant form box ^ 2 := sq_nonneg _
  unfold boxVariation
  rw [mul_pow]
  rw [RatBox.diagonalSq_eq]
  calc
    variationMajorant form box ^ 2 * (box.widthX + box.widthY) ^ 2 ≤
        variationMajorant form box ^ 2 *
          (2 * (box.widthX ^ 2 + box.widthY ^ 2)) :=
      mul_le_mul_of_nonneg_left widths majorantSqNonnegative
    _ = 2 * variationMajorant form box ^ 2 *
        (box.widthX ^ 2 + box.widthY ^ 2) := by ring

theorem eval_center_sq_le_boxVariation_sq_of_strictSignCheck_ne
    (form : HermitianForm) (box : RatBox)
    (failed : strictSignCheck form box ≠ true) :
    form.eval box.center ^ 2 ≤ boxVariation form box ^ 2 := by
  have neither : ¬(0 < lowerBound form box ∨ upperBound form box < 0) := by
    intro signs
    exact failed ((strictSignCheck_eq_true_iff form box).2 signs)
  simp only [not_or, not_lt] at neither
  have absolute : |form.eval box.center| ≤ boxVariation form box := by
    rw [abs_le]
    dsimp only [lowerBound, upperBound] at neither
    exact ⟨by linarith [neither.2], by linarith [neither.1]⟩
  have squared := (sq_le_sq₀ (abs_nonneg (form.eval box.center))
    (boxVariation_nonneg form box)).2 absolute
  simpa only [sq_abs] using squared

/-! ## One uniform finite refinement for the planned family -/

def sourceStrictCost
    (source : CCLBranchPlan.BoundarySource) (box : RatBox) : ℚ :=
  2 * PlannedBoundarySource.coefficient source *
    variationMajorant source.form box ^ 2

theorem sourceStrictCost_nonneg
    (source : CCLBranchPlan.BoundarySource) (box : RatBox)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    0 ≤ sourceStrictCost source box := by
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (PlannedBoundarySource.coefficient_pos source determinantNonzero
        nondegenerate).le)
    (sq_nonneg _)

def plannedStrictCost (state : RawParser.State) (box : RatBox) : ℚ :=
  1 + ((CCLBranchPlan.inputPlan state).map fun source =>
    sourceStrictCost source box).sum

theorem plannedStrictCost_pos
    (state : RawParser.State) (box : RatBox)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    0 < plannedStrictCost state box := by
  have sumNonnegative : 0 ≤
      ((CCLBranchPlan.inputPlan state).map fun source =>
        sourceStrictCost source box).sum := by
    apply List.sum_nonneg
    intro value valueMember
    rw [List.mem_map] at valueMember
    rcases valueMember with ⟨source, sourceMember, rfl⟩
    exact sourceStrictCost_nonneg source box
      (CCLBranchPlan.inputPlan_determinant_ne state sourceMember
        stateDeterminant)
      (CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMember)
  unfold plannedStrictCost
  linarith

theorem sourceStrictCost_lt_plannedStrictCost
    (state : RawParser.State) (box : RatBox)
    (stateDeterminant : determinant state.matrix ≠ 0)
    {source : CCLBranchPlan.BoundarySource}
    (sourceMember : source ∈ CCLBranchPlan.inputPlan state) :
    sourceStrictCost source box < plannedStrictCost state box := by
  have singleLe : sourceStrictCost source box ≤
      ((CCLBranchPlan.inputPlan state).map fun item =>
        sourceStrictCost item box).sum := by
    apply List.single_le_sum
    · intro value valueMember
      rw [List.mem_map] at valueMember
      rcases valueMember with ⟨item, itemMember, rfl⟩
      exact sourceStrictCost_nonneg item box
        (CCLBranchPlan.inputPlan_determinant_ne state itemMember
          stateDeterminant)
        (CCLBranchPlan.inputPlan_parametrizationNondegenerate state itemMember)
    · exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
  unfold plannedStrictCost
  linarith

def strictTarget
    (guardBox separationBox : RatBox) (boundaryEpsilon : ℚ) : ℚ :=
  min boundaryEpsilon
    (strictInteriorMargin guardBox separationBox ^ 2)

theorem strictTarget_pos
    {guardBox separationBox : RatBox}
    (strict : StrictInterior guardBox separationBox)
    {boundaryEpsilon : ℚ} (boundaryEpsilonPositive : 0 < boundaryEpsilon) :
    0 < strictTarget guardBox separationBox boundaryEpsilon := by
  apply lt_min boundaryEpsilonPositive
  exact sq_pos_of_pos (strictInteriorMargin_pos strict)

def plannedStrictRadius
    (state : RawParser.State) (guardBox separationBox : RatBox)
    (boundaryEpsilon : ℚ) : ℚ :=
  min (1 / 2)
    (strictTarget guardBox separationBox boundaryEpsilon /
      (2 * plannedStrictCost state guardBox))

theorem plannedStrictRadius_pos
    (state : RawParser.State) {guardBox separationBox : RatBox}
    (strict : StrictInterior guardBox separationBox)
    {boundaryEpsilon : ℚ} (boundaryEpsilonPositive : 0 < boundaryEpsilon)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    0 < plannedStrictRadius state guardBox separationBox boundaryEpsilon := by
  apply lt_min
  · norm_num
  · exact div_pos (strictTarget_pos strict boundaryEpsilonPositive)
      (mul_pos (by norm_num)
        (plannedStrictCost_pos state guardBox stateDeterminant))

theorem plannedStrictCost_mul_radius_sq_lt_target
    (state : RawParser.State) {guardBox separationBox : RatBox}
    (strict : StrictInterior guardBox separationBox)
    {boundaryEpsilon : ℚ} (boundaryEpsilonPositive : 0 < boundaryEpsilon)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    plannedStrictCost state guardBox *
        plannedStrictRadius state guardBox separationBox boundaryEpsilon ^ 2 <
      strictTarget guardBox separationBox boundaryEpsilon := by
  let cost := plannedStrictCost state guardBox
  let radius := plannedStrictRadius state guardBox separationBox boundaryEpsilon
  let target := strictTarget guardBox separationBox boundaryEpsilon
  have costPositive : 0 < cost :=
    plannedStrictCost_pos state guardBox stateDeterminant
  have radiusPositive : 0 < radius :=
    plannedStrictRadius_pos state strict boundaryEpsilonPositive
      stateDeterminant
  have radiusHalf : radius ≤ 1 / 2 := min_le_left _ _
  have radiusLtOne : radius < 1 := by linarith
  have radiusSqLt : radius ^ 2 < radius := by
    nlinarith [mul_pos radiusPositive (sub_pos.mpr radiusLtOne)]
  have radiusRatio : radius ≤ target / (2 * cost) := min_le_right _ _
  have scaledRadius : cost * radius ≤ target / 2 := by
    have denominatorPositive : 0 < 2 * cost := mul_pos (by norm_num) costPositive
    have scaled := (le_div_iff₀ denominatorPositive).mp radiusRatio
    dsimp only [cost, target] at scaled ⊢
    nlinarith
  dsimp only [cost, radius, target] at radiusSqLt scaledRadius ⊢
  have strictScaled :
      plannedStrictCost state guardBox *
          plannedStrictRadius state guardBox separationBox boundaryEpsilon ^ 2 <
        plannedStrictCost state guardBox *
          plannedStrictRadius state guardBox separationBox boundaryEpsilon :=
    mul_lt_mul_of_pos_left radiusSqLt costPositive
  have targetPositive := strictTarget_pos strict boundaryEpsilonPositive
  linarith

/-! ## Strict signs forced by the completed boundary exclusion -/

/-- If interval strictness still failed at the requested accuracy, projecting
the center to that planned boundary would produce a forbidden nearby point
inside the older separation box. -/
theorem plannedBoundary_projection_inside_near
    (state : RawParser.State) {guardBox separationBox nextBox : RatBox}
    {boundaryEpsilon : ℚ}
    (strict : StrictInterior guardBox separationBox)
    (boundaryEpsilonPositive : 0 < boundaryEpsilon)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈ CCLBranchPlan.inputPlan state)
    (nextRefines : nextBox.Refines guardBox)
    (nextAccurate : nextBox.diagonalSq ≤
      plannedStrictRadius state guardBox separationBox boundaryEpsilon ^ 2)
    (failed : strictSignCheck source.form nextBox ≠ true) :
    let projected := PlannedBoundarySource.projection source nextBox.center
      (CCLBranchPlan.inputPlan_determinant_ne state sourceMember
        stateDeterminant)
      (CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMember)
    separationBox.Contains projected.point ∧
      WithinSqOfBox guardBox projected.point boundaryEpsilon := by
  let radius := plannedStrictRadius state guardBox separationBox boundaryEpsilon
  let target := strictTarget guardBox separationBox boundaryEpsilon
  have sourceDeterminant : determinant source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state sourceMember stateDeterminant
  have sourceNondegenerate : source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMember
  have radiusPositive : 0 < radius :=
    plannedStrictRadius_pos state strict boundaryEpsilonPositive
      stateDeterminant
  let projected := PlannedBoundarySource.projection source nextBox.center
    sourceDeterminant sourceNondegenerate
  have centerResidualSq : source.form.eval nextBox.center ^ 2 ≤
      boxVariation source.form nextBox ^ 2 :=
    eval_center_sq_le_boxVariation_sq_of_strictSignCheck_ne source.form
      nextBox failed
  have variationSq : boxVariation source.form nextBox ^ 2 ≤
      2 * variationMajorant source.form nextBox ^ 2 * nextBox.diagonalSq :=
    boxVariation_sq_le_two_majorant_sq_mul_diagonalSq source.form nextBox
  have majorantLe : variationMajorant source.form nextBox ≤
      variationMajorant source.form guardBox :=
    variationMajorant_le_of_refines source.form nextRefines
  have majorantSqLe : variationMajorant source.form nextBox ^ 2 ≤
      variationMajorant source.form guardBox ^ 2 :=
    (sq_le_sq₀ (variationMajorant_pos source.form nextBox).le
      (variationMajorant_pos source.form guardBox).le).2 majorantLe
  have diagonalNonnegative : 0 ≤ nextBox.diagonalSq :=
    nextBox.diagonalSq_nonneg
  have scaledMajorant :
      2 * variationMajorant source.form nextBox ^ 2 * nextBox.diagonalSq ≤
        2 * variationMajorant source.form guardBox ^ 2 * nextBox.diagonalSq :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left majorantSqLe (by norm_num))
      diagonalNonnegative
  have residualBound : source.form.eval nextBox.center ^ 2 ≤
      2 * variationMajorant source.form guardBox ^ 2 * nextBox.diagonalSq :=
    centerResidualSq.trans (variationSq.trans scaledMajorant)
  have coefficientPositive :
      0 < PlannedBoundarySource.coefficient source :=
    PlannedBoundarySource.coefficient_pos source sourceDeterminant
      sourceNondegenerate
  have projectionDistance := projected.distance
  rw [PlannedBoundarySource.projection_coefficient] at projectionDistance
  have distanceLeSourceCost :
      normSq (projected.point - nextBox.center) ≤
        sourceStrictCost source guardBox * nextBox.diagonalSq := by
    calc
      normSq (projected.point - nextBox.center) ≤
          PlannedBoundarySource.coefficient source *
            source.form.eval nextBox.center ^ 2 := projectionDistance
      _ ≤ PlannedBoundarySource.coefficient source *
          (2 * variationMajorant source.form guardBox ^ 2 *
            nextBox.diagonalSq) :=
        mul_le_mul_of_nonneg_left residualBound coefficientPositive.le
      _ = sourceStrictCost source guardBox * nextBox.diagonalSq := by
        unfold sourceStrictCost
        ring
  have sourceCostNonnegative : 0 ≤ sourceStrictCost source guardBox :=
    sourceStrictCost_nonneg source guardBox sourceDeterminant
      sourceNondegenerate
  have sourceCostLe : sourceStrictCost source guardBox ≤
      plannedStrictCost state guardBox :=
    (sourceStrictCost_lt_plannedStrictCost state guardBox stateDeterminant
      sourceMember).le
  have radiusSqNonnegative : 0 ≤ radius ^ 2 := sq_nonneg _
  have distanceTarget : normSq (projected.point - nextBox.center) < target := by
    calc
      normSq (projected.point - nextBox.center) ≤
          sourceStrictCost source guardBox * nextBox.diagonalSq :=
        distanceLeSourceCost
      _ ≤ sourceStrictCost source guardBox * radius ^ 2 :=
        mul_le_mul_of_nonneg_left (by simpa only [radius] using nextAccurate)
          sourceCostNonnegative
      _ ≤ plannedStrictCost state guardBox * radius ^ 2 :=
        mul_le_mul_of_nonneg_right sourceCostLe radiusSqNonnegative
      _ < target := by
        simpa only [radius, target] using
          plannedStrictCost_mul_radius_sq_lt_target state strict
            boundaryEpsilonPositive stateDeterminant
  have distanceMargin : normSq (projected.point - nextBox.center) <
      strictInteriorMargin guardBox separationBox ^ 2 :=
    distanceTarget.trans_le (min_le_right _ _)
  have projectedInside : separationBox.Contains projected.point :=
    contains_of_normSq_sub_lt_strictInteriorMargin_sq strict
      (nextRefines.contains nextBox.contains_center) distanceMargin
  have distanceBoundary : normSq (projected.point - nextBox.center) <
      boundaryEpsilon :=
    distanceTarget.trans_le (min_le_left _ _)
  exact ⟨projectedInside,
    ⟨nextBox.center, nextRefines.contains nextBox.contains_center,
      distanceBoundary⟩⟩

theorem inputPlan_strictSignCheck_of_accurate
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse current.word) separation))
    (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)
    (strict : StrictInterior guardOutput.state.box separation.state.box)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines guardOutput.state.box)
    (nextAccurate : next.box.diagonalSq ≤
      plannedStrictRadius (RawParser.parse current.word)
        guardOutput.state.box separation.state.box
          (min output.epsilon guardOutput.epsilon) ^ 2)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈
      CCLBranchPlan.inputPlan (RawParser.parse current.word)) :
    strictSignCheck source.form next.box = true := by
  let state := RawParser.parse current.word
  let boundaryEpsilon := min output.epsilon guardOutput.epsilon
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have boundaryEpsilonPositive : 0 < boundaryEpsilon :=
    lt_min output.epsilonPositive guardOutput.epsilonPositive
  by_contra failed
  have sourceDeterminant : determinant source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state sourceMember stateDeterminant
  have sourceNondegenerate : source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMember
  let projected := PlannedBoundarySource.projection source next.box.center
    sourceDeterminant sourceNondegenerate
  have near := plannedBoundary_projection_inside_near state strict
    boundaryEpsilonPositive stateDeterminant source sourceMember nextRefines
      nextAccurate failed
  exact alignedAllClear_guardClear_not_near_boundary alignment output
    guardEvidence guardOutput source sourceMember projected.point near.1
      projected.boundary near.2

/-- Sample-free form of the computed refinement: the quantitative construction
uses only the winding state and raw word. -/
structure PlannedStrictOutputData
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (guardState : WindingOneState p ambient) where
  state : WindingOneState p ambient
  refines : state.box.Refines guardState.box
  strictSigns : ∀ source ∈
    CCLBranchPlan.inputPlan (RawParser.parse word),
      strictSignCheck source.form state.box = true

/-- The purely metric half of a planned strict-cell refinement.  Keeping this
certificate separate lets the later finite boundary argument elaborate within
the ordinary project budget. -/
structure PlannedAccuracyOutput
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (guardState : WindingOneState p ambient)
    (separationBox : RatBox) (boundaryEpsilon : ℚ) where
  state : WindingOneState p ambient
  refines : state.box.Refines guardState.box
  accurate : state.box.diagonalSq ≤
    plannedStrictRadius (RawParser.parse word) guardState.box separationBox
      boundaryEpsilon ^ 2

/-- Compute the requested numerical accuracy, independently of all boundary
certificates. -/
def refineForPlannedAccuracy
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (word : Prefix.Word) (guardState : WindingOneState p ambient)
    (separationBox : RatBox) (boundaryEpsilon : ℚ)
    (radiusPositive : 0 < plannedStrictRadius (RawParser.parse word)
      guardState.box separationBox boundaryEpsilon) :
    PlannedAccuracyOutput word guardState separationBox boundaryEpsilon := by
  let radius := plannedStrictRadius (RawParser.parse word) guardState.box
    separationBox boundaryEpsilon
  let next := track.refine guardState radius radiusPositive
  exact
    { state := next
      refines := track.nested guardState radius radiusPositive
      accurate := track.accurate guardState radius radiusPositive }

/-- A finite boundary-exclusion certificate turns numerical accuracy into one
strict comparison.  This metric lemma deliberately knows nothing about the
root-count machinery that supplied the exclusion certificate. -/
theorem strictSignCheck_of_plannedBoundary_exclusion
    (state : RawParser.State) {guardBox separationBox nextBox : RatBox}
    {boundaryEpsilon : ℚ}
    (strict : StrictInterior guardBox separationBox)
    (boundaryEpsilonPositive : 0 < boundaryEpsilon)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (source : CCLBranchPlan.BoundarySource)
    (sourceMember : source ∈ CCLBranchPlan.inputPlan state)
    (nextRefines : nextBox.Refines guardBox)
    (nextAccurate : nextBox.diagonalSq ≤
      plannedStrictRadius state guardBox separationBox boundaryEpsilon ^ 2)
    (excluded : ∀ point, separationBox.Contains point →
      source.form.eval point = 0 →
      WithinSqOfBox guardBox point boundaryEpsilon → False) :
    strictSignCheck source.form nextBox = true := by
  by_contra failed
  have sourceDeterminant : determinant source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state sourceMember stateDeterminant
  have sourceNondegenerate : source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state sourceMember
  let projected := PlannedBoundarySource.projection source nextBox.center
    sourceDeterminant sourceNondegenerate
  have near := plannedBoundary_projection_inside_near state strict
    boundaryEpsilonPositive stateDeterminant source sourceMember nextRefines
      nextAccurate failed
  exact excluded projected.point near.1 projected.boundary near.2

/-- Compute the strict local comparison cell from finite boundary exclusion,
without constructing or consulting a represented rational sample. -/
def refineForPlannedStrictCellOfExclusion
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (word : Prefix.Word) (guardState : WindingOneState p ambient)
    (separationBox : RatBox) (boundaryEpsilon : ℚ)
    (strict : StrictInterior guardState.box separationBox)
    (boundaryEpsilonPositive : 0 < boundaryEpsilon)
    (excluded : ∀ source ∈ CCLBranchPlan.inputPlan (RawParser.parse word),
      ∀ point, separationBox.Contains point → source.form.eval point = 0 →
        WithinSqOfBox guardState.box point boundaryEpsilon → False) :
    PlannedStrictOutputData word guardState := by
  let state := RawParser.parse word
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne word
  let radius := plannedStrictRadius state guardState.box separationBox
    boundaryEpsilon
  have radiusPositive : 0 < radius :=
    plannedStrictRadius_pos state strict boundaryEpsilonPositive
      stateDeterminant
  let planned := refineForPlannedAccuracy track word guardState separationBox
    boundaryEpsilon (by
      simpa only [state, radius] using radiusPositive)
  exact
    { state := planned.state
      refines := planned.refines
      strictSigns := by
        intro source sourceMember
        apply strictSignCheck_of_plannedBoundary_exclusion state strict
          boundaryEpsilonPositive stateDeterminant source sourceMember
          planned.refines
        · simpa only [state] using planned.accurate
        · intro point contains boundary near
          exact excluded source sourceMember point contains boundary near }

/-- Compatibility wrapper for the older sampled coupled-state controller. -/
structure PlannedStrictOutput
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (guardState : WindingOneState p ambient) where
  state : WindingOneState p ambient
  refines : state.box.Refines guardState.box
  strictSigns : ∀ source ∈
    CCLBranchPlan.inputPlan (RawParser.parse current.word),
      strictSignCheck source.form state.box = true

def refineForPlannedStrictCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient separation.state evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse current.word) separation))
    (guardOutput : GuardRefinementOutput p ambient output.state guardEvidence)
    (strict : StrictInterior guardOutput.state.box separation.state.box) :
    PlannedStrictOutput current guardOutput.state := by
  let state := RawParser.parse current.word
  let boundaryEpsilon := min output.epsilon guardOutput.epsilon
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have boundaryEpsilonPositive : 0 < boundaryEpsilon :=
    lt_min output.epsilonPositive guardOutput.epsilonPositive
  let radius := plannedStrictRadius state guardOutput.state.box
    separation.state.box boundaryEpsilon
  have radiusPositive : 0 < radius :=
    plannedStrictRadius_pos state strict boundaryEpsilonPositive
      stateDeterminant
  let next := track.refine guardOutput.state radius radiusPositive
  have nextRefines : next.box.Refines guardOutput.state.box :=
    track.nested guardOutput.state radius radiusPositive
  have nextAccurate : next.box.diagonalSq ≤ radius ^ 2 :=
    track.accurate guardOutput.state radius radiusPositive
  exact
    { state := next
      refines := nextRefines
      strictSigns := by
        intro source sourceMember
        exact inputPlan_strictSignCheck_of_accurate alignment output
          guardEvidence guardOutput strict next nextRefines (by
            simpa only [state, boundaryEpsilon, radius] using nextAccurate)
          source sourceMember }

/-- Any track whose individual calls are strictly nested makes the first
spatial call of `refineForClearance` a permanent strict-interior margin; the
second call only needs ordinary nesting. -/
theorem refineForClearance_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox} {arcs : List (BoundaryArc p)}
    (track : WindingOneTrack p ambient)
    (strictRefine : ∀ current epsilon positive,
      StrictInterior (track.refine current epsilon positive).box current.box)
    (current : WindingOneState p ambient) (evidence : AllClear p arcs) :
    StrictInterior (refineForClearance track current evidence).state.box
      current.box := by
  let spatial := clearSpatialRadius p ambient evidence
  let spatialPositive := clearSpatialRadius_pos p ambient evidence
  let small := track.refine current spatial spatialPositive
  let threshold := evidence.uniformClearance / 16
  have thresholdPositive : 0 < threshold :=
    div_pos evidence.uniformClearance_pos (by norm_num)
  let residual := residualRefinementRadius p ambient threshold
  let residualPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  let final := track.refine small residual residualPositive
  have finalRefines : final.box.Refines small.box :=
    track.nested small residual residualPositive
  have smallStrict : StrictInterior small.box current.box :=
    strictRefine current spatial spatialPositive
  have finalStrict := refines_trans_strictInterior finalRefines smallStrict
  simpa only [refineForClearance, spatial, spatialPositive, small, threshold,
    thresholdPositive, residual, residualPositive, final] using finalStrict

/-- The terminal-guard clearance refinement has the same strict-nesting
property: its first spatial call enters the current box strictly and its
second residual call remains inside that strict margin. -/
theorem refineForGuardClearance_strictInterior
    {p : GaussianPolynomial} {ambient box : RatBox}
    {sourceCells : List (SourceEventGuardCell p box)}
    (track : WindingOneTrack p ambient)
    (strictRefine : ∀ current epsilon positive,
      StrictInterior (track.refine current epsilon positive).box current.box)
    (current : WindingOneState p ambient)
    (evidence : AllGuardClear p box sourceCells) :
    StrictInterior (refineForGuardClearance track current evidence).state.box
      current.box := by
  let spatial := guardSpatialRadius p ambient evidence
  let spatialPositive := guardSpatialRadius_pos p ambient evidence
  let small := track.refine current spatial spatialPositive
  let threshold := evidence.uniformClearance / 16
  have thresholdPositive : 0 < threshold :=
    div_pos evidence.uniformClearance_pos (by norm_num)
  let residual := residualRefinementRadius p ambient threshold
  let residualPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  let final := track.refine small residual residualPositive
  have finalRefines : final.box.Refines small.box :=
    track.nested small residual residualPositive
  have smallStrict : StrictInterior small.box current.box :=
    strictRefine current spatial spatialPositive
  have finalStrict := refines_trans_strictInterior finalRefines smallStrict
  simpa only [refineForGuardClearance, spatial, spatialPositive, small,
    threshold, thresholdPositive, residual, residualPositive, final] using
      finalStrict

/-- The concrete constructive track supplies strict nesting with no added
resource or recursion option. -/
theorem concreteRefineForClearance_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {arcs : List (BoundaryArc p)}
    (current : WindingOneState p ambient) (evidence : AllClear p arcs) :
    StrictInterior
      (refineForClearance (ConstructiveTrack.ofInitial squarefree elimination
        current) current evidence).state.box current.box := by
  apply refineForClearance_strictInterior
  intro state epsilon positive
  exact ConstructiveTrack.refineState_strictInterior squarefree elimination
    state epsilon positive

end CCLBoundaryStrictCell
end FTA
