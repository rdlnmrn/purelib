import FTA.CCLBranchEvidence
import FTA.GaussianPolynomialBounds

/-!
# Excluding clear CCL boundary arcs from refined root boxes

This is the quantitative contradiction in the zero-count half of Theorem
10.2.  A finite intersection sampler would return a rational point on a clear
branch arc close to the current winding-one box.  The center residual, the
box diagonal, and the sampler error then force the polynomial norm at that
arc point below half of its certified clearance, which is impossible.
-/

namespace FTA
namespace CCLClearanceExclusion

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.GaussianPolynomialBounds
open FTA.ProjectivePath
open FTA.CCLIntersectionSampler
open FTA.CCLBranchEvidence

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- A fixed rational enlargement containing an ambient box and every point
at squared distance below one from it. -/
def nearbyAmbient (ambient : RatBox) : RatBox :=
  RatBox.symmetric (ambient.coordinateRadius + 1) (by
    exact add_nonneg ambient.coordinateRadius_nonneg (by norm_num))

theorem nearbyAmbient_contains
    {ambient : RatBox} {z : QI} (hz : ambient.Contains z) :
    (nearbyAmbient ambient).Contains z := by
  rcases ambient.abs_coordinates_le_radius hz with ⟨hre, him⟩
  rcases abs_le.mp hre with ⟨hreLower, hreUpper⟩
  rcases abs_le.mp him with ⟨himLower, himUpper⟩
  dsimp only [nearbyAmbient, RatBox.symmetric, RatBox.Contains]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem abs_coordinate_sub_lt_one
    {z w : QI} (distance : normSq (z - w) < 1) :
    |z.re - w.re| < 1 ∧ |z.im - w.im| < 1 := by
  have realSq : (z.re - w.re) ^ 2 < 1 := by
    dsimp only [normSq, sub_re, sub_im] at distance
    nlinarith [sq_nonneg (z.im - w.im)]
  have imagSq : (z.im - w.im) ^ 2 < 1 := by
    dsimp only [normSq, sub_re, sub_im] at distance
    nlinarith [sq_nonneg (z.re - w.re)]
  rw [← sq_abs] at realSq imagSq
  constructor <;> nlinarith [abs_nonneg (z.re - w.re),
    abs_nonneg (z.im - w.im)]

/-- A sampler point within squared distance at most one of a subbox lies in
the fixed rational enlargement of the ambient box. -/
theorem nearbyAmbient_contains_of_withinSqOfBox
    {ambient box : RatBox} (refines : box.Refines ambient)
    {point : QI} {epsilon : ℚ} (epsilonAtMostOne : epsilon ≤ 1)
    (near : WithinSqOfBox box point epsilon) :
    (nearbyAmbient ambient).Contains point := by
  rcases near with ⟨witness, witnessInBox, distance⟩
  have witnessInAmbient := refines.contains witnessInBox
  have distanceOne : normSq (point - witness) < 1 :=
    distance.trans_le epsilonAtMostOne
  rcases abs_coordinate_sub_lt_one distanceOne with ⟨realDifference, imagDifference⟩
  rcases ambient.abs_coordinates_le_radius witnessInAmbient with
    ⟨witnessReal, witnessImag⟩
  have pointReal : |point.re| < ambient.coordinateRadius + 1 := by
    calc
      |point.re| = |(point.re - witness.re) + witness.re| := by ring_nf
      _ ≤ |point.re - witness.re| + |witness.re| := abs_add_le _ _
      _ < 1 + ambient.coordinateRadius :=
        add_lt_add_of_lt_of_le realDifference witnessReal
      _ = ambient.coordinateRadius + 1 := by ring
  have pointImag : |point.im| < ambient.coordinateRadius + 1 := by
    calc
      |point.im| = |(point.im - witness.im) + witness.im| := by ring_nf
      _ ≤ |point.im - witness.im| + |witness.im| := abs_add_le _ _
      _ < 1 + ambient.coordinateRadius :=
        add_lt_add_of_lt_of_le imagDifference witnessImag
      _ = ambient.coordinateRadius + 1 := by ring
  rcases abs_lt.mp pointReal with ⟨realLower, realUpper⟩
  rcases abs_lt.mp pointImag with ⟨imagLower, imagUpper⟩
  exact ⟨realLower.le, realUpper.le, imagLower.le, imagUpper.le⟩

/-- A point whose polynomial residual and distance to its coordinatewise
clamp are both small relative to certified boundary clearance must lie
strictly inside the box. -/
theorem strictContains_of_clamp
    {p : GaussianPolynomial} {box : RatBox}
    (clearance : LocalExtraction.BoxBoundaryClearanceCertificate p box)
    {point : QI} {epsilon : ℚ} (epsilonAtMostOne : epsilon ≤ 1)
    (clampDistance : normSq (point - clampToBox box point) < epsilon)
    (pointResidual : normSq (p.eval point) < clearance.bound / 8)
    (distanceBudget :
      denseLipschitzBound p (nearbyAmbient box) * epsilon <
        clearance.bound / 8) :
    box.StrictContains point := by
  by_contra notStrict
  let witness := clampToBox box point
  have boundary : LocalExtraction.OnBoxBoundary box witness := by
    exact clampToBox_boundary_coordinates_of_not_strictContains notStrict
  have witnessInNearby : (nearbyAmbient box).Contains witness :=
    nearbyAmbient_contains boundary.1
  have near : WithinSqOfBox box point epsilon :=
    ⟨witness, boundary.1, clampDistance⟩
  have pointInNearby : (nearbyAmbient box).Contains point :=
    nearbyAmbient_contains_of_withinSqOfBox (RatBox.refines_refl box)
      epsilonAtMostOne near
  have evaluationDifference :
      normSq (p.eval point - p.eval witness) < clearance.bound / 8 := by
    have lipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound
      p pointInNearby witnessInNearby
    have scaledDistance :
        denseLipschitzBound p (nearbyAmbient box) *
            normSq (point - witness) <
          denseLipschitzBound p (nearbyAmbient box) * epsilon :=
      mul_lt_mul_of_pos_left clampDistance
        (denseLipschitzBound_pos p (nearbyAmbient box))
    have evaluationDistance :
        normSq (p.eval point - p.eval witness) <
          denseLipschitzBound p (nearbyAmbient box) * epsilon := by
      simpa only [GaussianRat.sub_eq_add_neg] using
        lipschitz.trans_lt (by
          simpa only [GaussianRat.sub_eq_add_neg] using scaledDistance)
    exact evaluationDistance.trans distanceBudget
  have witnessEvaluation :
      normSq (p.eval witness) < clearance.bound / 2 := by
    have decomposition :
        -(p.eval point - p.eval witness) + p.eval point = p.eval witness := by
      ext <;> simp only [sub_re, sub_im, add_re, add_im, neg_re, neg_im] <;>
        ring
    have sumBound := normSq_add_le_two
      (-(p.eval point - p.eval witness)) (p.eval point)
    rw [decomposition, normSq_neg] at sumBound
    nlinarith
  have boundaryLower := clearance.lower witness boundary
  nlinarith [clearance.positive]

/-- A fixed positive rational interior scale derived solely from boundary
clearance.  It is deliberately conservative so its square is controlled
without extracting a rational square root. -/
def boundaryInteriorRadius
    (p : GaussianPolynomial) (box : RatBox)
    (clearance : LocalExtraction.BoxBoundaryClearanceCertificate p box) : ℚ :=
  min 1 (clearance.bound /
    (256 * denseLipschitzBound p (nearbyAmbient box)))

theorem boundaryInteriorRadius_pos
    (p : GaussianPolynomial) (box : RatBox)
    (clearance : LocalExtraction.BoxBoundaryClearanceCertificate p box) :
    0 < boundaryInteriorRadius p box clearance := by
  apply lt_min zero_lt_one
  exact div_pos clearance.positive
    (mul_pos (by norm_num)
      (denseLipschitzBound_pos p (nearbyAmbient box)))

/-- A strictly contained point with residual below one sixteenth of the
boundary clearance has a uniform four-radius gap from every side. -/
theorem deepInside_of_small_residual
    {p : GaussianPolynomial} {box : RatBox}
    (clearance : LocalExtraction.BoxBoundaryClearanceCertificate p box)
    {point : QI} (strict : box.StrictContains point)
    (residual : normSq (p.eval point) ≤ clearance.bound / 16) :
    let radius := boundaryInteriorRadius p box clearance
    box.xLower + 4 * radius < point.re ∧
      point.re < box.xUpper - 4 * radius ∧
      box.yLower + 4 * radius < point.im ∧
      point.im < box.yUpper - 4 * radius := by
  let radius := boundaryInteriorRadius p box clearance
  let L := denseLipschitzBound p (nearbyAmbient box)
  have radiusPositive : 0 < radius :=
    boundaryInteriorRadius_pos p box clearance
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeRatio : radius ≤ clearance.bound / (256 * L) :=
    min_le_right _ _
  have LPositive : 0 < L := denseLipschitzBound_pos p (nearbyAmbient box)
  have radiusSquareLe : radius ^ 2 ≤ radius := by nlinarith
  have variationBudget : L * (16 * radius ^ 2) ≤ clearance.bound / 16 := by
    have scaled :=
      (le_div_iff₀ (mul_pos (by norm_num) LPositive)).mp radiusLeRatio
    nlinarith
  have pointNearby : (nearbyAmbient box).Contains point :=
    nearbyAmbient_contains strict.contains
  have boundaryNotClose (witness : QI)
      (boundary : LocalExtraction.OnBoxBoundary box witness)
      (distance : normSq (point - witness) ≤ 16 * radius ^ 2) : False := by
    have witnessNearby : (nearbyAmbient box).Contains witness :=
      nearbyAmbient_contains boundary.1
    have lipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound
      p pointNearby witnessNearby
    have evaluationDifference :
        normSq (p.eval point - p.eval witness) ≤ clearance.bound / 16 := by
      have distanceScaled : L * normSq (point - witness) ≤
          L * (16 * radius ^ 2) :=
        mul_le_mul_of_nonneg_left distance LPositive.le
      have distanceFinal :
          denseLipschitzBound p (nearbyAmbient box) *
              normSq (point + -witness) ≤ clearance.bound / 16 := by
        simpa only [L, GaussianRat.sub_eq_add_neg] using
          distanceScaled.trans variationBudget
      simpa only [GaussianRat.sub_eq_add_neg] using
        lipschitz.trans distanceFinal
    have witnessEvaluation :
        normSq (p.eval witness) ≤ clearance.bound / 4 := by
      have decomposition :
          -(p.eval point - p.eval witness) + p.eval point = p.eval witness := by
        ext <;> simp only [sub_re, sub_im, add_re, add_im, neg_re, neg_im] <;>
          ring
      have sumBound := normSq_add_le_two
        (-(p.eval point - p.eval witness)) (p.eval point)
      rw [decomposition, normSq_neg] at sumBound
      nlinarith
    have lower := clearance.lower witness boundary
    nlinarith [clearance.positive]
  have left : box.xLower + 4 * radius < point.re := by
    by_contra notLeft
    have gapNonnegative : 0 ≤ point.re - box.xLower :=
      sub_nonneg.mpr strict.1.le
    have gapUpper : point.re - box.xLower ≤ 4 * radius := by linarith
    let witness : QI := ⟨box.xLower, point.im⟩
    have contains : box.Contains witness :=
      ⟨le_rfl, box.x_valid, strict.2.2.1.le, strict.2.2.2.le⟩
    have boundary : LocalExtraction.OnBoxBoundary box witness :=
      ⟨contains, Or.inl rfl⟩
    apply boundaryNotClose witness boundary
    dsimp only [witness, normSq, sub_re, sub_im]
    have product := mul_nonneg gapNonnegative (sub_nonneg.mpr gapUpper)
    nlinarith
  have right : point.re < box.xUpper - 4 * radius := by
    by_contra notRight
    have gapNonnegative : 0 ≤ box.xUpper - point.re :=
      sub_nonneg.mpr strict.2.1.le
    have gapUpper : box.xUpper - point.re ≤ 4 * radius := by linarith
    let witness : QI := ⟨box.xUpper, point.im⟩
    have contains : box.Contains witness :=
      ⟨box.x_valid, le_rfl, strict.2.2.1.le, strict.2.2.2.le⟩
    have boundary : LocalExtraction.OnBoxBoundary box witness :=
      ⟨contains, Or.inr (Or.inl rfl)⟩
    apply boundaryNotClose witness boundary
    dsimp only [witness, normSq, sub_re, sub_im]
    have product := mul_nonneg gapNonnegative (sub_nonneg.mpr gapUpper)
    nlinarith
  have bottom : box.yLower + 4 * radius < point.im := by
    by_contra notBottom
    have gapNonnegative : 0 ≤ point.im - box.yLower :=
      sub_nonneg.mpr strict.2.2.1.le
    have gapUpper : point.im - box.yLower ≤ 4 * radius := by linarith
    let witness : QI := ⟨point.re, box.yLower⟩
    have contains : box.Contains witness :=
      ⟨strict.1.le, strict.2.1.le, le_rfl, box.y_valid⟩
    have boundary : LocalExtraction.OnBoxBoundary box witness :=
      ⟨contains, Or.inr (Or.inr (Or.inl rfl))⟩
    apply boundaryNotClose witness boundary
    dsimp only [witness, normSq, sub_re, sub_im]
    have product := mul_nonneg gapNonnegative (sub_nonneg.mpr gapUpper)
    nlinarith
  have top : point.im < box.yUpper - 4 * radius := by
    by_contra notTop
    have gapNonnegative : 0 ≤ box.yUpper - point.im :=
      sub_nonneg.mpr strict.2.2.2.le
    have gapUpper : box.yUpper - point.im ≤ 4 * radius := by linarith
    let witness : QI := ⟨point.re, box.yUpper⟩
    have contains : box.Contains witness :=
      ⟨strict.1.le, strict.2.1.le, box.y_valid, le_rfl⟩
    have boundary : LocalExtraction.OnBoxBoundary box witness :=
      ⟨contains, Or.inr (Or.inr (Or.inr rfl))⟩
    apply boundaryNotClose witness boundary
    dsimp only [witness, normSq, sub_re, sub_im]
    have product := mul_nonneg gapNonnegative (sub_nonneg.mpr gapUpper)
    nlinarith
  exact ⟨left, right, bottom, top⟩

theorem RatBox.diagonalSq_le_of_refines
    {small large : RatBox} (refines : small.Refines large) :
    small.diagonalSq ≤ large.diagonalSq := by
  rcases refines with ⟨xLower, xUpper, yLower, yUpper⟩
  have widthX : small.widthX ≤ large.widthX := by
    dsimp only [RatBox.widthX]
    linarith
  have widthY : small.widthY ≤ large.widthY := by
    dsimp only [RatBox.widthY]
    linarith
  have widthXSq : small.widthX ^ 2 ≤ large.widthX ^ 2 :=
    (sq_le_sq₀ small.widthX_nonneg large.widthX_nonneg).2 widthX
  have widthYSq : small.widthY ^ 2 ≤ large.widthY ^ 2 :=
    (sq_le_sq₀ small.widthY_nonneg large.widthY_nonneg).2 widthY
  simpa only [RatBox.diagonalSq_eq] using add_le_add widthXSq widthYSq

/-! ## Explicit all-clear track refinement -/

/-- Spatial radius leaving ample room in the `δ/8` sampler budget. -/
def clearSpatialRadius
    (p : GaussianPolynomial) (ambient : RatBox) {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) : ℚ :=
  min (1 / 2) (evidence.uniformClearance /
    (64 * denseLipschitzBound p (nearbyAmbient ambient)))

theorem clearSpatialRadius_pos
    (p : GaussianPolynomial) (ambient : RatBox) {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) :
    0 < clearSpatialRadius p ambient evidence := by
  apply lt_min
  · norm_num
  · exact div_pos evidence.uniformClearance_pos
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient ambient)))

/-- Two finite track calls: the first fixes the spatial/sampler budget, and
the second fixes the center residual while nesting preserves the first
bound. -/
structure RefinementOutput
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : RootTrackSeparation.WindingOneState p ambient)
    {arcs : List (BoundaryArc p)} (evidence : AllClear p arcs) where
  state : RootTrackSeparation.WindingOneState p ambient
  refines : state.box.Refines current.box
  epsilon : ℚ
  epsilonPositive : 0 < epsilon
  epsilonAtMostOne : epsilon ≤ 1
  centerResidual :
    normSq (p.eval state.box.center) < evidence.uniformClearance / 8
  distanceBudget :
    denseLipschitzBound p (nearbyAmbient ambient) *
        (2 * (epsilon + state.box.diagonalSq)) <
      evidence.uniformClearance / 8

/-- Regard a clearance refinement begun in a nested winding box as a
refinement of any displayed ancestor.  The quantitative fields concern only
the final state, so only the box-refinement proof is composed. -/
def RefinementOutput.rebase
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer inner : RootTrackSeparation.WindingOneState p ambient}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (output : RefinementOutput p ambient inner evidence)
    (innerRefines : inner.box.Refines outer.box) :
    RefinementOutput p ambient outer evidence where
  state := output.state
  refines := output.refines.trans innerRefines
  epsilon := output.epsilon
  epsilonPositive := output.epsilonPositive
  epsilonAtMostOne := output.epsilonAtMostOne
  centerResidual := output.centerResidual
  distanceBudget := output.distanceBudget

/-- Precompute and execute the all-clear refinement required in the proof of
Theorem 10.2. -/
def refineForClearance
    {p : GaussianPolynomial} {ambient : RatBox} {arcs : List (BoundaryArc p)}
    (track : RootTrackSeparation.WindingOneTrack p ambient)
    (current : RootTrackSeparation.WindingOneState p ambient)
    (evidence : AllClear p arcs) :
    RefinementOutput p ambient current evidence := by
  let delta := evidence.uniformClearance
  let L := denseLipschitzBound p (nearbyAmbient ambient)
  let spatial := clearSpatialRadius p ambient evidence
  let spatialPositive := clearSpatialRadius_pos p ambient evidence
  let small := track.refine current spatial spatialPositive
  let threshold := delta / 16
  have deltaPositive : 0 < delta := evidence.uniformClearance_pos
  have thresholdPositive : 0 < threshold := div_pos deltaPositive (by norm_num)
  let residual := RootTrackSeparation.residualRefinementRadius
    p ambient threshold
  let residualPositive := RootTrackSeparation.residualRefinementRadius_pos
    p ambient thresholdPositive
  let final := track.refine small residual residualPositive
  let epsilon := spatial ^ 2
  have spatialHalf : spatial ≤ 1 / 2 := min_le_left _ _
  have spatialOne : spatial ≤ 1 := by linarith
  have spatialSqLe : spatial ^ 2 ≤ spatial := by
    nlinarith [mul_nonneg spatialPositive.le (sub_nonneg.mpr spatialOne)]
  have epsilonPositive : 0 < epsilon := sq_pos_of_pos spatialPositive
  have epsilonAtMostOne : epsilon ≤ 1 :=
    spatialSqLe.trans spatialOne
  have finalRefinesSmall : final.box.Refines small.box :=
    track.nested small residual residualPositive
  have smallRefinesCurrent : small.box.Refines current.box :=
    track.nested current spatial spatialPositive
  have finalDiagonal : final.box.diagonalSq ≤ epsilon := by
    apply (RatBox.diagonalSq_le_of_refines finalRefinesSmall).trans
    simpa only [small, epsilon] using
      track.accurate current spatial spatialPositive
  have centerResidualLe :
      normSq (p.eval final.box.center) ≤ threshold := by
    simpa only [residual, residualPositive, final] using
      RootTrackSeparation.refined_center_residual_le
        track small thresholdPositive
  have centerResidual :
      normSq (p.eval final.box.center) < delta / 8 := by
    dsimp only [threshold] at centerResidualLe
    linarith
  have LPositive : 0 < L :=
    denseLipschitzBound_pos p (nearbyAmbient ambient)
  have spatialRatio : spatial ≤ delta / (64 * L) := by
    exact min_le_right _ _
  have scaledSpatial : 64 * L * spatial ≤ delta := by
    have scaled := (le_div_iff₀
      (mul_pos (by norm_num) LPositive)).mp spatialRatio
    nlinarith
  have distanceBudget :
      L * (2 * (epsilon + final.box.diagonalSq)) < delta / 8 := by
    calc
      L * (2 * (epsilon + final.box.diagonalSq)) ≤
          L * (2 * (epsilon + epsilon)) := by
        apply mul_le_mul_of_nonneg_left _ LPositive.le
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl finalDiagonal) (by norm_num)
      _ = 4 * L * spatial ^ 2 := by
        dsimp only [epsilon]
        ring
      _ ≤ 4 * L * spatial :=
        mul_le_mul_of_nonneg_left spatialSqLe
          (mul_nonneg (by norm_num) LPositive.le)
      _ ≤ delta / 16 := by nlinarith
      _ < delta / 8 := by linarith
  exact
    { state := final
      refines := finalRefinesSmall.trans smallRefinesCurrent
      epsilon := epsilon
      epsilonPositive := epsilonPositive
      epsilonAtMostOne := epsilonAtMostOne
      centerResidual := by
        simpa only [delta, final] using centerResidual
      distanceBudget := by
        simpa only [delta, L, final] using distanceBudget }

/-- A rational point on a zero-count arc cannot lie within the requested
sampler distance of a box satisfying the two displayed finite residual
budgets. -/
theorem ClearEvidence.not_near_box
    {p : GaussianPolynomial} {arc : BoundaryArc p}
    (clear : ClearEvidence p arc)
    {ambient box : RatBox} (refines : box.Refines ambient)
    {epsilon t margin : ℚ} (epsilonAtMostOne : epsilon ≤ 1)
    (marginPositive : 0 < margin)
    (marginLe : margin ≤ clear.certificate.bound)
    (tLower : arc.interval.lower ≤ t) (tUpper : t ≤ arc.interval.upper)
    (near : WithinSqOfBox box (arc.path.value t) epsilon)
    (centerResidual :
      normSq (p.eval box.center) < margin / 8)
    (distanceBudget :
      denseLipschitzBound p (nearbyAmbient ambient) *
          (2 * (epsilon + box.diagonalSq)) <
        margin / 8) : False := by
  rcases near with ⟨witness, witnessInBox, pointDistance⟩
  let point := arc.path.value t
  have centerInAmbient : ambient.Contains box.center :=
    refines.contains box.contains_center
  have centerInNearby : (nearbyAmbient ambient).Contains box.center :=
    nearbyAmbient_contains centerInAmbient
  have pointInNearby : (nearbyAmbient ambient).Contains point := by
    apply nearbyAmbient_contains_of_withinSqOfBox refines epsilonAtMostOne
    exact ⟨witness, witnessInBox, pointDistance⟩
  have witnessDistance : normSq (witness - box.center) ≤ box.diagonalSq :=
    RatBox.normSq_sub_le_diagonalSq witnessInBox box.contains_center
  have pointDecomposition :
      point - box.center = (point - witness) + (witness - box.center) := by
    ext <;> simp only [sub_re, sub_im, add_re, add_im] <;> ring
  have pointCenterDistance :
      normSq (point - box.center) <
        2 * (epsilon + box.diagonalSq) := by
    rw [pointDecomposition]
    apply (normSq_add_le_two (point - witness)
      (witness - box.center)).trans_lt
    exact mul_lt_mul_of_pos_left
      (add_lt_add_of_lt_of_le pointDistance witnessDistance) (by norm_num)
  have evaluationDifference :
      normSq (p.eval point - p.eval box.center) <
        margin / 8 := by
    have lipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound
      p pointInNearby centerInNearby
    have scaledDistance :
        denseLipschitzBound p (nearbyAmbient ambient) *
            normSq (point - box.center) <
          denseLipschitzBound p (nearbyAmbient ambient) *
            (2 * (epsilon + box.diagonalSq)) :=
      mul_lt_mul_of_pos_left pointCenterDistance
        (denseLipschitzBound_pos p (nearbyAmbient ambient))
    have evaluationDistance :
        normSq (p.eval point - p.eval box.center) <
          denseLipschitzBound p (nearbyAmbient ambient) *
            (2 * (epsilon + box.diagonalSq)) := by
      have scaledDistance' :
          denseLipschitzBound p (nearbyAmbient ambient) *
              normSq (point + -box.center) <
            denseLipschitzBound p (nearbyAmbient ambient) *
              (2 * (epsilon + box.diagonalSq)) := by
        simpa only [GaussianRat.sub_eq_add_neg] using scaledDistance
      simpa only [GaussianRat.sub_eq_add_neg] using
        lipschitz.trans_lt scaledDistance'
    exact evaluationDistance.trans distanceBudget
  have pointEvaluation :
      normSq (p.eval point) < margin / 2 := by
    have decomposition :
        (p.eval point - p.eval box.center) + p.eval box.center =
          p.eval point := by
      ext <;> simp only [sub_re, sub_im, add_re, add_im] <;> ring
    have sumBound := normSq_add_le_two
      (p.eval point - p.eval box.center) (p.eval box.center)
    rw [decomposition] at sumBound
    nlinarith
  have clearanceLower : clear.certificate.bound ≤ normSq (p.eval point) :=
    clear.certificate.lower t tLower tUpper
      (arc.denominator.denominator_ne tLower tUpper)
  nlinarith

/-- Quantitative sampler form of the exclusion theorem.  Once a parameter
descendant has the computed small width, no point of that arc cell can lie in
the refined root box. -/
theorem ClearEvidence.no_intersection
    {p : GaussianPolynomial} {arc : BoundaryArc p}
    (clear : ClearEvidence p arc)
    {ambient box : RatBox} (refines : box.Refines ambient)
    {cell : RationalInterval} (cellRefines : cell.Refines arc.interval)
    (cellProper : cell.Proper) {epsilon margin : ℚ}
    (epsilonPositive : 0 < epsilon) (epsilonAtMostOne : epsilon ≤ 1)
    (marginPositive : 0 < margin)
    (marginLe : margin ≤ clear.certificate.bound)
    (widthSmall : cell.width ≤ CCLIntersectionSampler.samplingWidth
      arc.path arc.interval arc.denominator epsilon)
    (centerResidual :
      normSq (p.eval box.center) < margin / 8)
    (distanceBudget :
      denseLipschitzBound p (nearbyAmbient ambient) *
          (2 * (epsilon + box.diagonalSq)) <
        margin / 8) :
    ¬∃ intersectionParameter : ℚ,
      cell.lower ≤ intersectionParameter ∧
      intersectionParameter ≤ cell.upper ∧
      box.Contains (arc.path.value intersectionParameter) := by
  rintro ⟨intersectionParameter, parameterLower, parameterUpper, intersection⟩
  let sample := FTA.RationalPolynomialBounds.midpoint cell.lower cell.upper
  have sampleLowerCell : cell.lower ≤ sample :=
    (FTA.RationalPolynomialBounds.lower_lt_midpoint cellProper).le
  have sampleUpperCell : sample ≤ cell.upper :=
    (FTA.RationalPolynomialBounds.midpoint_lt_upper cellProper).le
  have sampleLower : arc.interval.lower ≤ sample :=
    cellRefines.1.trans sampleLowerCell
  have sampleUpper : sample ≤ arc.interval.upper :=
    sampleUpperCell.trans cellRefines.2
  have near : WithinSqOfBox box (arc.path.value sample) epsilon := by
    simpa only [sample] using midpoint_withinSqOfBox arc.denominator
      cellRefines cellProper epsilonPositive widthSmall
      parameterLower parameterUpper intersection
  exact FTA.CCLClearanceExclusion.ClearEvidence.not_near_box clear
    refines epsilonAtMostOne marginPositive marginLe
    sampleLower sampleUpper near centerResidual distanceBudget

/-- All-clear family specialization: the single computed positive minimum is
simultaneously valid for every finite arc position. -/
theorem AllClear.no_intersectionAt
    {p : GaussianPolynomial} {arcs : List (BoundaryArc p)}
    (evidence : AllClear p arcs) (i : Fin arcs.length)
    {ambient box : RatBox} (refines : box.Refines ambient)
    {cell : RationalInterval}
    (cellRefines : cell.Refines (arcs.get i).interval)
    (cellProper : cell.Proper) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) (epsilonAtMostOne : epsilon ≤ 1)
    (widthSmall : cell.width ≤ CCLIntersectionSampler.samplingWidth
      (arcs.get i).path (arcs.get i).interval
        (arcs.get i).denominator epsilon)
    (centerResidual :
      normSq (p.eval box.center) < evidence.uniformClearance / 8)
    (distanceBudget :
      denseLipschitzBound p (nearbyAmbient ambient) *
          (2 * (epsilon + box.diagonalSq)) <
        evidence.uniformClearance / 8) :
    ¬∃ intersectionParameter : ℚ,
      cell.lower ≤ intersectionParameter ∧
      intersectionParameter ≤ cell.upper ∧
      box.Contains ((arcs.get i).path.value intersectionParameter) := by
  apply FTA.CCLClearanceExclusion.ClearEvidence.no_intersection
    (evidence.get i) refines cellRefines cellProper
    epsilonPositive epsilonAtMostOne evidence.uniformClearance_pos
    (evidence.uniformClearance_le_certificate i) widthSmall
    centerResidual distanceBudget

/-- Every sufficiently sampled parameter descendant is excluded from the
explicitly refined all-clear track box. -/
theorem RefinementOutput.no_intersectionAt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : RootTrackSeparation.WindingOneState p ambient}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (output : RefinementOutput p ambient current evidence)
    (i : Fin arcs.length) {cell : RationalInterval}
    (cellRefines : cell.Refines (arcs.get i).interval)
    (cellProper : cell.Proper)
    (widthSmall : cell.width ≤ CCLIntersectionSampler.samplingWidth
      (arcs.get i).path (arcs.get i).interval
        (arcs.get i).denominator output.epsilon) :
    ¬∃ intersectionParameter : ℚ,
      cell.lower ≤ intersectionParameter ∧
      intersectionParameter ≤ cell.upper ∧
      output.state.box.Contains
        ((arcs.get i).path.value intersectionParameter) := by
  exact FTA.CCLClearanceExclusion.AllClear.no_intersectionAt
    evidence i output.state.refinesAmbient cellRefines cellProper
    output.epsilonPositive output.epsilonAtMostOne widthSmall
    output.centerResidual output.distanceBudget

/-- Running the sampler at its computed depth removes the auxiliary width
premise: no rational parameter on any cleared arc can map into the refined
track box. -/
theorem RefinementOutput.no_arc_intersectionAt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : RootTrackSeparation.WindingOneState p ambient}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (output : RefinementOutput p ambient current evidence)
    (i : Fin arcs.length) :
    ¬∃ t : ℚ,
      (arcs.get i).interval.lower ≤ t ∧
      t ≤ (arcs.get i).interval.upper ∧
      output.state.box.Contains ((arcs.get i).path.value t) := by
  rintro ⟨t, lower, upper, contains⟩
  let arc := arcs.get i
  rcases samplingCells_cover arc.path arc.interval arc.denominator
      arc.proper output.epsilon output.epsilonPositive lower upper with
    ⟨cell, _member, cellLower, cellUpper⟩
  exact output.no_intersectionAt i cell.refines cell.proper cell.widthSmall
    ⟨t, cellLower, cellUpper, contains⟩

/-- Membership form of `no_arc_intersectionAt`, convenient when source/arc
alignment recovers a cleared boundary by list membership rather than index. -/
theorem RefinementOutput.no_arc_intersection_of_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : RootTrackSeparation.WindingOneState p ambient}
    {arcs : List (BoundaryArc p)} {evidence : AllClear p arcs}
    (output : RefinementOutput p ambient current evidence)
    {arc : BoundaryArc p} (member : arc ∈ arcs) :
    ¬∃ t : ℚ,
      arc.interval.lower ≤ t ∧ t ≤ arc.interval.upper ∧
      output.state.box.Contains (arc.path.value t) := by
  obtain ⟨i, equality⟩ := List.mem_iff_get.mp member
  simpa only [equality] using output.no_arc_intersectionAt i

end CCLClearanceExclusion
end FTA
