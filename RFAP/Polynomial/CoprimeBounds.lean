import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ShrinkingTrack
import RFAP.Polynomial.Squarefree

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace RFAP.CoprimeBounds

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds
open RFAP.LocalExtraction
open RFAP.Winding

/-- Residual threshold for the left member of a displayed Bézout pair. -/
def leftThreshold
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (ambient : Box) : Coordinate :=
  1 / (16 * denseEvalNormMajorant coprime.left ambient)

/-- Positive squared-norm margin forced on the right member once the left
residual is below `leftThreshold`. -/
def rightMargin
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (ambient : Box) : Coordinate :=
  1 / (16 * denseEvalNormMajorant coprime.right ambient)

theorem leftThreshold_pos
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (ambient : Box) : 0 < leftThreshold coprime ambient := by
  apply RFAP.ConstructiveFraction.div_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (denseEvalNormMajorant_pos coprime.left ambient)

theorem rightMargin_pos
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (ambient : Box) : 0 < rightMargin coprime ambient := by
  apply RFAP.ConstructiveFraction.div_pos_direct (by decide)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (denseEvalNormMajorant_pos coprime.right ambient)

private theorem majorant_mul_scaled_inverse_le
    {majorant : Coordinate} (positive : 0 < majorant) :
    majorant * (1 / (16 * majorant)) ≤ (1 / 16 : Coordinate) := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 16 by decide)).mpr
  calc
    (majorant * (1 / (16 * majorant))) * 16 =
        (1 / (16 * majorant)) * (16 * majorant) := by ring1
    _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
      (16 * majorant)
      (ne_of_gt (RFAP.ConstructiveFraction.mul_pos_direct
        (by decide) positive))
    _ ≤ 1 := le_rfl

/-- The finite Bézout identity gives a uniform right-value margin wherever
the displayed left residual is sufficiently small. -/
theorem rightMargin_le_of_left_small
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (ambient : Box) {z : Gaussian} (inside : ambient.Contains z)
    (small : normSq (p.eval z) ≤ leftThreshold coprime ambient) :
    rightMargin coprime ambient ≤ normSq (q.eval z) := by
  let leftMajorant := denseEvalNormMajorant coprime.left ambient
  let rightMajorant := denseEvalNormMajorant coprime.right ambient
  let leftValue := coprime.left.eval z
  let rightValue := coprime.right.eval z
  let pValue := p.eval z
  let qValue := q.eval z
  have leftMajorantPositive : 0 < leftMajorant :=
    denseEvalNormMajorant_pos coprime.left ambient
  have rightMajorantPositive : 0 < rightMajorant :=
    denseEvalNormMajorant_pos coprime.right ambient
  have leftBound : normSq leftValue ≤ leftMajorant :=
    normSq_eval_le_denseEvalNormMajorant coprime.left inside
  have rightBound : normSq rightValue ≤ rightMajorant :=
    normSq_eval_le_denseEvalNormMajorant coprime.right inside
  by_cases marginBound : rightMargin coprime ambient ≤ normSq qValue
  · exact marginBound
  · have qBound : normSq qValue ≤ rightMargin coprime ambient :=
      (lt_of_not_ge marginBound).le
    have leftProduct : normSq leftValue * normSq pValue ≤
        leftMajorant * leftThreshold coprime ambient :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftBound small
        (normSq_nonneg pValue) leftMajorantPositive.le
    have rightProduct : normSq rightValue * normSq qValue ≤
        rightMajorant * rightMargin coprime ambient :=
      RFAP.ConstructiveFraction.mul_le_mul_direct rightBound qBound
        (normSq_nonneg qValue) rightMajorantPositive.le
    have leftScaled : leftMajorant * leftThreshold coprime ambient ≤
        (1 / 16 : Coordinate) := by
      exact majorant_mul_scaled_inverse_le leftMajorantPositive
    have rightScaled : rightMajorant * rightMargin coprime ambient ≤
        (1 / 16 : Coordinate) := by
      exact majorant_mul_scaled_inverse_le rightMajorantPositive
    have sumNorm := normSq_add_le_two
      (leftValue * pValue) (rightValue * qValue)
    have bezout : 1 = leftValue * pValue + rightValue * qValue :=
      coprime.identity z
    have impossible : (1 : Coordinate) ≤ 1 / 4 := by
      calc
        (1 : Coordinate) =
            normSq (leftValue * pValue + rightValue * qValue) := by
          rw [← bezout, normSq_one]
        _ ≤ 2 * (normSq (leftValue * pValue) +
              normSq (rightValue * qValue)) := sumNorm
        _ = 2 * (normSq leftValue * normSq pValue +
              normSq rightValue * normSq qValue) := by
          rw [normSq_mul, normSq_mul]
        _ ≤ 2 * ((1 / 16 : Coordinate) + 1 / 16) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.trans leftScaled)
              (rightProduct.trans rightScaled)) (by decide)
        _ = 1 / 4 := by decide
    exact ((show ¬ ((1 : Coordinate) ≤ 1 / 4) by decide)
      impossible).elim

/-- Every displayed point of a winding-one box has a residual bounded by
four times the ambient Lipschitz coefficient and the squared diagonal. -/
theorem normSq_eval_le_four_lipschitz_diagonal
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (state : WindingOneState p ambient) {z : Gaussian}
    (inside : state.box.Contains z) :
    normSq (p.eval z) ≤
      4 * denseLipschitzBound p ambient * state.box.diagonalSq := by
  have anchorResidual :=
    anchor_residual_le_of_quadrupledBoxWinding_ne_zero p degreePositive
      state.refinesAmbient state.proper state.raw.rawWinding_ne
  have variation := normSq_eval_sub_anchor_le p state.refinesAmbient inside
  calc
    normSq (p.eval z) =
        normSq ((p.eval z - p.eval state.box.anchor) +
          p.eval state.box.anchor) := by
      congr 1
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, sub_re, sub_im] <;> ring1
    _ ≤ 2 * (normSq (p.eval z - p.eval state.box.anchor) +
          normSq (p.eval state.box.anchor)) := normSq_add_le_two _ _
    _ ≤ 2 * (anchorResidualBound p ambient state.box +
          anchorResidualBound p ambient state.box) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = 4 * denseLipschitzBound p ambient * state.box.diagonalSq := by
      simp only [anchorResidualBound]
      ring1

/-- A positive request small enough to force the left residual threshold and
make the right polynomial locally constant in winding. -/
def protectionRadius
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (pAmbient : Box) : Coordinate :=
  min 1 (min
    (leftThreshold coprime pAmbient /
      (8 * denseLipschitzBound p pAmbient))
    (rightMargin coprime pAmbient /
      (2 * denseLipschitzBound q pAmbient)))

theorem protectionRadius_pos
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (pAmbient : Box) : 0 < protectionRadius coprime pAmbient := by
  exact lt_min (by decide) (lt_min
    (RFAP.ConstructiveFraction.div_pos_direct
      (leftThreshold_pos coprime pAmbient)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p pAmbient)))
    (RFAP.ConstructiveFraction.div_pos_direct
      (rightMargin_pos coprime pAmbient)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos q pAmbient))))

private theorem protectionRadius_sq_le
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (pAmbient : Box) :
    protectionRadius coprime pAmbient ^ 2 ≤
      protectionRadius coprime pAmbient := by
  let radius := protectionRadius coprime pAmbient
  have radiusPositive : 0 < radius := protectionRadius_pos coprime pAmbient
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  rw [pow_two]
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    radiusLeOne radiusPositive.le).trans_eq (one_mul radius)

/-- Refining one track at the explicit protection radius. -/
def protectedState
    {p q : GaussianPolynomial} {pAmbient : Box}
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) : WindingOneState p pAmbient :=
  track.refine current (protectionRadius coprime pAmbient)
    (protectionRadius_pos coprime pAmbient)

theorem protectedState_left_small
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian}
    (inside : (protectedState coprime track current).box.Contains z) :
    normSq (p.eval z) ≤ leftThreshold coprime pAmbient := by
  let radius := protectionRadius coprime pAmbient
  let state := protectedState coprime track current
  have residual := normSq_eval_le_four_lipschitz_diagonal
    pDegreePositive state inside
  have diagonal := track.accurate current radius
    (protectionRadius_pos coprime pAmbient)
  have radiusSquare := protectionRadius_sq_le coprime pAmbient
  have radiusBudget : radius ≤ leftThreshold coprime pAmbient /
      (8 * denseLipschitzBound p pAmbient) :=
    (min_le_right (1 : Coordinate) _).trans (min_le_left _ _)
  have scaled : radius * (8 * denseLipschitzBound p pAmbient) ≤
      leftThreshold coprime pAmbient :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p pAmbient))).mp radiusBudget
  calc
    normSq (p.eval z) ≤
        4 * denseLipschitzBound p pAmbient * state.box.diagonalSq := residual
    _ ≤ 4 * denseLipschitzBound p pAmbient * radius ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p pAmbient)).le
    _ ≤ 4 * denseLipschitzBound p pAmbient * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusSquare
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p pAmbient)).le
    _ ≤ radius * (8 * denseLipschitzBound p pAmbient) := by
      have radiusNonnegative :=
        (protectionRadius_pos coprime pAmbient).le
      have coefficient :
          4 * denseLipschitzBound p pAmbient ≤
            8 * denseLipschitzBound p pAmbient :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (4 : Coordinate) ≤ 8 by decide)
          (denseLipschitzBound_pos p pAmbient).le
      calc
        4 * denseLipschitzBound p pAmbient * radius =
            radius * (4 * denseLipschitzBound p pAmbient) := by ring1
        _ ≤ radius * (8 * denseLipschitzBound p pAmbient) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            coefficient radiusNonnegative
    _ ≤ leftThreshold coprime pAmbient := by
      simpa only [radius] using scaled

/-- The other coprime polynomial has a uniform positive lower bound on the
whole protected box. -/
theorem protectedState_right_lower
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) {z : Gaussian}
    (inside : (protectedState coprime track current).box.Contains z) :
    rightMargin coprime pAmbient ≤ normSq (q.eval z) :=
  rightMargin_le_of_left_small coprime pAmbient
    ((protectedState coprime track current).refinesAmbient.contains inside)
    (protectedState_left_small pDegreePositive coprime track current inside)

/-- The forced right margin is in particular a constructive boundary
clearance certificate. -/
def protectedState_rightBoundaryClearance
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) :
    BoundaryClearance q (protectedState coprime track current).box where
  bound := rightMargin coprime pAmbient
  positive := rightMargin_pos coprime pAmbient
  lower := fun z boundary =>
    protectedState_right_lower (z := z) pDegreePositive coprime track current
      boundary.1

/-- On the protected left track, the other positive-degree polynomial has
zero raw winding. -/
theorem protectedState_rightWinding_zero
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient) :
    quadrupledBoxWinding q (protectedState coprime track current).box = 0 := by
  let radius := protectionRadius coprime pAmbient
  let state := protectedState coprime track current
  have radiusSquare := protectionRadius_sq_le coprime pAmbient
  have radiusBudget : radius ≤ rightMargin coprime pAmbient /
      (2 * denseLipschitzBound q pAmbient) :=
    (min_le_right (1 : Coordinate) _).trans (min_le_right _ _)
  have scaled : radius * (2 * denseLipschitzBound q pAmbient) ≤
      rightMargin coprime pAmbient :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos q pAmbient))).mp radiusBudget
  have diagonal := track.accurate current radius
    (protectionRadius_pos coprime pAmbient)
  have variationStrict : anchorResidualBound q pAmbient state.box <
      rightMargin coprime pAmbient := by
    have radiusPositive := protectionRadius_pos coprime pAmbient
    calc
      anchorResidualBound q pAmbient state.box =
          denseLipschitzBound q pAmbient * state.box.diagonalSq := rfl
      _ ≤ denseLipschitzBound q pAmbient * radius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
          (denseLipschitzBound_pos q pAmbient).le
      _ ≤ denseLipschitzBound q pAmbient * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusSquare
          (denseLipschitzBound_pos q pAmbient).le
      _ < radius * (2 * denseLipschitzBound q pAmbient) := by
        have productPositive : 0 <
            denseLipschitzBound q pAmbient * radius :=
          RFAP.ConstructiveFraction.mul_pos_direct
            (denseLipschitzBound_pos q pAmbient) radiusPositive
        calc
          denseLipschitzBound q pAmbient * radius =
              0 + denseLipschitzBound q pAmbient * radius := by ring1
          _ < denseLipschitzBound q pAmbient * radius +
              denseLipschitzBound q pAmbient * radius :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct productPositive _
          _ = radius * (2 * denseLipschitzBound q pAmbient) := by ring1
      _ ≤ rightMargin coprime pAmbient := scaled
  have anchorLower : rightMargin coprime pAmbient ≤
      normSq (q.eval state.box.anchor) :=
    protectedState_right_lower pDegreePositive coprime track current
      state.box.contains_anchor
  exact quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    q qDegreePositive state.refinesAmbient state.proper
      (variationStrict.trans_le anchorLower)

/-! ## Uniform residual refinement and cross-polynomial separation -/

/-- Positive radius making every point of the requested winding-one box have
residual strictly below a supplied positive threshold. -/
def uniformResidualRadius
    (p : GaussianPolynomial) (ambient : Box) (threshold : Coordinate) :
    Coordinate :=
  min 1 (threshold / (8 * denseLipschitzBound p ambient))

theorem uniformResidualRadius_pos
    (p : GaussianPolynomial) (ambient : Box) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    0 < uniformResidualRadius p ambient threshold := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct thresholdPositive
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p ambient)))

private theorem uniformResidualRadius_sq_le
    (p : GaussianPolynomial) (ambient : Box) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    uniformResidualRadius p ambient threshold ^ 2 ≤
      uniformResidualRadius p ambient threshold := by
  let radius := uniformResidualRadius p ambient threshold
  have positive := uniformResidualRadius_pos p ambient thresholdPositive
  have leOne : radius ≤ 1 := min_le_left _ _
  rw [pow_two]
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    leOne positive.le).trans_eq (one_mul radius)

def uniformlySmallState
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold) :
    WindingOneState p ambient :=
  track.refine current (uniformResidualRadius p ambient threshold)
    (uniformResidualRadius_pos p ambient thresholdPositive)

theorem uniformlySmallState_residual_lt
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient)
    {threshold : Coordinate} (thresholdPositive : 0 < threshold)
    {z : Gaussian}
    (inside : (uniformlySmallState track current threshold
      thresholdPositive).box.Contains z) :
    normSq (p.eval z) < threshold := by
  let radius := uniformResidualRadius p ambient threshold
  let state := uniformlySmallState track current threshold thresholdPositive
  have residual := normSq_eval_le_four_lipschitz_diagonal
    degreePositive state inside
  have diagonal := track.accurate current radius
    (uniformResidualRadius_pos p ambient thresholdPositive)
  have radiusSquare := uniformResidualRadius_sq_le p ambient thresholdPositive
  have radiusBudget : radius ≤
      threshold / (8 * denseLipschitzBound p ambient) := min_le_right _ _
  have scaled : radius * (8 * denseLipschitzBound p ambient) ≤ threshold :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p ambient))).mp radiusBudget
  have positiveProduct : 0 < denseLipschitzBound p ambient * radius :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (denseLipschitzBound_pos p ambient)
      (uniformResidualRadius_pos p ambient thresholdPositive)
  calc
    normSq (p.eval z) ≤
        4 * denseLipschitzBound p ambient * state.box.diagonalSq := residual
    _ ≤ 4 * denseLipschitzBound p ambient * radius ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p ambient)).le
    _ ≤ 4 * denseLipschitzBound p ambient * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusSquare
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p ambient)).le
    _ < radius * (8 * denseLipschitzBound p ambient) := by
      calc
        4 * denseLipschitzBound p ambient * radius =
            4 * (denseLipschitzBound p ambient * radius) := by ring1
        _ < 8 * (denseLipschitzBound p ambient * radius) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
            (show (4 : Coordinate) < 8 by decide) positiveProduct
        _ = radius * (8 * denseLipschitzBound p ambient) := by ring1
    _ ≤ threshold := scaled

/-- A left track protected by a Bézout margin is positively separated from a
right track refined below that same margin. -/
theorem protectedState_separated_uniformlySmallState
    {p q : GaussianPolynomial} {pAmbient qAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (pTrack : WindingOneTrack p pAmbient)
    (pCurrent : WindingOneState p pAmbient)
    (qTrack : WindingOneTrack q qAmbient)
    (qCurrent : WindingOneState q qAmbient) :
    (protectedState coprime pTrack pCurrent).box.Separated
      (uniformlySmallState qTrack qCurrent (rightMargin coprime pAmbient)
        (rightMargin_pos coprime pAmbient)).box := by
  let pState := protectedState coprime pTrack pCurrent
  let margin := rightMargin coprime pAmbient
  let marginPositive := rightMargin_pos coprime pAmbient
  let qState := uniformlySmallState qTrack qCurrent margin marginPositive
  by_cases separated : pState.box.Separated qState.box
  · exact separated
  · have overlap :=
      RFAP.Boxes.Box.contains_overlapPoint_of_not_separated
        separated
    let point := RFAP.Boxes.Box.overlapPoint pState.box qState.box
    have lower : margin ≤ normSq (q.eval point) := by
      exact protectedState_right_lower (z := point) pDegreePositive coprime
        pTrack pCurrent overlap.1
    have upper : normSq (q.eval point) < margin := by
      exact uniformlySmallState_residual_lt qDegreePositive qTrack qCurrent
        marginPositive overlap.2
    exact (not_lt_of_ge lower upper).elim

/-! ## Protection at any smaller positive request -/

/-- Refine a winding-one track at an explicitly supplied positive request.
The following lemmas require that request to be no larger than the relevant
Bézout protection radius. -/
def protectedStateAt
    {p : GaussianPolynomial} {pAmbient : Box}
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    (request : Coordinate) (requestPositive : 0 < request) :
    WindingOneState p pAmbient :=
  track.refine current request requestPositive

private theorem request_sq_le
    {p q : GaussianPolynomial} (coprime : CoprimeCertificate p q)
    (pAmbient : Box) {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient) :
    request ^ 2 ≤ request := by
  have requestLeOne : request ≤ 1 :=
    requestLe.trans (min_le_left _ _)
  rw [pow_two]
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    requestLeOne requestPositive.le).trans_eq (one_mul request)

theorem protectedStateAt_left_small
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient)
    {z : Gaussian}
    (inside : (protectedStateAt track current request requestPositive).box.Contains z) :
    normSq (p.eval z) ≤ leftThreshold coprime pAmbient := by
  let state := protectedStateAt track current request requestPositive
  have residual := normSq_eval_le_four_lipschitz_diagonal
    pDegreePositive state inside
  have diagonal := track.accurate current request requestPositive
  have requestSquare := request_sq_le coprime pAmbient requestPositive requestLe
  have radiusBudget : request ≤ leftThreshold coprime pAmbient /
      (8 * denseLipschitzBound p pAmbient) :=
    requestLe.trans ((min_le_right (1 : Coordinate) _).trans
      (min_le_left _ _))
  have scaled : request * (8 * denseLipschitzBound p pAmbient) ≤
      leftThreshold coprime pAmbient :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos p pAmbient))).mp radiusBudget
  calc
    normSq (p.eval z) ≤
        4 * denseLipschitzBound p pAmbient * state.box.diagonalSq := residual
    _ ≤ 4 * denseLipschitzBound p pAmbient * request ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p pAmbient)).le
    _ ≤ 4 * denseLipschitzBound p pAmbient * request :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct requestSquare
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (denseLipschitzBound_pos p pAmbient)).le
    _ ≤ request * (8 * denseLipschitzBound p pAmbient) := by
      have coefficient :
          4 * denseLipschitzBound p pAmbient ≤
            8 * denseLipschitzBound p pAmbient :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (4 : Coordinate) ≤ 8 by decide)
          (denseLipschitzBound_pos p pAmbient).le
      calc
        4 * denseLipschitzBound p pAmbient * request =
            request * (4 * denseLipschitzBound p pAmbient) := by ring1
        _ ≤ request * (8 * denseLipschitzBound p pAmbient) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            coefficient requestPositive.le
    _ ≤ leftThreshold coprime pAmbient := scaled

theorem protectedStateAt_right_lower
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient)
    {z : Gaussian}
    (inside : (protectedStateAt track current request requestPositive).box.Contains z) :
    rightMargin coprime pAmbient ≤ normSq (q.eval z) :=
  rightMargin_le_of_left_small coprime pAmbient
    ((protectedStateAt track current request requestPositive).refinesAmbient.contains
      inside)
    (protectedStateAt_left_small pDegreePositive coprime track current
      requestPositive requestLe inside)

def protectedStateAt_rightBoundaryClearance
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient) :
    BoundaryClearance q
      (protectedStateAt track current request requestPositive).box where
  bound := rightMargin coprime pAmbient
  positive := rightMargin_pos coprime pAmbient
  lower := fun _z boundary => protectedStateAt_right_lower
    pDegreePositive coprime track current requestPositive requestLe boundary.1

theorem protectedStateAt_rightWinding_zero
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qDegreePositive : 0 < q.natDegree)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient) :
    quadrupledBoxWinding q
      (protectedStateAt track current request requestPositive).box = 0 := by
  let state := protectedStateAt track current request requestPositive
  have requestSquare := request_sq_le coprime pAmbient requestPositive requestLe
  have radiusBudget : request ≤ rightMargin coprime pAmbient /
      (2 * denseLipschitzBound q pAmbient) :=
    requestLe.trans ((min_le_right (1 : Coordinate) _).trans
      (min_le_right _ _))
  have scaled : request * (2 * denseLipschitzBound q pAmbient) ≤
      rightMargin coprime pAmbient :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (denseLipschitzBound_pos q pAmbient))).mp radiusBudget
  have diagonal := track.accurate current request requestPositive
  have variationStrict : anchorResidualBound q pAmbient state.box <
      rightMargin coprime pAmbient := by
    calc
      anchorResidualBound q pAmbient state.box =
          denseLipschitzBound q pAmbient * state.box.diagonalSq := rfl
      _ ≤ denseLipschitzBound q pAmbient * request ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
          (denseLipschitzBound_pos q pAmbient).le
      _ ≤ denseLipschitzBound q pAmbient * request :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct requestSquare
          (denseLipschitzBound_pos q pAmbient).le
      _ < request * (2 * denseLipschitzBound q pAmbient) := by
        have productPositive : 0 < denseLipschitzBound q pAmbient * request :=
          RFAP.ConstructiveFraction.mul_pos_direct
            (denseLipschitzBound_pos q pAmbient) requestPositive
        calc
          denseLipschitzBound q pAmbient * request =
              0 + denseLipschitzBound q pAmbient * request := by ring1
          _ < denseLipschitzBound q pAmbient * request +
              denseLipschitzBound q pAmbient * request :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct productPositive _
          _ = request * (2 * denseLipschitzBound q pAmbient) := by ring1
      _ ≤ rightMargin coprime pAmbient := scaled
  have anchorLower : rightMargin coprime pAmbient ≤
      normSq (q.eval state.box.anchor) :=
    protectedStateAt_right_lower pDegreePositive coprime track current
      requestPositive requestLe state.box.contains_anchor
  exact quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    q qDegreePositive state.refinesAmbient state.proper
      (variationStrict.trans_le anchorLower)

/-- The same zero-winding conclusion for every displayed nonzero right
polynomial, with the constant case discharged by its exact normalized
constant winding. -/
theorem protectedStateAt_rightWinding_zero_of_nonzero
    {p q : GaussianPolynomial} {pAmbient : Box}
    (pDegreePositive : 0 < p.natDegree)
    (qNonzero : q.isZero = false)
    (coprime : CoprimeCertificate p q)
    (track : WindingOneTrack p pAmbient)
    (current : WindingOneState p pAmbient)
    {request : Coordinate} (requestPositive : 0 < request)
    (requestLe : request ≤ protectionRadius coprime pAmbient) :
    quadrupledBoxWinding q
      (protectedStateAt track current request requestPositive).box = 0 := by
  by_cases degreeZero : q.natDegree = 0
  · have normalizedConstant : q.normalize =
        RFAP.GlobalWinding.gaussianConstant q.leadingCoeff :=
      RFAP.ComputablePolynomial.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
        qNonzero degreeZero
    calc
      quadrupledBoxWinding q
          (protectedStateAt track current request requestPositive).box =
          quadrupledBoxWinding q.normalize
            (protectedStateAt track current request requestPositive).box :=
        (quadrupledBoxWinding_normalize q _).symm
      _ = quadrupledBoxWinding
            (RFAP.GlobalWinding.gaussianConstant q.leadingCoeff)
            (protectedStateAt track current request requestPositive).box := by
        rw [normalizedConstant]
      _ = 0 :=
        RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant
          (RFAP.ComputablePolynomial.DensePolynomial.leadingCoeff_ne_zero
            qNonzero) _
  · exact protectedStateAt_rightWinding_zero pDegreePositive
      (Nat.pos_of_ne_zero degreeZero) coprime track current requestPositive
      requestLe

end RFAP.CoprimeBounds
