import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ShrinkingTrack

/-!
# Finite separation of constructive winding-one tracks

Two separated winding-one tracks cannot both remain in a sufficiently small
common box.  The proof uses only finite residual refinements, the displayed
squarefree Bézout identity, and the coefficient-scanned Taylor bound.  This
replaces the older resultant-root argument and never forms a set of roots.
-/

namespace RFAP.TrackSeparation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev DerivativeSeparation :=
  RFAP.LocalExtraction.DerivativeSeparation
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds
open RFAP.LocalExtraction

/-- Squared-diameter threshold on which the derivative term dominates the
Taylor remainder. -/
def separatedUniquenessDiagonalThreshold
    {p : GaussianPolynomial} (ambient : Box)
    (separation : DerivativeSeparation p ambient) : Coordinate :=
  separation.margin / (8 * denseTaylorRemainderBound p ambient)

theorem separatedUniquenessDiagonalThreshold_pos
    {p : GaussianPolynomial} (ambient : Box)
    (separation : DerivativeSeparation p ambient) :
    0 < separatedUniquenessDiagonalThreshold ambient separation := by
  exact RFAP.ConstructiveFraction.div_pos_direct separation.margin_pos
    (RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide))
      (denseTaylorRemainderBound_pos p ambient))

/-- Squarefree specialization retained for the finite-packing interface. -/
def uniquenessDiagonalThreshold
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) : Coordinate :=
  separatedUniquenessDiagonalThreshold
    ambient (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)

theorem uniquenessDiagonalThreshold_pos
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) : 0 < uniquenessDiagonalThreshold squarefree ambient := by
  exact separatedUniquenessDiagonalThreshold_pos
    ambient (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)

/-- Positive residual budget chosen after a concrete separation gap is
known. -/
def separatedPairResidualThreshold
    {p : GaussianPolynomial} (ambient : Box)
    (separation : DerivativeSeparation p ambient)
    (gap : Coordinate) : Coordinate :=
  min separation.threshold
    ((1 / 32 : Coordinate) * (separation.margin * gap ^ 2))

theorem separatedPairResidualThreshold_pos
    {p : GaussianPolynomial} (ambient : Box)
    (separation : DerivativeSeparation p ambient)
    {gap : Coordinate} (gapPositive : 0 < gap) :
    0 < separatedPairResidualThreshold ambient separation gap := by
  exact lt_min separation.threshold_pos
    (RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 1) (by decide))
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 32) (by decide)))
      (RFAP.ConstructiveFraction.mul_pos_direct separation.margin_pos
        (RFAP.ConstructiveFraction.pow_pos_direct gapPositive 2)))

/-- Squarefree specialization of the separated residual budget. -/
def pairResidualThreshold
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) (gap : Coordinate) : Coordinate :=
  separatedPairResidualThreshold
    ambient (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient) gap

theorem pairResidualThreshold_pos
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (ambient : Box) {gap : Coordinate} (gapPositive : 0 < gap) :
    0 < pairResidualThreshold squarefree ambient gap := by
  exact separatedPairResidualThreshold_pos
    ambient (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)
      gapPositive

/-- Radius whose squared-diagonal request forces the anchor residual below a
given positive threshold. -/
def residualRefinementRadius
    (p : GaussianPolynomial) (ambient : Box)
    (threshold : Coordinate) : Coordinate :=
  min 1 (threshold / denseLipschitzBound p ambient)

theorem residualRefinementRadius_pos
    (p : GaussianPolynomial) (ambient : Box) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    0 < residualRefinementRadius p ambient threshold := by
  exact lt_min
    (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
    (RFAP.ConstructiveFraction.div_pos_direct thresholdPositive
      (denseLipschitzBound_pos p ambient))

theorem lipschitz_mul_residualRadius_sq_le
    (p : GaussianPolynomial) (ambient : Box) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    denseLipschitzBound p ambient *
        residualRefinementRadius p ambient threshold ^ 2 ≤ threshold := by
  let radius := residualRefinementRadius p ambient threshold
  let lipschitz := denseLipschitzBound p ambient
  have radiusPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusRatio : radius ≤ threshold / lipschitz := min_le_right _ _
  have lipschitzPositive := denseLipschitzBound_pos p ambient
  have squareLeRadius : radius ^ 2 ≤ radius := by
    rw [pow_two]
    calc
      radius * radius ≤ 1 * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          radiusLeOne radiusPositive.le
      _ = radius := by ring1
  have ratioScaled : radius * lipschitz ≤ threshold :=
    (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp radiusRatio
  calc
    lipschitz * radius ^ 2 ≤ lipschitz * radius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLeRadius
        lipschitzPositive.le
    _ = radius * lipschitz := by ring1
    _ ≤ threshold := ratioScaled

/-- One finite track call produces a rational anchor with the requested
residual. -/
theorem refined_anchor_residual_le
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) {threshold : Coordinate}
    (thresholdPositive : 0 < threshold) :
    let radius := residualRefinementRadius p ambient threshold
    let refined := track.refine current radius
      (residualRefinementRadius_pos p ambient thresholdPositive)
    normSq (p.eval refined.box.anchor) ≤ threshold := by
  let radius := residualRefinementRadius p ambient threshold
  let radiusPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  let refined := track.refine current radius radiusPositive
  have residual :=
    anchor_residual_le_of_quadrupledBoxWinding_ne_zero p degreePositive
      refined.refinesAmbient refined.proper refined.raw.rawWinding_ne
  have diagonal := track.accurate current radius radiusPositive
  calc
    normSq (p.eval refined.box.anchor) ≤
        anchorResidualBound p ambient refined.box := residual
    _ = denseLipschitzBound p ambient * refined.box.diagonalSq := rfl
    _ ≤ denseLipschitzBound p ambient * radius ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct diagonal
        (denseLipschitzBound_pos p ambient).le
    _ ≤ threshold := lipschitz_mul_residualRadius_sq_le p ambient
      thresholdPositive

/-- A concrete coordinate separation supplies a positive squared-distance
lower bound for every selected point of the two boxes. -/
theorem separated_normSq_lower
    {left right : Box} (separated : left.Separated right) :
    ∃ gap : Coordinate, 0 < gap ∧
      ∀ {u v : Gaussian}, left.Contains u → right.Contains v →
        gap ^ 2 ≤ normSq (u - v) := by
  let certificate := RFAP.Boxes.Box.separationCertificate separated
  exact ⟨certificate.gap, certificate.positive, certificate.lower⟩

/-- Two separated winding-one tracks cannot both be supported in a common box
below the finite Taylor uniqueness threshold supplied by an explicit
derivative-separation certificate. -/
theorem separated_tracks_not_supported_in_small_common_box_of_separation
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (separation : DerivativeSeparation p ambient)
    (leftTrack rightTrack : WindingOneTrack p ambient)
    (leftState rightState : WindingOneState p ambient)
    (separated : leftState.box.Separated rightState.box)
    (common : Box)
    (leftCommon : leftState.box.Refines common)
    (rightCommon : rightState.box.Refines common)
    (small : common.diagonalSq <
      separatedUniquenessDiagonalThreshold ambient separation) : False := by
  obtain ⟨gap, gapPositive, gapLower⟩ := separated_normSq_lower separated
  let threshold := separatedPairResidualThreshold ambient separation gap
  have thresholdPositive := separatedPairResidualThreshold_pos ambient
    separation gapPositive
  let radius := residualRefinementRadius p ambient threshold
  let radiusPositive := residualRefinementRadius_pos p ambient
    thresholdPositive
  let leftRefined := leftTrack.refine leftState radius radiusPositive
  let rightRefined := rightTrack.refine rightState radius radiusPositive
  let u := leftRefined.box.anchor
  let v := rightRefined.box.anchor
  have leftResidual : normSq (p.eval u) ≤ threshold := by
    simpa only [radius, radiusPositive, leftRefined, u] using
      refined_anchor_residual_le degreePositive leftTrack leftState
        thresholdPositive
  have rightResidual : normSq (p.eval v) ≤ threshold := by
    simpa only [radius, radiusPositive, rightRefined, v] using
      refined_anchor_residual_le degreePositive rightTrack rightState
        thresholdPositive
  have uLeft : leftState.box.Contains u :=
    (leftTrack.nested leftState radius radiusPositive).contains
      leftRefined.box.contains_anchor
  have vRight : rightState.box.Contains v :=
    (rightTrack.nested rightState radius radiusPositive).contains
      rightRefined.box.contains_anchor
  have uAmbient : ambient.Contains u := leftState.refinesAmbient.contains uLeft
  have vAmbient : ambient.Contains v := rightState.refinesAmbient.contains vRight
  have uCommon : common.Contains u := leftCommon.contains uLeft
  have vCommon : common.Contains v := rightCommon.contains vRight
  let distance := normSq (v - u)
  have distanceLower : gap ^ 2 ≤ distance := by
    have raw := gapLower uLeft vRight
    calc
      gap ^ 2 ≤ normSq (u - v) := raw
      _ = normSq (v - u) := by
        simp only [normSq, sub_re, sub_im]
        ring1
  have distancePositive : 0 < distance :=
    (RFAP.ConstructiveFraction.pow_pos_direct gapPositive 2).trans_le
      distanceLower
  have distanceUpper : distance ≤ common.diagonalSq :=
    common.normSq_sub_le_diagonalSq vCommon uCommon
  have distanceSmall : distance <
      separatedUniquenessDiagonalThreshold ambient separation :=
    distanceUpper.trans_lt small
  have derivativeLower : separation.margin ≤
      normSq ((RFAP.ConstructiveGCD.derivative p).eval u) := by
    exact separation.lower uAmbient
      (leftResidual.trans (min_le_left _ _))
  let error := p.eval v - p.eval u -
    (RFAP.ConstructiveGCD.derivative p).eval u * (v - u)
  have errorBound : normSq error ≤
      denseTaylorRemainderBound p ambient * distance ^ 2 := by
    exact normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      p vAmbient uAmbient
  have distanceScaled :
      distance * (8 * denseTaylorRemainderBound p ambient) ≤
        separation.margin :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 8) (by decide))
        (denseTaylorRemainderBound_pos p ambient))).mp distanceSmall.le
  have errorScaled : 8 * normSq error ≤
      separation.margin * distance := by
    have eightNonnegative : (0 : Coordinate) ≤ 8 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide)).le
    calc
      8 * normSq error ≤ 8 *
          (denseTaylorRemainderBound p ambient * distance ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct errorBound
          eightNonnegative
      _ = (distance *
          (8 * denseTaylorRemainderBound p ambient)) * distance := by ring1
      _ ≤ separation.margin * distance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          distanceScaled distancePositive.le
  have differenceBound : normSq (p.eval v - p.eval u) ≤ 4 * threshold := by
    calc
      normSq (p.eval v - p.eval u) ≤
          2 * (normSq (p.eval v) + normSq (p.eval u)) :=
        normSq_sub_le_two _ _
      _ ≤ 2 * (threshold + threshold) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add rightResidual leftResidual)
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 2) (by decide)).le
      _ = 4 * threshold := by ring1
  have inverseThirtyTwo :
      (32 : Coordinate) * (1 / 32) = 1 := by
    calc
      (32 : Coordinate) * (1 / 32) = (1 / 32) * 32 := by ring1
      _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 32
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 32) (by decide)).ne'
  have differenceScaled : 8 * normSq (p.eval v - p.eval u) ≤
      separation.margin * distance := by
    have eightNonnegative : (0 : Coordinate) ≤ 8 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 8) (by decide)).le
    have thirtyTwoNonnegative : (0 : Coordinate) ≤ 32 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 32) (by decide)).le
    calc
      8 * normSq (p.eval v - p.eval u) ≤ 8 * (4 * threshold) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          differenceBound eightNonnegative
      _ = 32 * threshold := by ring1
      _ ≤ 32 * ((1 / 32 : Coordinate) *
          (separation.margin * gap ^ 2)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (min_le_right _ _) thirtyTwoNonnegative
      _ = separation.margin * gap ^ 2 := by
        rw [show 32 * ((1 / 32 : Coordinate) *
            (separation.margin * gap ^ 2)) =
              (32 * (1 / 32 : Coordinate)) *
                (separation.margin * gap ^ 2) by ring1,
          inverseThirtyTwo]
        ring1
      _ ≤ separation.margin * distance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          distanceLower separation.margin_pos.le
  let linear := (RFAP.ConstructiveGCD.derivative p).eval u * (v - u)
  have linearIdentity : linear = (p.eval v - p.eval u) - error := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [linear, error, sub_re, sub_im, mul_re, mul_im] <;>
      ring1
  have linearUpper : normSq linear ≤
      2 * (normSq (p.eval v - p.eval u) + normSq error) := by
    rw [linearIdentity]
    exact normSq_sub_le_two _ _
  have fourLinearUpper : 4 * normSq linear ≤
      2 * (separation.margin * distance) := by
    have fourNonnegative : (0 : Coordinate) ≤ 4 :=
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 4) (by decide)).le
    calc
      4 * normSq linear ≤
          4 * (2 * (normSq (p.eval v - p.eval u) + normSq error)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct linearUpper
          fourNonnegative
      _ = 8 * normSq (p.eval v - p.eval u) + 8 * normSq error := by ring1
      _ ≤ separation.margin * distance +
          separation.margin * distance :=
        add_le_add differenceScaled errorScaled
      _ = 2 * (separation.margin * distance) := by ring1
  have linearLower : separation.margin * distance ≤
      normSq linear := by
    calc
      separation.margin * distance ≤
          normSq ((RFAP.ConstructiveGCD.derivative p).eval u) * distance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          derivativeLower distancePositive.le
      _ = normSq linear := by
        dsimp only [linear, distance]
        rw [normSq_mul]
  have impossible : 4 * (separation.margin * distance) ≤
      2 * (separation.margin * distance) :=
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct linearLower
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 4) (by decide)).le).trans fourLinearUpper
  have basePositive : 0 < separation.margin * distance :=
    RFAP.ConstructiveFraction.mul_pos_direct
      separation.margin_pos distancePositive
  have strict : 2 * (separation.margin * distance) <
      4 * (separation.margin * distance) := by
    calc
      2 * (separation.margin * distance) =
          0 + 2 * (separation.margin * distance) := by ring1
      _ < 2 * (separation.margin * distance) +
          2 * (separation.margin * distance) :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 2) (by decide)) basePositive)
          (2 * (separation.margin * distance))
      _ = 4 * (separation.margin * distance) := by ring1
  exact (not_le_of_gt strict impossible).elim

/-- Squarefree specialization used by the degree-sharp finite packing
argument. -/
theorem separated_tracks_not_supported_in_small_common_box
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (leftTrack rightTrack : WindingOneTrack p ambient)
    (leftState rightState : WindingOneState p ambient)
    (separated : leftState.box.Separated rightState.box)
    (common : Box)
    (leftCommon : leftState.box.Refines common)
    (rightCommon : rightState.box.Refines common)
    (small : common.diagonalSq <
      uniquenessDiagonalThreshold squarefree ambient) : False :=
  separated_tracks_not_supported_in_small_common_box_of_separation
    degreePositive
    (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)
    leftTrack rightTrack leftState rightState separated common leftCommon
    rightCommon small

end RFAP.TrackSeparation
