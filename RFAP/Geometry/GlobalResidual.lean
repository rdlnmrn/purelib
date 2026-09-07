import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.ResidualChordal
import RFAP.Isolation.BoxFTA

/-!
# Global residual localization

This module extends the local residual Newton construction to the
coefficient-computed large isolation square.  An explicit leading-term
estimate excludes small residuals outside that square.  Inside it, the
minimal `ProtectedAmbient` interface constructs a winding-one track without
assuming that the parent square itself has winding one; finite maximality
then assigns the track to one of the already isolated output tracks.

Every input and output point is a displayed Gaussian rational.  The global
classifier never constructs or quantifies over a completed root.
-/

namespace RFAP.GlobalResidual

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev ProtectedAmbient := RFAP.ResidualWinding.ProtectedAmbient
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.GlobalWinding

private theorem radius_sq_lt_normSq_of_lt
    {radius x y : Coordinate} (radiusPositive : 0 < radius)
    (outside : radius < x) :
    radius ^ 2 < x ^ 2 + y ^ 2 := by
  have xPositive : 0 < x := radiusPositive.trans outside
  have first : radius * radius < radius * x :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      radiusPositive outside
  have second : radius * x < x * x :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct outside xPositive
  calc
    radius ^ 2 < x ^ 2 := by
      simpa only [pow_two] using first.trans second
    _ ≤ x ^ 2 + y ^ 2 :=
      le_add_of_nonneg_right (RFAP.ConstructiveFraction.sq_nonneg_direct y)

/-- A point outside the coefficient-computed closed square has squared norm
strictly larger than the square radius. -/
theorem radiusSq_lt_normSq_of_not_largeSquare_contains
    (p : GaussianPolynomial) (sample : Gaussian)
    (outside : ¬(largeSquareBox p).Contains sample) :
    denseLargeSquareRadius p ^ 2 < normSq sample := by
  let radius := denseLargeSquareRadius p
  have radiusPositive : 0 < radius := denseLargeSquareRadius_pos p
  by_cases left : -radius ≤ sample.re
  · by_cases right : sample.re ≤ radius
    · by_cases bottom : -radius ≤ sample.im
      · by_cases top : sample.im ≤ radius
        · exact (outside (by
            change -radius ≤ sample.re ∧ sample.re ≤ radius ∧
              -radius ≤ sample.im ∧ sample.im ≤ radius
            exact ⟨left, right, bottom, top⟩)).elim
        · have beyond : radius < sample.im := lt_of_not_ge top
          change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
          have bound := radius_sq_lt_normSq_of_lt radiusPositive beyond
            (x := sample.im) (y := sample.re)
          simpa only [RFAP.ConstructiveFraction.add_comm] using bound
      · have beyondNegative : sample.im < -radius := lt_of_not_ge bottom
        have beyond : radius < -sample.im := by
          have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
            beyondNegative
          calc
            radius = -(-radius) := by ring1
            _ < -sample.im := negated
        change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
        have bound := radius_sq_lt_normSq_of_lt radiusPositive beyond
          (x := -sample.im) (y := sample.re)
        have squareIdentity : (-sample.im) ^ 2 = sample.im ^ 2 := by ring1
        rw [squareIdentity] at bound
        simpa only [RFAP.ConstructiveFraction.add_comm] using bound
    · have beyond : radius < sample.re := lt_of_not_ge right
      change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
      exact radius_sq_lt_normSq_of_lt radiusPositive beyond
  · have beyondNegative : sample.re < -radius := lt_of_not_ge left
    have beyond : radius < -sample.re := by
      have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct
        beyondNegative
      calc
        radius = -(-radius) := by ring1
        _ < -sample.re := negated
    change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
    have bound := radius_sq_lt_normSq_of_lt radiusPositive beyond
      (x := -sample.re) (y := sample.im)
    have squareIdentity : (-sample.re) ^ 2 = sample.re ^ 2 := by ring1
    rw [squareIdentity] at bound
    exact bound

/-- Coefficient upper bound for the leading monomial on the annulus ending
at twice the squared large-square radius. -/
def annularLeadingUpper (p : GaussianPolynomial) : Coordinate :=
  normSq p.leadingCoeff *
    (2 * denseLargeSquareRadius p ^ 2) ^ p.natDegree

theorem annularLeadingUpper_pos
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    0 < annularLeadingUpper p := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingPositive := normSq_pos (leadingCoeff_ne_zero polynomialNonzero)
  have radialPositive : 0 < 2 * denseLargeSquareRadius p ^ 2 :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.pow_pos_direct
        (denseLargeSquareRadius_pos p) 2)
  exact RFAP.ConstructiveFraction.mul_pos_direct leadingPositive
    (RFAP.ConstructiveFraction.pow_pos_direct radialPositive p.natDegree)

/-- Explicit positive residual below which a displayed sample cannot lie
outside the coefficient-computed isolation square.  The first branch is used
far from the square; the quotient branch is the finite annular Rouché gap. -/
def outsideResidualThreshold (p : GaussianPolynomial) : Coordinate :=
  min (largeSquareDominanceMargin p)
    (largeSquareDominanceMargin p ^ 2 / (4 * annularLeadingUpper p))

theorem outsideResidualThreshold_pos
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    0 < outsideResidualThreshold p := by
  have marginPositive := largeSquareDominanceMargin_pos degreePositive
  exact lt_min marginPositive
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct marginPositive 2)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (annularLeadingUpper_pos degreePositive)))

private theorem leadingNormSq_le_annularUpper
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {sample : Gaussian}
    (normUpper : normSq sample ≤ 2 * denseLargeSquareRadius p ^ 2) :
    normSq ((leadingMonomial p).eval sample) ≤ annularLeadingUpper p := by
  rw [leadingMonomial_eval degreePositive, normSq_mul, normSq_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.pow_le_pow_direct (normSq_nonneg sample)
      normUpper p.natDegree)
    (normSq_nonneg p.leadingCoeff)

/-- Ring rearrangement with the half-scale supplied as an opaque rational.
Keeping the scale as an argument prevents the normalization proof from
unfolding rational inversion through a generic division-ring instance. -/
private theorem weighted_scale_identity
    (leadingNorm sampleSq weight scale : Coordinate) (exponent : Nat) :
    (leadingNorm * (sampleSq * scale) - weight) * sampleSq ^ exponent =
      (leadingNorm * (sampleSq ^ exponent * sampleSq)) * scale -
        weight * sampleSq ^ exponent := by
  ring1

theorem outside_residual_lower_annulus
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {sample : Gaussian}
    (normLower : denseLargeSquareRadius p ^ 2 ≤ normSq sample)
    (normUpper : normSq sample ≤ 2 * denseLargeSquareRadius p ^ 2) :
    largeSquareDominanceMargin p ^ 2 / (4 * annularLeadingUpper p) ≤
      normSq (p.eval sample) := by
  let leading := (leadingMonomial p).eval sample
  let lower := (lowerTermsPolynomial p).eval sample
  let margin := largeSquareDominanceMargin p
  have marginPositive : 0 < margin :=
    largeSquareDominanceMargin_pos degreePositive
  have gap : margin ≤ normSq leading - normSq lower := by
    simpa only [leading, lower, margin] using
      largeSquare_radial_dominance_margin degreePositive normLower normUpper
  have leadingPositive : 0 < normSq leading := by
    have gapLeLeading : margin ≤ normSq leading :=
      gap.trans (sub_le_self _ (normSq_nonneg lower))
    exact marginPositive.trans_le gapLeLeading
  have leadingUpper : normSq leading ≤ annularLeadingUpper p := by
    simpa only [leading] using
      leadingNormSq_le_annularUpper degreePositive normUpper
  have denominatorOrder : 4 * normSq leading ≤
      4 * annularLeadingUpper p :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      leadingUpper (by decide)
  have quotientOrder : margin ^ 2 / (4 * annularLeadingUpper p) ≤
      margin ^ 2 / (4 * normSq leading) :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (RFAP.ConstructiveFraction.pow_nonneg_direct marginPositive.le 2)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) leadingPositive)
      denominatorOrder
  have sumLower := normSq_add_lower_of_gap marginPositive gap
  calc
    margin ^ 2 / (4 * annularLeadingUpper p) ≤
        margin ^ 2 / (4 * normSq leading) := quotientOrder
    _ ≤ normSq (leading + lower) := sumLower
    _ = normSq (p.eval sample) := by
      rw [leadingMonomial_add_lowerTerms_eval degreePositive]

theorem outside_residual_lower_far
    {p : GaussianPolynomial} (degreeAtLeastTwo : 2 ≤ p.natDegree)
    {sample : Gaussian}
    (normLower : 2 * denseLargeSquareRadius p ^ 2 ≤ normSq sample) :
    largeSquareDominanceMargin p ≤ normSq (p.eval sample) := by
  let radiusSq := denseLargeSquareRadius p ^ 2
  let sampleSq := normSq sample
  let leadingNorm := normSq p.leadingCoeff
  let weight := denseLowerCoefficientWeight p
  let exponent := p.natDegree - 1
  let half : Coordinate := (2 : Coordinate)⁻¹
  let leading := (leadingMonomial p).eval sample
  let lower := (lowerTermsPolynomial p).eval sample
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    exact RFAP.ConstructiveFraction.pow_pos_direct
      (denseLargeSquareRadius_pos p) 2
  have oneLeRadiusSq : (1 : Coordinate) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (one_le_denseLargeSquareRadius p) (one_le_denseLargeSquareRadius p)
      (by decide) (denseLargeSquareRadius_pos p).le
  have radiusLeTwice : radiusSq ≤ 2 * radiusSq := by
    calc
      radiusSq = 1 * radiusSq := by ring1
      _ ≤ 2 * radiusSq :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) radiusSqPositive.le
  have radiusSqLeSample : radiusSq ≤ sampleSq := by
    exact radiusLeTwice.trans (by
      simpa only [radiusSq, sampleSq] using normLower)
  have oneLeSample : (1 : Coordinate) ≤ sampleSq :=
    oneLeRadiusSq.trans radiusSqLeSample
  have sampleNonnegative : 0 ≤ sampleSq := oneLeSample.trans' (by decide)
  have sampleUpper : sampleSq ≤ 2 * sampleSq := by
    simpa only [RFAP.ConstructiveFraction.one_mul] using
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 : Coordinate) ≤ 2 by decide) sampleNonnegative)
  have lowerBound : normSq lower ≤ weight * sampleSq ^ exponent := by
    simpa only [lower, weight, sampleSq, exponent] using
      normSq_lowerTermsPolynomial_eval_le degreePositive sampleUpper oneLeSample
  have halfSample : radiusSq ≤ sampleSq / 2 := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    simpa only [radiusSq, sampleSq,
      RFAP.ConstructiveFraction.mul_comm] using normLower
  have coefficientOrder : leadingNorm * radiusSq - weight ≤
      leadingNorm * (sampleSq / 2) - weight := by
    exact RFAP.ConstructiveFraction.sub_le_sub_right_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        halfSample (normSq_nonneg p.leadingCoeff)) weight
  have coefficientPositive : 0 < leadingNorm * radiusSq - weight := by
    dsimp only [leadingNorm, radiusSq, weight]
    exact RFAP.ConstructiveFraction.sub_pos_direct
      (denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive)
  have powerOrder : radiusSq ^ exponent ≤ sampleSq ^ exponent :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusSqPositive.le
      radiusSqLeSample exponent
  have scaledCoefficient :
      (leadingNorm * radiusSq - weight) * radiusSq ^ exponent ≤
        (leadingNorm * (sampleSq / 2) - weight) * sampleSq ^ exponent :=
    RFAP.ConstructiveFraction.mul_le_mul_direct coefficientOrder powerOrder
      (RFAP.ConstructiveFraction.pow_nonneg_direct radiusSqPositive.le
        exponent)
      (coefficientPositive.trans_le coefficientOrder).le
  have degreeIdentity : exponent + 1 = p.natDegree := by
    dsimp only [exponent]
    exact Nat.sub_add_cancel degreePositive
  have leadingIdentity : normSq leading =
      leadingNorm * sampleSq ^ p.natDegree := by
    dsimp only [leading, leadingNorm, sampleSq]
    rw [leadingMonomial_eval degreePositive, normSq_mul, normSq_pow]
  have marginToHalfDifference : largeSquareDominanceMargin p ≤
      normSq leading / 2 - normSq lower := by
    calc
      largeSquareDominanceMargin p =
          (leadingNorm * radiusSq - weight) * radiusSq ^ exponent := by
        rfl
      _ ≤ (leadingNorm * (sampleSq / 2) - weight) *
          sampleSq ^ exponent := scaledCoefficient
      _ = (leadingNorm * sampleSq ^ p.natDegree) / 2 -
          weight * sampleSq ^ exponent := by
        rw [← degreeIdentity, pow_succ]
        change (leadingNorm * (sampleSq * half) - weight) *
            sampleSq ^ exponent =
          (leadingNorm * (sampleSq ^ exponent * sampleSq)) * half -
            weight * sampleSq ^ exponent
        exact weighted_scale_identity leadingNorm sampleSq weight half exponent
      _ = normSq leading / 2 - weight * sampleSq ^ exponent := by
        rw [leadingIdentity]
      _ ≤ normSq leading / 2 - normSq lower :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct lowerBound _
  have sumLower := half_normSq_sub_le_normSq_sub leading (-lower)
  have normalizedSum : leading - -lower = p.eval sample := by
    calc
      leading - -lower = leading + lower := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im, add_re, add_im] <;>
          ring1
      _ = p.eval sample := leadingMonomial_add_lowerTerms_eval
        degreePositive sample
  calc
    largeSquareDominanceMargin p ≤
        normSq leading / 2 - normSq lower := marginToHalfDifference
    _ = normSq leading / 2 - normSq (-lower) := by rw [normSq_neg]
    _ ≤ normSq (leading - -lower) := sumLower
    _ = normSq (p.eval sample) := by rw [normalizedSum]

/-- A displayed sample outside the large square has residual at least the
explicit coefficient-computed exclusion threshold. -/
theorem outsideResidualThreshold_le
    {p : GaussianPolynomial} (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (sample : Gaussian) (outside : ¬(largeSquareBox p).Contains sample) :
    outsideResidualThreshold p ≤ normSq (p.eval sample) := by
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have normLower :=
    (radiusSq_lt_normSq_of_not_largeSquare_contains p sample outside).le
  by_cases annular : normSq sample ≤
      2 * denseLargeSquareRadius p ^ 2
  · exact (min_le_right _ _).trans
      (outside_residual_lower_annulus degreePositive normLower annular)
  · have far : 2 * denseLargeSquareRadius p ^ 2 ≤ normSq sample :=
      (lt_of_not_ge annular).le
    exact (min_le_left _ _).trans
      (outside_residual_lower_far degreeAtLeastTwo far)

/-! ## Protected large-square localization and finite ownership -/

/-- The coefficient-computed isolation square viewed through precisely the
parent data used by residual Newton localization. -/
def largeSquareProtectedAmbient
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    ProtectedAmbient p (largeSquareBox p) where
  box := largeSquareBox p
  refinesAmbient := RFAP.Boxes.Box.refines_refl _
  proper := largeSquareBox_proper p
  clearance := largeSquare_boundaryClearance degreePositive

/-- Uniform positive target for a displayed sample contained in the global
isolation square. -/
def insideResidualTarget
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (epsilon : Coordinate) : Coordinate :=
  RFAP.ResidualWinding.uniformAnchoredResidualTarget input.squarefree
    (largeSquareProtectedAmbient input.degreePositive) epsilon

theorem insideResidualTarget_pos
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    0 < insideResidualTarget input epsilon := by
  exact RFAP.ResidualWinding.uniformAnchoredResidualTarget_pos
    input.squarefree (largeSquareProtectedAmbient input.degreePositive)
      epsilonPositive

/-- The total global threshold uses the local protected-square budget inside
and the leading-term exclusion budget outside. -/
def residualThreshold
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  if (largeSquareBox p).Contains sample then
    insideResidualTarget input epsilon
  else
    outsideResidualThreshold p

theorem residualThreshold_pos
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    0 < residualThreshold input sample epsilon := by
  by_cases inside : (largeSquareBox p).Contains sample
  · rw [residualThreshold, if_pos inside]
    exact insideResidualTarget_pos input epsilonPositive
  · rw [residualThreshold, if_neg inside]
    exact outsideResidualThreshold_pos input.degreePositive

/-- A globally constructed winding-one box, its total shrinking track, and
its deterministic owner in the already computed degree-sized isolation. -/
structure AssignedResult
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) (epsilon : Coordinate) where
  radius : Coordinate
  radiusPositive : 0 < radius
  radiusLeRequested : radius ≤ epsilon
  state : WindingOneState p (largeSquareBox p)
  stateStrictLargeSquare :
    state.box.StrictInterior (largeSquareBox p)
  windingFour : RFAP.Winding.quadrupledBoxWinding p state.box = 4
  diagonalBound : state.box.diagonalSq ≤ 32 * epsilon ^ 2
  track : WindingOneTrack p (largeSquareBox p)
  trackInitial : track.initial = state
  owner : RFAP.Maximality.OwnerSelection input.isolation track
  bandNearSample : ∀ z, state.box.Contains z →
    normSq (z - sample) ≤ 18 * radius ^ 2
  chordalBound : ∀ z, state.box.Contains z →
    RFAP.Chordal.affineChordalSq sample z ≤ 18 * epsilon ^ 2

/-- Construct and assign the local winding-one box for a contained sample
whose residual meets the uniform protected-square target. -/
def assignInside
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) (inside : (largeSquareBox p).Contains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      insideResidualTarget input epsilon) :
    AssignedResult input sample epsilon := by
  let parent := largeSquareProtectedAmbient input.degreePositive
  have localized :=
    RFAP.ResidualWinding.uniform_residual_strict_and_anchored
      input.squarefree parent sample inside epsilonPositive residualSmall
  let seed := RFAP.ResidualWinding.seedOfResidual input.squarefree
    input.elimination parent sample localized.1 epsilonPositive localized.2
  let state := seed.state input.degreeAtLeastTwo
  let track := seed.track input.degreeAtLeastTwo
  have radiusLe :=
    RFAP.ResidualWinding.seedOfResidual_radius_le_cap input.squarefree
      input.elimination parent sample localized.1 epsilonPositive
        localized.2
  have radiusSquareLe : seed.radius ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct seed.radiusPositive.le
      radiusLe 2
  have diagonal : state.box.diagonalSq ≤ 32 * epsilon ^ 2 := by
    have bandDiagonal := seed.band.diagonalSq_le seed.radiusPositive
    have scaled : 32 * seed.radius ^ 2 ≤ 32 * epsilon ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusSquareLe
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 32) (by decide)).le
    simpa only [state, RFAP.ResidualWinding.Seed.state,
      RFAP.ResidualWinding.Seed.band] using bandDiagonal.trans scaled
  have supported : track.initial.box.Refines input.isolation.support := by
    change state.box.Refines (largeSquareBox p)
    exact state.refinesAmbient
  let owner := (RFAP.BoxFTA.prove input).ownership track supported
  exact
    { radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := radiusLe
      state := state
      stateStrictLargeSquare := by
        simpa only [state, parent, largeSquareProtectedAmbient] using
          seed.state_strict_current input.degreeAtLeastTwo
      windingFour := state.rawWindingFour
      diagonalBound := diagonal
      track := track
      trackInitial := rfl
      owner := owner
      bandNearSample := by
        intro z zInside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall zInside
        simpa only [seed, state, parent,
          RFAP.ResidualWinding.Seed.state,
          RFAP.ResidualWinding.Seed.band,
          RFAP.ResidualWinding.seedOfResidual,
          RFAP.ResidualWinding.AnchoredInput.seed,
          RFAP.ResidualWinding.anchoredInputOfResidual,
          RFAP.ResidualWinding.anchoredSquare_anchor] using distance
      chordalBound := by
        intro z zInside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall zInside
        have distanceFromSample : normSq (sample - z) ≤
            18 * seed.radius ^ 2 := by
          have swapped : sample - z = -(z - sample) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
          rw [swapped, normSq_neg]
          simpa only [seed, state, parent,
            RFAP.ResidualWinding.Seed.state,
            RFAP.ResidualWinding.Seed.band,
            RFAP.ResidualWinding.seedOfResidual,
            RFAP.ResidualWinding.AnchoredInput.seed,
            RFAP.ResidualWinding.anchoredInputOfResidual,
            RFAP.ResidualWinding.anchoredSquare_anchor] using distance
        have scaled : 18 * seed.radius ^ 2 ≤ 18 * epsilon ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe (by decide)
        exact (RFAP.Chordal.affineChordalSq_le_normSq sample z).trans
          (distanceFromSample.trans scaled) }

/-- When the requested cap is below the global point-independent reference
radius, global residual assignment uses exactly that radius.  The selected
band geometry is therefore known before the sufficiently accurate sample is
read from its finite approximation. -/
theorem assignInside_radius_eq_of_le_uniformReference
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) (inside : (largeSquareBox p).Contains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall : normSq (p.eval sample) <
      insideResidualTarget input epsilon)
    (epsilonLeReference :
      epsilon ≤ RFAP.ResidualWinding.uniformAnchoredRadius input.squarefree
        (largeSquareProtectedAmbient input.degreePositive) 1) :
    (assignInside input sample inside epsilonPositive residualSmall).radius =
      epsilon := by
  let parent := largeSquareProtectedAmbient input.degreePositive
  have residualQuarter :
      normSq (p.eval sample) < parent.clearance.bound / 4 := by
    exact residualSmall.trans_le (min_le_left _ _)
  change RFAP.ResidualWinding.anchoredRadius input.squarefree parent sample
      epsilon = epsilon
  exact RFAP.ResidualWinding.anchoredRadius_eq_cap_of_le_uniformReference
    input.squarefree parent sample inside epsilonLeReference residualQuarter

/-- Total result of inspecting an arbitrary displayed Gaussian-rational
sample.  The failure constructor records the explicit rational inequality
that prevented localization. -/
inductive Observation
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) (epsilon : Coordinate) : Type where
  | exact (evaluation : p.eval sample = 0)
  | assigned (result : AssignedResult input sample epsilon)
  | residualNotSmall
      (failure : residualThreshold input sample epsilon ≤
        normSq (p.eval sample))

/-- Classify any displayed Gaussian-rational sample by finite evaluation,
protected Newton localization plus output ownership, or a witnessed failure
of the explicit positive small-residual hypothesis. -/
def classify
    {p : GaussianPolynomial} (input : RFAP.BoxFTA.Input p)
    (sample : Gaussian) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) : Observation input sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else if inside : (largeSquareBox p).Contains sample then
    if residualSmall : normSq (p.eval sample) <
        residualThreshold input sample epsilon then
      .assigned (assignInside input sample inside epsilonPositive (by
        rw [residualThreshold, if_pos inside] at residualSmall
        exact residualSmall))
    else
      .residualNotSmall (le_of_not_gt residualSmall)
  else
    .residualNotSmall (by
      rw [residualThreshold, if_neg inside]
      exact outsideResidualThreshold_le input.degreeAtLeastTwo sample inside)

end RFAP.GlobalResidual
