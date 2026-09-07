import FTA.SturmTransducer

/-!
# Finite no-pole Cauchy-index cancellation

This module proves the constructive no-pole case used by the half-plane
winding argument.  A whole-interval strict-sign certificate for the original
denominator supplies an explicit lower bound.  The exact gcd factorization
and a coefficient upper bound transfer that lower bound to the reduced
denominator.  A fixed finite midpoint subdivision then resolves the first
member of every reduced signed-remainder chain, so every leaf has zero Cauchy
index and additivity cancels the finite partition.
-/

namespace FTA.CauchyNoPole

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.RationalPolynomialBounds
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

/-- Proof-bearing positive lower bound for the absolute value of a rational
polynomial throughout a closed rational interval. -/
structure IntervalAbsLowerCertificate
    (p : RatPolynomial) (root : RationalInterval) where
  bound : ℚ
  positive : 0 < bound
  lower : ∀ t : ℚ, root.lower ≤ t → t ≤ root.upper → bound ≤ |p.eval t|

/-- A whole-cell strict-sign certificate supplies its explicit absolute
margin as an interval lower-bound certificate. -/
def IntervalAbsLowerCertificate.ofIntervalSign
    {p : RatPolynomial} {root : RationalInterval}
    (sign : IntervalSignCertificate p root.lower root.upper) :
    IntervalAbsLowerCertificate p root where
  bound := sign.absMargin
  positive := sign.absMargin_pos
  lower := by
    intro t hLower hUpper
    exact sign.absMargin_le_abs_eval hLower hUpper

/-- A coefficient upper bound for the common gcd on the ambient interval. -/
def gcdAbsMajorant (R S : RatPolynomial) (root : RationalInterval) : ℚ :=
  max 1 (denseEvalAbsBound (FTA.DenseGCD.symmetricGCD R S)
    (intervalMagnitude root.lower root.upper))

theorem gcdAbsMajorant_pos (R S : RatPolynomial) (root : RationalInterval) :
    0 < gcdAbsMajorant R S root :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- A coefficient upper bound for the reduced denominator's slope on every
nested cell. -/
def reducedDenominatorSlopeMajorant
    (R S : RatPolynomial) (root : RationalInterval) : ℚ :=
  max 1 (denseEvalLipschitzBound (reducedDenominator R S)
    (intervalMagnitude root.lower root.upper))

theorem reducedDenominatorSlopeMajorant_pos
    (R S : RatPolynomial) (root : RationalInterval) :
    0 < reducedDenominatorSlopeMajorant R S root :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Width below which an original-denominator absolute lower bound forces the
gcd-reduced denominator to pass the executable
midpoint sign test. -/
def reducedDenominatorAbsLowerWidthResolution
    (R S : RatPolynomial) {root : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root) : ℚ :=
  2 * lower.bound /
    (gcdAbsMajorant R S root *
      reducedDenominatorSlopeMajorant R S root)

theorem reducedDenominatorAbsLowerWidthResolution_pos
    (R S : RatPolynomial) {root : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root) :
    0 < reducedDenominatorAbsLowerWidthResolution R S lower := by
  exact div_pos (mul_pos (by norm_num) lower.positive)
    (mul_pos (gcdAbsMajorant_pos R S root)
      (reducedDenominatorSlopeMajorant_pos R S root))

/-- The quantitative original-denominator sign margin survives executable
gcd reduction.  This is the key common-factor step in the no-pole proof. -/
theorem reducedDenominator_midpointResolved_of_refined_width
    (R S : RatPolynomial) {root interval : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      reducedDenominatorAbsLowerWidthResolution R S lower) :
    MidpointResolved interval (reducedDenominator R S) := by
  let rootB := intervalMagnitude root.lower root.upper
  let subB := intervalMagnitude interval.lower interval.upper
  let sample := midpoint interval.lower interval.upper
  let common := FTA.DenseGCD.symmetricGCD R S
  let denominator := reducedDenominator R S
  let commonMajorant := gcdAbsMajorant R S root
  let slopeMajorant := reducedDenominatorSlopeMajorant R S root
  have hsubNonneg : 0 ≤ subB := (intervalMagnitude_pos _ _).le
  have hmagnitude : subB ≤ rootB :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hrootNonneg : 0 ≤ rootB := hsubNonneg.trans hmagnitude
  have hsampleSub : |sample| ≤ subB :=
    abs_le_intervalMagnitude (lower_lt_midpoint proper).le
      (midpoint_lt_upper proper).le
  have hsampleRootLower : root.lower ≤ sample :=
    hrefines.1.trans (lower_lt_midpoint proper).le
  have hsampleRootUpper : sample ≤ root.upper :=
    (midpoint_lt_upper proper).le.trans hrefines.2
  have hcommonBound : |common.eval sample| ≤ commonMajorant := by
    calc
      |common.eval sample| ≤ denseEvalAbsBound common subB :=
        abs_dense_eval_le_denseEvalAbsBound common hsubNonneg hsampleSub
      _ ≤ denseEvalAbsBound common rootB :=
        (denseHornerBounds_mono common hsubNonneg hmagnitude).1
      _ ≤ commonMajorant := le_max_right _ _
  have hcommonMajorant : 0 < commonMajorant := by
    simpa only [commonMajorant] using gcdAbsMajorant_pos R S root
  have hslopeBound :
      denseEvalLipschitzBound denominator subB ≤ slopeMajorant := by
    exact ((denseHornerBounds_mono denominator hsubNonneg hmagnitude).2).trans
      (le_max_right _ _)
  have hslopeNonneg : 0 ≤ denseEvalLipschitzBound denominator subB :=
    (denseHornerBounds_nonneg denominator hsubNonneg).2
  have hslopeMajorant : 0 < slopeMajorant := by
    simpa only [slopeMajorant] using
      reducedDenominatorSlopeMajorant_pos R S root
  have hmarginToProduct :
      lower.bound ≤ commonMajorant * |denominator.eval sample| := by
    calc
      lower.bound ≤ |S.eval sample| :=
        lower.lower sample hsampleRootLower hsampleRootUpper
      _ = |common.eval sample| * |denominator.eval sample| := by
        rw [FTA.DenseGCD.symmetricRightFactor_eval_identity R S sample,
          abs_mul]
        rfl
      _ ≤ commonMajorant * |denominator.eval sample| :=
        mul_le_mul_of_nonneg_right hcommonBound (abs_nonneg _)
  have hdenominatorLower :
      lower.bound / commonMajorant ≤ |denominator.eval sample| := by
    rw [div_le_iff₀ hcommonMajorant]
    simpa [mul_comm] using hmarginToProduct
  have hradius : intervalRadius interval.lower interval.upper sample =
      interval.width / 2 := by
    simpa only [sample] using interval.midpointRadius_eq_half_width proper
  have hradiusNonneg :
      0 ≤ intervalRadius interval.lower interval.upper sample := by
    rw [hradius]
    exact div_nonneg (RationalInterval.width_pos proper).le (by norm_num)
  have hradiusSmall :
      intervalRadius interval.lower interval.upper sample <
        lower.bound / (commonMajorant * slopeMajorant) := by
    rw [hradius]
    dsimp only [reducedDenominatorAbsLowerWidthResolution] at hwidth
    have hhalf := mul_lt_mul_of_pos_right hwidth (show (0 : ℚ) < 1 / 2 by
      norm_num)
    calc
      interval.width / 2 = interval.width * (1 / 2 : ℚ) := by ring
      _ < (2 * lower.bound /
          (gcdAbsMajorant R S root *
            reducedDenominatorSlopeMajorant R S root)) * (1 / 2 : ℚ) := hhalf
      _ = lower.bound /
          (commonMajorant * slopeMajorant) := by
            dsimp only [commonMajorant, slopeMajorant]
            ring
  have hslopeTimesRadius :
      denseEvalLipschitzBound denominator subB *
        intervalRadius interval.lower interval.upper sample <
        lower.bound / commonMajorant := by
    calc
      denseEvalLipschitzBound denominator subB *
          intervalRadius interval.lower interval.upper sample ≤
          slopeMajorant *
            intervalRadius interval.lower interval.upper sample :=
        mul_le_mul_of_nonneg_right hslopeBound hradiusNonneg
      _ < slopeMajorant *
          (lower.bound / (commonMajorant * slopeMajorant)) :=
        mul_lt_mul_of_pos_left hradiusSmall hslopeMajorant
      _ = lower.bound / commonMajorant := by
        field_simp [hcommonMajorant.ne', hslopeMajorant.ne']
  change denseEvalLipschitzBound denominator subB *
      intervalRadius interval.lower interval.upper sample <
        |denominator.eval sample|
  exact hslopeTimesRadius.trans_le hdenominatorLower

/-- One positive width simultaneously resolves the complete reduced Cauchy
chain and its first (denominator) member. -/
def noPoleWidthResolution
    (R S : RatPolynomial) (hR : R.isZero = false)
    (hS : S.isZero = false) {root : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root) : ℚ :=
  min (cauchyChainAmbientWidthResolution R S hR hS root)
    (reducedDenominatorAbsLowerWidthResolution R S lower)

theorem noPoleWidthResolution_pos
    (R S : RatPolynomial) (hR : R.isZero = false)
    (hS : S.isZero = false) {root : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root) :
    0 < noPoleWidthResolution R S hR hS lower := by
  exact lt_min (cauchyChainAmbientWidthResolution_pos R S hR hS root)
    (reducedDenominatorAbsLowerWidthResolution_pos R S lower)

/-- Every sufficiently narrow nested cell has zero Cauchy index. -/
theorem cauchyIndex2_eq_zero_of_refined_width
    (R S : RatPolynomial) (hR : R.isZero = false)
    (hS : S.isZero = false) {root interval : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < noPoleWidthResolution R S hR hS lower) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  have hchainWidth : interval.width <
      cauchyChainAmbientWidthResolution R S hR hS root :=
    hwidth.trans_le (min_le_left _ _)
  have hdenominatorWidth : interval.width <
      reducedDenominatorAbsLowerWidthResolution R S lower :=
    hwidth.trans_le (min_le_right _ _)
  have headResolved :=
    reducedDenominator_midpointResolved_of_refined_width
      R S lower hrefines proper hdenominatorWidth
  let result := neutralCauchyChainCertificates?_succeeds_of_refined_width
    R S hR hS root interval hrefines proper hchainWidth headResolved
  exact result.1.cauchyIndex2_eq_zero

/-- Fixed-depth midpoint subdivision.  The displayed geometric inequality is
finite natural-number evidence that every leaf is below the no-pole width. -/
theorem cauchyIndex2_eq_zero_of_absLower_at_depth
    (R S : RatPolynomial) (hR : R.isZero = false)
    (hS : S.isZero = false) {root interval : RationalInterval}
    (lower : IntervalAbsLowerCertificate S root)
    (fuel : ℕ) (hrefines : interval.Refines root)
    (proper : interval.Proper)
    (hsufficient : (2 / 3 : ℚ) ^ fuel * interval.width <
      noPoleWidthResolution R S hR hS lower) :
    cauchyIndex2 R S interval.lower interval.upper = 0 := by
  induction fuel generalizing interval with
  | zero =>
      apply cauchyIndex2_eq_zero_of_refined_width
        R S hR hS lower hrefines proper
      simpa using hsufficient
  | succ fuel ih =>
      let cut := midpoint interval.lower interval.upper
      let left := interval.left cut
      let right := interval.right cut
      have hleftProper : left.Proper := by
        change interval.lower < cut
        exact lower_lt_midpoint proper
      have hrightProper : right.Proper := by
        change cut < interval.upper
        exact midpoint_lt_upper proper
      have hleftRefines : left.Refines root :=
        RationalInterval.refines_trans
          (by
            constructor
            · exact le_rfl
            · exact (midpoint_lt_upper proper).le)
          hrefines
      have hrightRefines : right.Refines root :=
        RationalInterval.refines_trans
          (by
            constructor
            · exact (lower_lt_midpoint proper).le
            · exact le_rfl)
          hrefines
      have hleftWidth : left.width = interval.width / 2 := by
        change cut - interval.lower =
          (interval.upper - interval.lower) / 2
        dsimp only [cut, FTA.RationalPolynomialBounds.midpoint]
        ring
      have hrightWidth : right.width = interval.width / 2 := by
        change interval.upper - cut =
          (interval.upper - interval.lower) / 2
        dsimp only [cut, FTA.RationalPolynomialBounds.midpoint]
        ring
      have hpowPos : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have hleftSufficient : (2 / 3 : ℚ) ^ fuel * left.width <
          noPoleWidthResolution R S hR hS lower := by
        calc
          (2 / 3 : ℚ) ^ fuel * left.width =
              (2 / 3 : ℚ) ^ fuel * (interval.width / 2) := by
                rw [hleftWidth]
          _ < (2 / 3 : ℚ) ^ fuel *
              ((2 / 3 : ℚ) * interval.width) := by
                apply mul_lt_mul_of_pos_left _ hpowPos
                have hwidthPos := RationalInterval.width_pos proper
                nlinarith
          _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
                rw [pow_succ]
                ring
          _ < noPoleWidthResolution R S hR hS lower := by
                simpa [Nat.succ_eq_add_one] using hsufficient
      have hrightSufficient : (2 / 3 : ℚ) ^ fuel * right.width <
          noPoleWidthResolution R S hR hS lower := by
        rw [hrightWidth]
        rw [hleftWidth] at hleftSufficient
        exact hleftSufficient
      have hleftIndex := ih hleftRefines hleftProper hleftSufficient
      have hrightIndex := ih hrightRefines hrightProper hrightSufficient
      have hadd := cauchyIndex2_add R S interval.lower cut interval.upper
      change cauchyIndex2 R S interval.lower interval.upper = 0
      have hleftIndex' : cauchyIndex2 R S interval.lower cut = 0 := by
        simpa only [left, RationalInterval.left] using hleftIndex
      have hrightIndex' : cauchyIndex2 R S cut interval.upper = 0 := by
        simpa only [right, RationalInterval.right] using hrightIndex
      omega

/-- Constructive no-pole theorem: a proof-bearing positive absolute lower
bound for the denominator makes the doubled Cauchy index vanish on the whole
interval.  The subdivision depth is computed by rational ceiling arithmetic. -/
theorem cauchyIndex2_eq_zero_of_intervalAbsLower
    (R S : RatPolynomial) {root : RationalInterval}
    (proper : root.Proper)
    (lower : IntervalAbsLowerCertificate S root) :
    cauchyIndex2 R S root.lower root.upper = 0 := by
  by_cases hR : R.isZero = false
  · by_cases hS : S.isZero = false
    · let resolution := noPoleWidthResolution R S hR hS lower
      let depth := geometricDepth root.width (resolution / 2)
      have hresolution : 0 < resolution := by
        simpa only [resolution] using noPoleWidthResolution_pos R S hR hS lower
      have hgeometric := geometricDepth_sufficient
        (RationalInterval.width_pos proper).le
        (show 0 < resolution / 2 by linarith)
      have hsufficient : (2 / 3 : ℚ) ^ depth * root.width < resolution := by
        calc
          (2 / 3 : ℚ) ^ depth * root.width ≤ resolution / 2 := by
            simpa only [depth] using hgeometric
          _ < resolution := by linarith
      exact cauchyIndex2_eq_zero_of_absLower_at_depth R S hR hS lower depth
        (RationalInterval.refines_refl root) proper hsufficient
    · have hSzero : S.isZero = true := by simpa using hS
      simp [cauchyIndex2, hSzero]
  · have hRzero : R.isZero = true := by simpa using hR
    simp [cauchyIndex2, hRzero]

/-- Strict-sign specialization of the general absolute-lower-bound no-pole
theorem. -/
theorem cauchyIndex2_eq_zero_of_intervalSign
    (R S : RatPolynomial) {root : RationalInterval}
    (proper : root.Proper)
    (sign : IntervalSignCertificate S root.lower root.upper) :
    cauchyIndex2 R S root.lower root.upper = 0 :=
  cauchyIndex2_eq_zero_of_intervalAbsLower R S proper
    (IntervalAbsLowerCertificate.ofIntervalSign sign)

end FTA.CauchyNoPole
