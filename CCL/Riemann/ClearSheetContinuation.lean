import CCL.Riemann.BranchCuts
import CCL.Riemann.SquareRootContinuationChain

/-!
# Quantitative square-root continuation on a clear segment

The dense Horner bound controls the change of `f(x)` between two rational
samples of a certified clear segment.  If that computed change fits inside
the current owner's Rouché clearance, this file advances the owner without a
fresh sheet choice.  It is the local step used by a finite adaptive
subdivision.
-/

namespace CCL.Riemann.ClearSheetContinuation

open CCL.Riemann.BranchCuts

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev PackedOwner :=
  CCL.Riemann.SquareRootContinuationChain.PackedOwner
abbrev Chain := CCL.Riemann.SquareRootContinuationChain.Chain

/-- The exact closed real unit interval, viewed as a (possibly degenerate)
Gaussian-rational box.  Polynomial bounds need only containment, not a
positive box area. -/
def parameterAmbient : Box where
  xLower := 0
  xUpper := 1
  yLower := 0
  yUpper := 0
  x_valid := by decide
  y_valid := by decide

/-- The base polynomial after exact affine substitution along one displayed
segment.  Bounding this polynomial in its unit parameter is substantially
sharper than bounding the original polynomial on the segment's often much
larger clearance ambient. -/
def segmentPolynomial {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish) :
    GaussianPolynomial :=
  RFAP.PathPolynomial.composeLine polynomial start (finish - start)

theorem parameterAmbient_contains (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    parameterAmbient.Contains (RFAP.PathPolynomial.ofCoordinate parameter) :=
  ⟨inside.1, inside.2, le_rfl, le_rfl⟩

theorem segmentPolynomial_eval
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    (segmentPolynomial segment).eval
        (RFAP.PathPolynomial.ofCoordinate parameter) =
      polynomial.eval (segment.pointAt parameter) := by
  rw [segmentPolynomial, RFAP.PathPolynomial.eval_composeLine]
  congr 1
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.PathPolynomial.line, ClearSegment.pointAt,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im,
      CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- Squared-variation majorant between two affine parameters.  The affine
substitution absorbs the geometric segment displacement before the finite
Horner scan, avoiding dependence on an unrelated large ambient box. -/
@[irreducible] def variationBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) : Coordinate :=
  RFAP.PolynomialBounds.denseLipschitzBound
      (segmentPolynomial segment) parameterAmbient *
    (left - right) ^ 2

/-- Exact rational specification of the cached dense-Horner variation.  This
accessor lets explicit finite certificates evaluate the polynomial scan once
and then reason about the much smaller endpoint factor. -/
theorem variationBound_eq_denseLipschitz
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment left right =
      RFAP.PolynomialBounds.denseLipschitzBound
          (segmentPolynomial segment) parameterAmbient *
        (left - right) ^ 2 := by
  unfold variationBound
  rfl

theorem variationBound_nonneg {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    0 <= variationBound segment left right := by
  unfold variationBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.PolynomialBounds.denseLipschitzBound_pos
      (segmentPolynomial segment) parameterAmbient).le
    (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))

/-- Uniform residual threshold for the degree-two root polynomial along one
clear base segment. -/
def squareRootDerivativeThreshold {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  segment.clearanceBound / 4

/-- Uniform positive derivative margin obtained from a finite dyadic
under-approximation to the square root of the base threshold.  For the
quadratic derivative `2Z`, this retains the squared lower bound instead of
collapsing it through `min 1`. -/
def squareRootDerivativeMargin {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  4 * CCL.FiniteGeometric.dyadicSquareRadius
    (squareRootDerivativeThreshold segment)

theorem squareRootDerivativeThreshold_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < squareRootDerivativeThreshold segment :=
  RFAP.ConstructiveFraction.div_pos_direct segment.clearanceBound_positive
    (by decide)

theorem squareRootDerivativeMargin_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < squareRootDerivativeMargin segment :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (CCL.FiniteGeometric.dyadicSquareRadius_positive _)

/-- The clear base-line certificate gives one derivative-separation
certificate for every degree-two root polynomial `Z² - f(x)` along the
segment.  Its threshold and margin are independent of the parameter and of
the displayed root-isolation box. -/
def squareRootDerivativeSeparation
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    RFAP.DerivativeSeparation.Certificate
      (CCL.PowerMonodromy.polynomial
        (polynomial.eval (segment.pointAt parameter))
        CCL.Riemann.SquareRootSheets.degreeTwo) rootAmbient where
  threshold := squareRootDerivativeThreshold segment
  threshold_pos := squareRootDerivativeThreshold_positive segment
  margin := squareRootDerivativeMargin segment
  margin_pos := squareRootDerivativeMargin_positive segment
  lower := by
    intro root _rootInside residualSmall
    let base := polynomial.eval (segment.pointAt parameter)
    let rootPolynomial := CCL.PowerMonodromy.polynomial base
      CCL.Riemann.SquareRootSheets.degreeTwo
    let baseClearance := segment.clearanceBound
    let threshold := squareRootDerivativeThreshold segment
    let rootNorm :=
      RFAP.ConstructiveGaussian.Gaussian.normSq root
    have baseLower : baseClearance ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq base := by
      exact segment.clearanceBound_le_eval_normSq
        (segment.pointAt_onCertifiedLine parameter inside)
    have baseIdentity : base = root ^ 2 - rootPolynomial.eval root := by
      rw [CCL.PowerMonodromy.polynomial_eval]
      change base = root ^ 2 - (root ^ 2 - base)
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1
    have baseUpper :
        RFAP.ConstructiveGaussian.Gaussian.normSq base ≤
          2 * (rootNorm ^ 2 + threshold) := by
      calc
        RFAP.ConstructiveGaussian.Gaussian.normSq base =
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (root ^ 2 - rootPolynomial.eval root) := by rw [baseIdentity]
        _ ≤ 2 *
            (RFAP.ConstructiveGaussian.Gaussian.normSq (root ^ 2) +
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (rootPolynomial.eval root)) :=
          RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
        _ = 2 * (rootNorm ^ 2 +
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (rootPolynomial.eval root)) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
        _ ≤ 2 * (rootNorm ^ 2 + threshold) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (by
              calc
                rootNorm ^ 2 +
                    RFAP.ConstructiveGaussian.Gaussian.normSq
                      (rootPolynomial.eval root) =
                    RFAP.ConstructiveGaussian.Gaussian.normSq
                        (rootPolynomial.eval root) + rootNorm ^ 2 := by ring1
                _ ≤ threshold + rootNorm ^ 2 :=
                  RFAP.ConstructiveFraction.add_le_add_right_direct
                    residualSmall (rootNorm ^ 2)
                _ = rootNorm ^ 2 + threshold := by ring1)
            (by decide)
    have clearanceToSquare : baseClearance / 4 ≤ rootNorm ^ 2 := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos
        (show (0 : Coordinate) < 4 by decide)).2
      have halfAddHalf :
          baseClearance / 2 + baseClearance / 2 = baseClearance := by
        apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
          (show (2 : Coordinate) ≠ 0 by decide)
        calc
          (baseClearance / 2 + baseClearance / 2) * 2 =
              (baseClearance / 2) * 2 +
                (baseClearance / 2) * 2 := by rw [add_mul]
          _ = baseClearance + baseClearance := by
            rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2
                (by decide)]
          _ = baseClearance * 2 := by ring1
      have twiceThreshold : 2 * threshold = baseClearance / 2 := by
        dsimp only [threshold, squareRootDerivativeThreshold,
          baseClearance]
        apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
          (show (2 : Coordinate) ≠ 0 by decide)
        calc
          (2 * (segment.clearanceBound / 4)) * 2 =
              (segment.clearanceBound / 4) * 4 := by ring1
          _ = segment.clearanceBound :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 4 (by decide)
          _ = (segment.clearanceBound / 2) * 2 :=
            (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2
              (by decide)).symm
      have reduced : baseClearance / 2 ≤ 2 * rootNorm ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := baseClearance / 2)
        calc
          baseClearance / 2 + baseClearance / 2 = baseClearance := halfAddHalf
          _ ≤ 2 * (rootNorm ^ 2 + threshold) := baseLower.trans baseUpper
          _ = 2 * rootNorm ^ 2 + baseClearance / 2 := by
            rw [mul_add, twiceThreshold]
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct reduced
          (show (0 : Coordinate) ≤ 2 by decide)
      have scaledClearance :
          baseClearance ≤ (2 * rootNorm ^ 2) * 2 := by
        rwa [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2
          (by decide)] at scaled
      calc
        baseClearance ≤ (2 * rootNorm ^ 2) * 2 := scaledClearance
        _ = rootNorm ^ 2 * 4 := by ring1
    let dyadicRoot := CCL.FiniteGeometric.dyadicSquareRadius threshold
    have dyadicSquareLe : dyadicRoot ^ 2 ≤ rootNorm ^ 2 :=
      (CCL.FiniteGeometric.dyadicSquareRadius_sq_lt
        (squareRootDerivativeThreshold_positive segment)).le.trans
          (by
            simpa only [threshold, squareRootDerivativeThreshold] using
              clearanceToSquare)
    have dyadicLeRoot : dyadicRoot ≤ rootNorm :=
      RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg root)
        dyadicSquareLe
    rw [CCL.PowerMonodromy.derivative_eval,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_pow,
      CCL.Riemann.SquareRootSheets.degreeTwo_value]
    have normSqTwo :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((2 : Nat) : Gaussian) = 4 := by
      simp only [RFAP.ConstructiveGaussian.Gaussian.normSq,
        RFAP.ConstructiveGaussian.Gaussian.natCast_re,
        RFAP.ConstructiveGaussian.Gaussian.natCast_im]
      ring1
    rw [normSqTwo]
    simp only [Nat.reduceSub, pow_one]
    change squareRootDerivativeMargin segment ≤ 4 * rootNorm
    unfold squareRootDerivativeMargin
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      dyadicLeRoot (by decide)

@[simp] theorem squareRootDerivativeSeparation_threshold
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    (squareRootDerivativeSeparation (rootAmbient := rootAmbient)
      segment parameter inside).threshold =
        squareRootDerivativeThreshold segment := rfl

@[simp] theorem squareRootDerivativeSeparation_margin
    {polynomial : GaussianPolynomial} {ambient rootAmbient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1) :
    (squareRootDerivativeSeparation (rootAmbient := rootAmbient)
      segment parameter inside).margin =
        squareRootDerivativeMargin segment := rfl

/-- Rational midpoint used by the executable subdivision checker. -/
def midpoint (left right : Coordinate) : Coordinate := (left + right) / 2

theorem left_le_midpoint {left right : Coordinate} (ordered : left <= right) :
    left <= midpoint left right := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left * 2 = left + left := by ring1
    _ <= left + right := add_le_add (le_refl _) ordered

theorem midpoint_le_right {left right : Coordinate} (ordered : left <= right) :
    midpoint left right <= right := by
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left + right <= right + right := add_le_add ordered (le_refl _)
    _ = right * 2 := by ring1

theorem left_lt_midpoint {left right : Coordinate} (ordered : left < right) :
    left < midpoint left right := by
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left * 2 = left + left := by ring1
    _ < left + right :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct ordered left

theorem midpoint_lt_right {left right : Coordinate} (ordered : left < right) :
    midpoint left right < right := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    left + right < right + right :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct ordered right
    _ = right * 2 := by ring1

theorem midpoint_inside {left right : Coordinate}
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    (0 : Coordinate) <= midpoint left right ∧ midpoint left right <= 1 := by
  constructor
  · exact RFAP.ConstructiveFraction.div_nonneg_direct
      (add_nonneg leftInside.1 rightInside.1) (by decide)
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    calc
      left + right <= 1 + 1 := add_le_add leftInside.2 rightInside.2
      _ = 1 * 2 := by ring1

private theorem left_sub_midpoint (left right : Coordinate) :
    left - midpoint left right = (left - right) / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (left - midpoint left right) * 2 =
        left * 2 - midpoint left right * 2 := by ring1
    _ = left * 2 - (left + right) := by
      rw [midpoint,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = left - right := by ring1
    _ = ((left - right) / 2) * 2 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)).symm

private theorem midpoint_sub_right (left right : Coordinate) :
    midpoint left right - right = (left - right) / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (midpoint left right - right) * 2 =
        midpoint left right * 2 - right * 2 := by ring1
    _ = (left + right) - right * 2 := by
      rw [midpoint,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = left - right := by ring1
    _ = ((left - right) / 2) * 2 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)).symm

theorem variationBound_left_midpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment left (midpoint left right) =
      variationBound segment left right / 4 := by
  unfold variationBound
  rw [left_sub_midpoint, pow_two,
    RFAP.ConstructiveFraction.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((left - right) * (left - right)) 4]
  simp only [pow_two]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      (RFAP.PolynomialBounds.denseLipschitzBound
        (segmentPolynomial segment) parameterAmbient *
          ((left - right) * (left - right))) 4]
  ring1

theorem variationBound_midpoint_right
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    variationBound segment (midpoint left right) right =
      variationBound segment left right / 4 := by
  unfold variationBound
  rw [midpoint_sub_right, pow_two,
    RFAP.ConstructiveFraction.div_mul_div_direct,
    show (2 : Coordinate) * 2 = 4 by decide]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      ((left - right) * (left - right)) 4]
  simp only [pow_two]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct
      (RFAP.PolynomialBounds.denseLipschitzBound
        (segmentPolynomial segment) parameterAmbient *
          ((left - right) * (left - right))) 4]
  ring1

theorem evaluation_variation_le {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (_within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left) -
          polynomial.eval (segment.pointAt right)) <=
      variationBound segment left right := by
  have variation :=
    RFAP.PolynomialBounds.normSq_eval_sub_eval_le_denseLipschitzBound
      (segmentPolynomial segment)
      (parameterAmbient_contains left leftInside)
      (parameterAmbient_contains right rightInside)
  rw [segmentPolynomial_eval, segmentPolynomial_eval] at variation
  unfold variationBound
  change _ <= RFAP.PolynomialBounds.denseLipschitzBound
      (segmentPolynomial segment) parameterAmbient * (left - right) ^ 2
  exact variation.trans_eq (by
    congr 1
    unfold RFAP.ConstructiveGaussian.Gaussian.normSq
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im]
    ring1)

/-- The variation majorant from the left endpoint is monotone on an ordered
rational subinterval. -/
theorem variationBound_le_of_between
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {left parameter right : Coordinate}
    (leftParameter : left <= parameter)
    (parameterRight : parameter <= right) :
    variationBound segment left parameter <=
      variationBound segment left right := by
  have parameterDeltaNonnegative : (0 : Coordinate) <= parameter - left :=
    RFAP.ConstructiveFraction.sub_nonneg_direct leftParameter
  have deltaOrder : parameter - left <= right - left := by
    exact sub_le_sub_right parameterRight left
  have squareOrder : (parameter - left) ^ 2 <= (right - left) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      parameterDeltaNonnegative deltaOrder 2
  have signedSquareOrder : (left - parameter) ^ 2 <=
      (left - right) ^ 2 := by
    calc
      (left - parameter) ^ 2 = (parameter - left) ^ 2 := by ring1
      _ <= (right - left) ^ 2 := squareOrder
      _ = (left - right) ^ 2 := by ring1
  unfold variationBound
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact signedSquareOrder
  · exact
      (RFAP.PolynomialBounds.denseLipschitzBound_pos
        (segmentPolynomial segment) parameterAmbient).le

/-- Advance a stored owner between two rational samples whenever the fully
computed dense-Horner variation fits its current clearance. -/
def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : variationBound segment left right <
      owner.track.initial.clearance.bound) :
    Owner (polynomial.eval (segment.pointAt right)) :=
  owner.advance
    (segment.pointAt_eval_ne_zero right rightInside)
    ((evaluation_variation_le segment within left right leftInside
      rightInside).trans_lt small)

/-- Executable one-step checker.  Failure is finite evidence that this
particular interval must be subdivided further; success returns the continued
owner itself. -/
def tryAdvance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left))) :
    Option (Owner (polynomial.eval (segment.pointAt right))) :=
  if small : variationBound segment left right <
      owner.track.initial.clearance.bound then
    some (advance segment within left right leftInside rightInside owner small)
  else none

theorem tryAdvance_eq_some_of_small
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (small : variationBound segment left right <
      owner.track.initial.clearance.bound) :
    tryAdvance segment within left right leftInside rightInside owner =
      some (advance segment within left right leftInside rightInside owner small) := by
  simp only [tryAdvance, dif_pos small]

theorem tryAdvance_eq_none_of_not_small
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt left)))
    (notSmall : ¬ variationBound segment left right <
      owner.track.initial.clearance.bound) :
    tryAdvance segment within left right leftInside rightInside owner = none := by
  simp only [tryAdvance, dif_neg notSmall]

/-- The corresponding single-entry finite chain, rooted at one canonical
sheet owner over the left sample. -/
def oneStep {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (sheet : Fin 2)
    (small : variationBound segment left right <
      (CCL.Riemann.SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet).track.initial.clearance.bound) :
    CCL.Riemann.SquareRootContinuationChain.SeededChain
      (polynomial.eval (segment.pointAt left))
      (segment.pointAt_eval_ne_zero left leftInside) where
  sheet := sheet
  continuation := by
    let initial :=
      CCL.Riemann.SquareRootContinuationChain.PackedOwner.independent
      (segment.pointAt_eval_ne_zero left leftInside) sheet
    let target := polynomial.eval (segment.pointAt right)
    have targetNonzero := segment.pointAt_eval_ne_zero right rightInside
    have moveSmall :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (initial.parameter - target) <
          initial.owner.track.initial.clearance.bound := by
      exact (evaluation_variation_le segment within left right leftInside
        rightInside).trans_lt small
    exact CCL.Riemann.SquareRootContinuationChain.Chain.single
      initial target targetNonzero moveSmall

@[simp] theorem oneStep_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
    (sheet : Fin 2)
    (small : variationBound segment left right <
      (CCL.Riemann.SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet).track.initial.clearance.bound) :
    (oneStep segment within left right leftInside rightInside sheet small).endpoint.parameter =
      polynomial.eval (segment.pointAt right) := rfl

/-- A finite, explicitly checked adaptive subdivision of one clear segment.
Each tail starts from the owner computed by the preceding Horner/Rouché
step.  No termination principle or completed path is hidden in this data. -/
inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Coordinate) →
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1) →
      Owner (polynomial.eval (segment.pointAt left)) → Type
  | stop (left : Coordinate)
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
      (owner : Owner (polynomial.eval (segment.pointAt left))) :
      Subdivision segment within left leftInside owner
  | next (left : Coordinate)
      (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
      (owner : Owner (polynomial.eval (segment.pointAt left)))
      (right : Coordinate)
      (rightInside : (0 : Coordinate) <= right ∧ right <= 1)
      (small : variationBound segment left right <
        owner.track.initial.clearance.bound)
      (remaining : Subdivision segment within right rightInside
        (advance segment within left right leftInside rightInside owner small)) :
      Subdivision segment within left leftInside owner

namespace Subdivision

structure Endpoint where
  parameter : Coordinate
  inside : (0 : Coordinate) <= parameter ∧ parameter <= 1

def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Endpoint
  | .stop left leftInside _ => ⟨left, leftInside⟩
  | .next _ _ _ _ _ _ remaining => remaining.endpoint

/-- The final owner, indexed by the actual final rational parameter. -/
def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Owner (polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter))
  | .stop _ _ owner => owner
  | .next _ _ _ _ _ _ remaining => remaining.terminalOwner

def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    Subdivision segment within left leftInside owner → Nat
  | .stop _ _ _ => 0
  | .next _ _ _ _ _ _ remaining => remaining.stepCount + 1

/-- Execute a proposed finite mesh from left to right.  Every comparison is
decidable rational arithmetic.  A successful result contains the complete
dependent owner chain; `none` means that at least one displayed mesh edge did
not fit its inherited clearance. -/
def trySamples {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (remaining : List Endpoint) →
      Option (Subdivision segment within current.parameter current.inside owner)
  | [] => some (.stop current.parameter current.inside owner)
  | sample :: rest =>
      if small : variationBound segment current.parameter sample.parameter <
          owner.track.initial.clearance.bound then
        match trySamples segment within sample
            (advance segment within current.parameter sample.parameter
              current.inside sample.inside owner small) rest with
        | none => none
        | some tail => some (.next current.parameter current.inside owner
            sample.parameter sample.inside small tail)
      else none

@[simp] theorem trySamples_nil {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    trySamples segment within current owner [] =
      some (.stop current.parameter current.inside owner) := rfl

/-- A successful finite mesh contains exactly one continuation step per
listed target sample. -/
theorem trySamples_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (remaining : List Endpoint)
    {subdivision : Subdivision segment within current.parameter
      current.inside owner}
    (success : trySamples segment within current owner remaining =
      some subdivision) :
    subdivision.stepCount = remaining.length := by
  induction remaining generalizing current owner subdivision with
  | nil =>
      simp only [trySamples] at success
      cases success
      rfl
  | cons sample rest inductionHypothesis =>
      simp only [trySamples] at success
      split at success
      next small =>
        split at success
        next recursiveFailure => contradiction
        next tail recursiveSuccess =>
          cases success
          simp only [stepCount, List.length_cons]
          exact congrArg Nat.succ
            (inductionHypothesis sample
              (advance segment within current.parameter sample.parameter
                current.inside sample.inside owner small)
              (subdivision := tail) recursiveSuccess)
      next notSmall => contradiction

def finalTarget (current : Endpoint) : List Endpoint -> Endpoint
  | [] => current
  | sample :: remaining => finalTarget sample remaining

theorem finalTarget_append (current : Endpoint)
    (first second : List Endpoint) :
    finalTarget current (first ++ second) =
      finalTarget (finalTarget current first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons sample remaining inductionHypothesis =>
      exact inductionHypothesis sample

theorem trySamples_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (remaining : List Endpoint)
    {subdivision : Subdivision segment within current.parameter
      current.inside owner}
    (success : trySamples segment within current owner remaining =
      some subdivision) :
    subdivision.endpoint.parameter =
      (finalTarget current remaining).parameter := by
  induction remaining generalizing current owner subdivision with
  | nil =>
      simp only [trySamples] at success
      cases success
      rfl
  | cons sample rest inductionHypothesis =>
      simp only [trySamples] at success
      split at success
      next small =>
        split at success
        next recursiveFailure => contradiction
        next tail recursiveSuccess =>
          cases success
          exact inductionHypothesis sample
            (advance segment within current.parameter sample.parameter
              current.inside sample.inside owner small)
            (subdivision := tail) recursiveSuccess
      next notSmall => contradiction

/-- Ordered dyadic target mesh between two certified unit-interval samples.
The left endpoint is omitted because it is the walk's initial state; the
right endpoint is always the final list entry. -/
def dyadicTargets : Nat -> Endpoint -> Endpoint -> List Endpoint
  | 0, _left, right => [right]
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      dyadicTargets depth left middle ++
        dyadicTargets depth middle right

/-- One parameter edge of a dyadic mesh, retaining both endpoints so that a
later mesh can be grouped into exact child blocks of an earlier mesh. -/
structure ParameterEdge where
  left : Endpoint
  right : Endpoint

/-- Retain both endpoints while walking an ordinary target list. -/
def parameterEdgesFrom : Endpoint -> List Endpoint -> List ParameterEdge
  | _current, [] => []
  | current, endpoint :: remaining =>
      { left := current, right := endpoint } ::
        parameterEdgesFrom endpoint remaining

/-- Edge extraction respects concatenation at the exact final endpoint of the
first target block. -/
theorem parameterEdgesFrom_append (current : Endpoint)
    (first second : List Endpoint) :
    parameterEdgesFrom current (first ++ second) =
      parameterEdgesFrom current first ++
        parameterEdgesFrom (finalTarget current first) second := by
  induction first generalizing current with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      simp only [List.cons_append, parameterEdgesFrom, finalTarget]
      exact congrArg (List.cons { left := current, right := endpoint })
        (inductionHypothesis endpoint)

/-- The edge presentation of the same dyadic mesh as `dyadicTargets`. -/
def dyadicEdges : Nat -> Endpoint -> Endpoint -> List ParameterEdge
  | 0, left, right => [{ left := left, right := right }]
  | depth + 1, left, right =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      dyadicEdges depth left middle ++ dyadicEdges depth middle right

/-- Forgetting the retained left endpoints recovers the original target
list definitionally, including its ordering. -/
theorem dyadicEdges_rights (depth : Nat) (left right : Endpoint) :
    (dyadicEdges depth left right).map (fun edge => edge.right) =
      dyadicTargets depth left right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [dyadicEdges, dyadicTargets, List.map_append]
      rw [inductionHypothesis, inductionHypothesis]

/-- Refine every displayed parameter edge by the same additional dyadic
depth, preserving the parent-block ordering. -/
def refineDyadicEdges (additionalDepth : Nat)
    (edges : List ParameterEdge) : List ParameterEdge :=
  edges.flatMap fun edge =>
    dyadicEdges additionalDepth edge.left edge.right

/-- Dyadic depths compose by an exact finite block decomposition.  Thus every
depth-`earlier + additional` edge belongs to one explicitly displayed
depth-`earlier` parent, with no appeal to an infinite limiting mesh. -/
theorem dyadicEdges_add (earlier additional : Nat)
    (left right : Endpoint) :
    dyadicEdges (earlier + additional) left right =
      refineDyadicEdges additional (dyadicEdges earlier left right) := by
  induction earlier generalizing left right with
  | zero =>
      simp only [Nat.zero_add, dyadicEdges, refineDyadicEdges,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | succ earlier inductionHypothesis =>
      simp only [Nat.succ_add, dyadicEdges, refineDyadicEdges,
        List.flatMap_append]
      rw [inductionHypothesis, inductionHypothesis]
      rfl

@[simp] theorem dyadicEdges_length (depth : Nat)
    (left right : Endpoint) :
    (dyadicEdges depth left right).length = 2 ^ depth := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [dyadicEdges, List.length_append,
        inductionHypothesis, pow_succ]
      omega

/-- Select one canonical dyadic edge by descending the balanced subdivision
tree instead of materializing and linearly indexing the complete edge list.
The recursion depth is the dyadic depth, so concrete certificate lookup stays
within ordinary elaboration limits even for a large retained mesh. -/
def dyadicEdgeAt : (depth : Nat) -> Endpoint -> Endpoint ->
    Fin (2 ^ depth) -> ParameterEdge
  | 0, left, right, _index => { left := left, right := right }
  | depth + 1, left, right, index =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      if lower : index.val < 2 ^ depth then
        dyadicEdgeAt depth left middle ⟨index.val, lower⟩
      else
        dyadicEdgeAt depth middle right
          ⟨index.val - 2 ^ depth, by
            have total := index.isLt
            have total' : index.val < 2 ^ depth + 2 ^ depth := by
              simpa [pow_succ, Nat.mul_two] using total
            omega⟩

/-- Every logarithmically selected dyadic edge preserves the order of its
two parent endpoints. -/
theorem dyadicEdgeAt_ordered (depth : Nat) (left right : Endpoint)
    (index : Fin (2 ^ depth)) (ordered : left.parameter <= right.parameter) :
    (dyadicEdgeAt depth left right index).left.parameter <=
      (dyadicEdgeAt depth left right index).right.parameter := by
  induction depth generalizing left right with
  | zero => exact ordered
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · apply inductionHypothesis
        exact left_le_midpoint ordered
      · apply inductionHypothesis
        exact midpoint_le_right ordered

/-- Every logarithmically selected dyadic edge has positive width whenever
its two outer endpoints do. -/
theorem dyadicEdgeAt_strict (depth : Nat) (left right : Endpoint)
    (index : Fin (2 ^ depth)) (ordered : left.parameter < right.parameter) :
    (dyadicEdgeAt depth left right index).left.parameter <
      (dyadicEdgeAt depth left right index).right.parameter := by
  induction depth generalizing left right with
  | zero => exact ordered
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · apply inductionHypothesis
        exact left_lt_midpoint ordered
      · apply inductionHypothesis
        exact midpoint_lt_right ordered

/-- Repeated quartering of a squared-variation bound. -/
def quarterVariation : Nat -> Coordinate -> Coordinate
  | 0, bound => bound
  | depth + 1, bound => quarterVariation depth (bound / 4)

/-- Repeated quartering preserves upper bounds.  This lets an explicit
certificate cache a short dyadic upper approximation to the expensive parent
variation instead of forcing the kernel to normalize that exact rational. -/
theorem quarterVariation_mono (depth : Nat) {left right : Coordinate}
    (lessEqual : left <= right) :
    quarterVariation depth left <= quarterVariation depth right := by
  induction depth generalizing left right with
  | zero => exact lessEqual
  | succ depth inductionHypothesis =>
      apply inductionHypothesis
      apply (RFAP.ConstructiveFraction.div_le_iff_pos (by decide)).2
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne]
      · exact lessEqual
      · decide

/-- Every edge at one dyadic depth has the same variation majorant.  This
lets explicit finite clients cache the parent segment calculation once,
rather than replaying its dense-Horner scan for every edge. -/
theorem variationBound_dyadicEdgeAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint) (index : Fin (2 ^ depth)) :
    variationBound segment
        (dyadicEdgeAt depth left right index).left.parameter
        (dyadicEdgeAt depth left right index).right.parameter =
      quarterVariation depth
        (variationBound segment left.parameter right.parameter) := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      unfold dyadicEdgeAt
      dsimp only
      split
      · rw [inductionHypothesis, variationBound_left_midpoint]
        rfl
      · rw [inductionHypothesis, variationBound_midpoint_right]
        rfl

@[simp] theorem dyadicTargets_length (depth : Nat)
    (left right : Endpoint) :
    (dyadicTargets depth left right).length = 2 ^ depth := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [dyadicTargets, List.length_append,
        inductionHypothesis, pow_succ]
      omega

@[simp] theorem dyadicTargets_finalTarget (depth : Nat)
    (left right : Endpoint) :
    finalTarget left (dyadicTargets depth left right) = right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      rw [dyadicTargets, finalTarget_append,
        inductionHypothesis left middle,
        inductionHypothesis middle right]

/-- Extracting consecutive edges from the target-list presentation gives the
same retained-endpoint mesh as `dyadicEdges`. -/
theorem parameterEdgesFrom_dyadicTargets (depth : Nat)
    (left right : Endpoint) :
    parameterEdgesFrom left (dyadicTargets depth left right) =
      dyadicEdges depth left right := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      rw [dyadicTargets, parameterEdgesFrom_append,
        dyadicTargets_finalTarget]
      change
        parameterEdgesFrom left (dyadicTargets depth left middle) ++
            parameterEdgesFrom middle (dyadicTargets depth middle right) =
          dyadicEdges depth left middle ++ dyadicEdges depth middle right
      rw [inductionHypothesis, inductionHypothesis]

/-- Every consecutive edge in one displayed endpoint list satisfies the same
rational polynomial-variation bound. -/
def EdgeVariationBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (bound : Coordinate) : Endpoint -> List Endpoint -> Prop
  | _current, [] => True
  | current, endpoint :: remaining =>
      current.parameter <= endpoint.parameter /\
        variationBound segment current.parameter endpoint.parameter <= bound /\
          EdgeVariationBound segment bound endpoint remaining

namespace EdgeVariationBound

/-- Uniform edge bounds concatenate at the exact displayed final endpoint. -/
theorem append {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (bound : Coordinate) :
    forall (current : Endpoint) (first second : List Endpoint),
      EdgeVariationBound segment bound current first ->
        EdgeVariationBound segment bound (finalTarget current first) second ->
          EdgeVariationBound segment bound current (first ++ second)
  | _current, [], _second, _firstBound, secondBound => secondBound
  | _current, endpoint :: remaining, second, firstBound, secondBound =>
      ⟨firstBound.1, firstBound.2.1,
        append segment bound endpoint remaining second firstBound.2.2
          secondBound⟩

end EdgeVariationBound

private theorem quarterRadius_div_four (scale : Coordinate) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius (scale / 4) index =
      CCL.FiniteGeometric.quarterRadius scale (index + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Coordinate) := by
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ConstructiveFraction.one_mul]
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

/-- Every edge of the depth-`n` dyadic mesh has at most the original segment
variation divided by `4^n`.  This is an exact finite mesh estimate and is the
quantitative input used by prepared-safety and integration schedules. -/
theorem dyadicTargets_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (depth : Nat) (left right : Endpoint)
    (ordered : left.parameter <= right.parameter) :
    EdgeVariationBound segment
      (CCL.FiniteGeometric.quarterRadius
        (variationBound segment left.parameter right.parameter) depth)
      left (dyadicTargets depth left right) := by
  induction depth generalizing left right with
  | zero =>
      refine ⟨ordered, ?_, trivial⟩
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct]
  | succ depth inductionHypothesis =>
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter,
          midpoint_inside left.inside right.inside⟩
      have leftBound := inductionHypothesis left middle
        (left_le_midpoint ordered)
      have rightBound := inductionHypothesis middle right
        (midpoint_le_right ordered)
      have leftScale :
          CCL.FiniteGeometric.quarterRadius
              (variationBound segment left.parameter middle.parameter) depth =
            CCL.FiniteGeometric.quarterRadius
              (variationBound segment left.parameter right.parameter)
                (depth + 1) := by
        change CCL.FiniteGeometric.quarterRadius
            (variationBound segment left.parameter
              (midpoint left.parameter right.parameter)) depth = _
        rw [variationBound_left_midpoint]
        exact quarterRadius_div_four _ _
      have rightScale :
          CCL.FiniteGeometric.quarterRadius
              (variationBound segment middle.parameter right.parameter) depth =
            CCL.FiniteGeometric.quarterRadius
              (variationBound segment left.parameter right.parameter)
                (depth + 1) := by
        change CCL.FiniteGeometric.quarterRadius
            (variationBound segment
              (midpoint left.parameter right.parameter) right.parameter)
              depth = _
        rw [variationBound_midpoint_right]
        exact quarterRadius_div_four _ _
      rw [leftScale] at leftBound
      rw [rightScale] at rightBound
      change EdgeVariationBound segment _ left
        (dyadicTargets depth left middle ++
          dyadicTargets depth middle right)
      apply EdgeVariationBound.append segment _ left
        (dyadicTargets depth left middle)
          (dyadicTargets depth middle right) leftBound
      simpa only [dyadicTargets_finalTarget] using rightBound

/-- The purely geometric path through a displayed endpoint list.  This is
the owner-independent mesh shared by the lifted cycle and the continuation
checker. -/
def geometricPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint) :
    (remaining : List Endpoint) ->
      ClearPath polynomial ambient (segment.pointAt current.parameter)
        (segment.pointAt (finalTarget current remaining).parameter)
  | [] => .nil _
  | endpoint :: rest =>
      .cons
        (segment.restrict within current.parameter endpoint.parameter
          current.inside endpoint.inside)
        (geometricPath segment within endpoint rest)

@[simp] theorem geometricPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (remaining : List Endpoint) :
    (geometricPath segment within current remaining).segmentCount =
      remaining.length := by
  induction remaining generalizing current with
  | nil => rfl
  | cons endpoint rest inductionHypothesis =>
      simp only [geometricPath, ClearPath.segmentCount, List.length_cons]
      exact congrArg Nat.succ (inductionHypothesis endpoint)

/-- The ordered depth-`n` dyadic refinement as a finite clear path. -/
def dyadicPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat)
    (left right : Endpoint) :
    ClearPath polynomial ambient (segment.pointAt left.parameter)
      (segment.pointAt right.parameter) :=
  (geometricPath segment within left (dyadicTargets depth left right)).castFinish
    (congrArg (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (dyadicTargets_finalTarget depth left right))

@[simp] theorem dyadicPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (depth : Nat)
    (left right : Endpoint) :
    (dyadicPath segment within depth left right).segmentCount = 2 ^ depth := by
  simp only [dyadicPath, ClearPath.segmentCount_castFinish,
    geometricPath_segmentCount, dyadicTargets_length]

/-- Total checker for the depth-`n` dyadic mesh.  Increasing `depth`
quarters the a priori polynomial variation on every geometric half-edge;
the returned option still checks the actual inherited owner clearances. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) :
    Option (Subdivision segment within left.parameter left.inside owner) :=
  trySamples segment within left owner (dyadicTargets depth left right)

theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat)
    {subdivision : Subdivision segment within left.parameter left.inside owner}
    (success : tryDyadic segment within left right owner depth =
      some subdivision) :
    subdivision.stepCount = 2 ^ depth := by
  exact (trySamples_stepCount segment within left owner
    (dyadicTargets depth left right) success).trans
      (dyadicTargets_length depth left right)

theorem tryDyadic_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat)
    {subdivision : Subdivision segment within left.parameter left.inside owner}
    (success : tryDyadic segment within left right owner depth =
      some subdivision) :
    subdivision.endpoint.parameter = right.parameter := by
  have endpoint := trySamples_endpoint_parameter segment within left owner
    (dyadicTargets depth left right) success
  simpa only [dyadicTargets_finalTarget] using endpoint

/-- The checked parameter mesh as an actual concatenation of restrictions of
the original clear segment.  Its endpoint is indexed by the subdivision's
computed final parameter, so the geometry and the owner continuation cannot
silently use different meshes. -/
def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      ClearPath polynomial ambient (segment.pointAt left)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop left _ _ => .nil (segment.pointAt left)
  | .next left leftInside _ right rightInside _ remaining =>
      .cons
        (segment.restrict within left right leftInside rightInside)
        remaining.toClearPath

/-- Every geometric restriction produced from a checked subdivision remains
inside the original segment's ambient box. -/
theorem toClearPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.WithinAmbient := by
  induction subdivision with
  | stop => exact .nil _
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact .cons
        (segment.restrict_withinAmbient within left right leftInside rightInside)
        inductionHypothesis

@[simp] theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toClearPath.segmentCount = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Forget the base parameters while retaining every same-owner Rouché
transport as a general finite continuation chain. -/
def toChain {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))} :
    (subdivision : Subdivision segment within left leftInside owner) →
      Chain ⟨polynomial.eval (segment.pointAt left), owner⟩
  | .stop _ _ _ => .nil _
  | .next left leftInside owner right rightInside small remaining => by
      let target := polynomial.eval (segment.pointAt right)
      let targetNonzero := segment.pointAt_eval_ne_zero right rightInside
      let moveSmall :
          RFAP.ConstructiveGaussian.Gaussian.normSq
              (polynomial.eval (segment.pointAt left) - target) <
            owner.track.initial.clearance.bound :=
        (evaluation_variation_le segment within left right leftInside
          rightInside).trans_lt small
      exact .step _ target targetNonzero moveSmall remaining.toChain

@[simp] theorem toChain_endpoint_parameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toChain.endpoint.parameter =
      polynomial.eval (segment.pointAt subdivision.endpoint.parameter) := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact inductionHypothesis

@[simp] theorem toChain_length {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    {owner : Owner (polynomial.eval (segment.pointAt left))}
    (subdivision : Subdivision segment within left leftInside owner) :
    subdivision.toChain.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left leftInside owner right rightInside small remaining
      inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

/-- Root an adaptive subdivision at one canonical sheet owner. -/
def seeded {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Coordinate}
    {leftInside : (0 : Coordinate) <= left ∧ left <= 1}
    (sheet : Fin 2)
    (subdivision : Subdivision segment within left leftInside
      (CCL.Riemann.SquareRootContinuationChain.Owner.independent
        (segment.pointAt_eval_ne_zero left leftInside) sheet)) :
    CCL.Riemann.SquareRootContinuationChain.SeededChain
      (polynomial.eval (segment.pointAt left))
      (segment.pointAt_eval_ne_zero left leftInside) where
  sheet := sheet
  continuation := subdivision.toChain

end Subdivision

end CCL.Riemann.ClearSheetContinuation
