import CCL.Riemann.BranchConfiguration

/-!
# Certified rational branch cuts

The initial isolation boxes come with polynomial-clear coordinate lines across
the one finite ambient square.  Consequently two finite branch boxes can be
joined by a rational L-shaped path: first along the lower edge line of the
left box, then along the left edge line of the right box.  An odd-degree
infinity cut exits along the same clear horizontal line to the right boundary
of the ambient square.  Every segment below stores its finite line-clearance
certificate; there is no appeal to a complement of an infinite point set.
-/

namespace CCL.Riemann.BranchCuts

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchIsolation
open CCL.Riemann.BranchConfiguration

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

abbrev point := RFAP.Winding.point

open RFAP.ConstructiveGaussian.Gaussian

/-- A polynomial-clear rational axis segment inside the common ambient box.
The dependent endpoints make concatenation exact rather than propositional. -/
inductive ClearSegment (polynomial : GaussianPolynomial) (ambient : Box) :
    Gaussian -> Gaussian -> Type
  | horizontal (xStart xFinish y : Coordinate)
      (startLower : ambient.xLower <= xStart)
      (startUpper : xStart <= ambient.xUpper)
      (finishLower : ambient.xLower <= xFinish)
      (finishUpper : xFinish <= ambient.xUpper)
      (clearance : RFAP.BoxClearance.HorizontalLineClearance
        polynomial ambient y) :
      ClearSegment polynomial ambient (point xStart y) (point xFinish y)
  | vertical (x yStart yFinish : Coordinate)
      (startLower : ambient.yLower <= yStart)
      (startUpper : yStart <= ambient.yUpper)
      (finishLower : ambient.yLower <= yFinish)
      (finishUpper : yFinish <= ambient.yUpper)
      (clearance : RFAP.BoxClearance.VerticalLineClearance
        polynomial ambient x) :
      ClearSegment polynomial ambient (point x yStart) (point x yFinish)

namespace ClearSegment

/-- The fixed positive squared-modulus lower bound carried by the certified
coordinate line underlying a clear segment. -/
def clearanceBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  match segment with
  | .horizontal _ _ _ _ _ _ _ clearance => clearance.bound
  | .vertical _ _ _ _ _ _ _ clearance => clearance.bound

theorem clearanceBound_positive {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < segment.clearanceBound := by
  cases segment with
  | horizontal _ _ _ _ _ _ _ clearance => exact clearance.positive
  | vertical _ _ _ _ _ _ _ clearance => exact clearance.positive

/-- A rational point on the certified ambient portion of the segment's
coordinate line.  This deliberately describes a superset of the oriented
segment, so its exclusion theorem is immediately reusable after subdivision. -/
def OnCertifiedLine {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (value : Gaussian) : Prop :=
  match segment with
  | .horizontal _ _ y _ _ _ _ _ =>
      value.im = y ∧ ambient.xLower <= value.re ∧ value.re <= ambient.xUpper
  | .vertical x _ _ _ _ _ _ _ =>
      value.re = x ∧ ambient.yLower <= value.im ∧ value.im <= ambient.yUpper

/-- The line-clearance number uniformly bounds the polynomial on every
displayed rational point of the certified ambient line. -/
theorem clearanceBound_le_eval_normSq {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish value : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    segment.clearanceBound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (polynomial.eval value) := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨imaginary, lower, upper⟩
      have bound := clearance.lower value.re lower upper
      have valueEqual : point value.re y = value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact imaginary.symm
      simpa only [clearanceBound, valueEqual] using bound
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨real, lower, upper⟩
      have bound := clearance.lower value.im lower upper
      have valueEqual : point x value.im = value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact real.symm
        · rfl
      simpa only [clearanceBound, valueEqual] using bound

/-- Rational affine parameterization of a displayed clear segment. -/
def pointAt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) : Gaussian :=
  start + CCL.FiniteExp.scale parameter (finish - start)

@[simp] theorem pointAt_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.pointAt 0 = start := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [pointAt, CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1

@[simp] theorem pointAt_one {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.pointAt 1 = finish := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [pointAt, CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1

/-- Every parameter in the rational unit interval stays on the certified
ambient portion of the segment's clearance line. -/
theorem pointAt_onCertifiedLine {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    segment.OnCertifiedLine (segment.pointAt parameter) := by
  have oneMinusNonnegative : (0 : Coordinate) <= 1 - parameter :=
    RFAP.ConstructiveFraction.sub_nonneg_direct inside.2
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have realFormula :
          (point xStart y +
            CCL.FiniteExp.scale parameter
              (point xFinish y - point xStart y)).re =
            (1 - parameter) * xStart + parameter * xFinish := by
        simp only [add_re, sub_re, CCL.FiniteExp.scale_re,
          RFAP.Winding.point]
        ring1
      refine ⟨?_, ?_, ?_⟩
      · simp only [pointAt, add_im, sub_im, CCL.FiniteExp.scale_im,
          RFAP.Winding.point]
        ring1
      · change ambient.xLower <=
          (point xStart y + CCL.FiniteExp.scale parameter
            (point xFinish y - point xStart y)).re
        rw [realFormula]
        calc
          ambient.xLower =
              (1 - parameter) * ambient.xLower +
                parameter * ambient.xLower := by ring1
          _ <= (1 - parameter) * xStart + parameter * xFinish :=
            add_le_add
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                startLower oneMinusNonnegative)
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                finishLower inside.1)
      · change
          (point xStart y + CCL.FiniteExp.scale parameter
            (point xFinish y - point xStart y)).re <= ambient.xUpper
        rw [realFormula]
        calc
          (1 - parameter) * xStart + parameter * xFinish <=
              (1 - parameter) * ambient.xUpper +
                parameter * ambient.xUpper :=
            add_le_add
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                startUpper oneMinusNonnegative)
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                finishUpper inside.1)
          _ = ambient.xUpper := by ring1
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have imaginaryFormula :
          (point x yStart +
            CCL.FiniteExp.scale parameter
              (point x yFinish - point x yStart)).im =
            (1 - parameter) * yStart + parameter * yFinish := by
        simp only [add_im, sub_im, CCL.FiniteExp.scale_im,
          RFAP.Winding.point]
        ring1
      refine ⟨?_, ?_, ?_⟩
      · simp only [pointAt, add_re, sub_re, CCL.FiniteExp.scale_re,
          RFAP.Winding.point]
        ring1
      · change ambient.yLower <=
          (point x yStart + CCL.FiniteExp.scale parameter
            (point x yFinish - point x yStart)).im
        rw [imaginaryFormula]
        calc
          ambient.yLower =
              (1 - parameter) * ambient.yLower +
                parameter * ambient.yLower := by ring1
          _ <= (1 - parameter) * yStart + parameter * yFinish :=
            add_le_add
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                startLower oneMinusNonnegative)
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                finishLower inside.1)
      · change
          (point x yStart + CCL.FiniteExp.scale parameter
            (point x yFinish - point x yStart)).im <= ambient.yUpper
        rw [imaginaryFormula]
        calc
          (1 - parameter) * yStart + parameter * yFinish <=
              (1 - parameter) * ambient.yUpper +
                parameter * ambient.yUpper :=
            add_le_add
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                startUpper oneMinusNonnegative)
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                finishUpper inside.1)
          _ = ambient.yUpper := by ring1

/-- The segment's fixed coordinate also lies in the ambient box.  Line
clearance itself is meaningful outside the box in that coordinate, so this
geometric fact is recorded separately. -/
def WithinAmbient {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Prop :=
  match segment with
  | .horizontal _ _ y _ _ _ _ _ =>
      ambient.yLower <= y ∧ y <= ambient.yUpper
  | .vertical x _ _ _ _ _ _ _ =>
      ambient.xLower <= x ∧ x <= ambient.xUpper

/-- A point on an ambient-contained certified line lies in the ambient box. -/
theorem contains_of_onCertifiedLine {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish value : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (onLine : segment.OnCertifiedLine value) : ambient.Contains value := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      exact ⟨onLine.2.1, onLine.2.2,
        by rw [onLine.1]; exact within.1,
        by rw [onLine.1]; exact within.2⟩
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      exact ⟨by rw [onLine.1]; exact within.1,
        by rw [onLine.1]; exact within.2,
        onLine.2.1, onLine.2.2⟩

theorem pointAt_contains {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    ambient.Contains (segment.pointAt parameter) :=
  segment.contains_of_onCertifiedLine within
    (segment.pointAt_onCertifiedLine parameter inside)

/-- Difference of two affine samples on the same segment. -/
theorem pointAt_sub_pointAt {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    segment.pointAt left - segment.pointAt right =
      CCL.FiniteExp.scale (left - right) (finish - start) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [pointAt, CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      add_re, add_im, sub_re, sub_im] <;> ring1

theorem normSq_pointAt_sub_pointAt {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (segment.pointAt left - segment.pointAt right) =
      (left - right) ^ 2 *
        RFAP.ConstructiveGaussian.Gaussian.normSq (finish - start) := by
  rw [segment.pointAt_sub_pointAt left right, CCL.FiniteExp.normSq_scale]

/-- A unit-interval point is no farther from the local start than the full
affine segment displacement. -/
theorem normSq_pointAt_sub_zero_le_full {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (segment.pointAt parameter - segment.pointAt 0) <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (segment.pointAt 1 - segment.pointAt 0) := by
  have squareLe : parameter ^ 2 <= (1 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct inside.1 inside.2 2
  have squareDifferenceLe : (parameter - 0) ^ 2 <=
      ((1 : Coordinate) - 0) ^ 2 := by
    convert squareLe using 1 <;> ring1
  rw [segment.normSq_pointAt_sub_pointAt parameter 0,
    segment.normSq_pointAt_sub_pointAt 1 0]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    squareDifferenceLe
    (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg (finish - start))

/-- Every rational point of a horizontal segment has nonzero polynomial
evaluation.  The interval hypotheses deliberately retain the segment's
orientation-free closed interval. -/
theorem horizontal_eval_ne_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {y : Coordinate}
    (clearance : RFAP.BoxClearance.HorizontalLineClearance
      polynomial ambient y)
    (x : Coordinate) (lower : ambient.xLower <= x)
    (upper : x <= ambient.xUpper) :
    polynomial.eval (point x y) ≠ 0 := by
  intro zero
  have bound := clearance.lower x lower upper
  rw [zero, normSq_zero] at bound
  exact (not_lt_of_ge bound) clearance.positive

/-- Every rational point of a vertical segment has nonzero polynomial
evaluation. -/
theorem vertical_eval_ne_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {x : Coordinate}
    (clearance : RFAP.BoxClearance.VerticalLineClearance
      polynomial ambient x)
    (y : Coordinate) (lower : ambient.yLower <= y)
    (upper : y <= ambient.yUpper) :
    polynomial.eval (point x y) ≠ 0 := by
  intro zero
  have bound := clearance.lower y lower upper
  rw [zero, normSq_zero] at bound
  exact (not_lt_of_ge bound) clearance.positive

/-- Every rational point on the certified line portion—and hence every point
of the displayed segment—avoids every finite branch root. -/
theorem eval_ne_zero {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish value : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    polynomial.eval value ≠ 0 := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨imaginary, lower, upper⟩
      have nonzero := horizontal_eval_ne_zero clearance value.re lower upper
      have valueEqual : point value.re y = value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact imaginary.symm
      rw [valueEqual] at nonzero
      exact nonzero
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨real, lower, upper⟩
      have nonzero := vertical_eval_ne_zero clearance value.im lower upper
      have valueEqual : point x value.im = value := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact real.symm
        · rfl
      rw [valueEqual] at nonzero
      exact nonzero

/-- Polynomial nonvanishing at every displayed rational unit-interval
parameter of a clear segment. -/
theorem pointAt_eval_ne_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    polynomial.eval (segment.pointAt parameter) ≠ 0 :=
  segment.eval_ne_zero (segment.pointAt_onCertifiedLine parameter inside)

/-- Join any two displayed points on the same certified line. -/
def betweenOnCertifiedLine {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish left right : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (leftOn : segment.OnCertifiedLine left)
    (rightOn : segment.OnCertifiedLine right) :
    ClearSegment polynomial ambient left right := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq : point left.re y = left := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact leftOn.1.symm
      have rightEq : point right.re y = right := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact rightOn.1.symm
      rw [← leftEq, ← rightEq]
      exact .horizontal left.re right.re y
        leftOn.2.1 leftOn.2.2 rightOn.2.1 rightOn.2.2 clearance
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq : point x left.im = left := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact leftOn.1.symm
        · rfl
      have rightEq : point x right.im = right := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact rightOn.1.symm
        · rfl
      rw [← leftEq, ← rightEq]
      exact .vertical x left.im right.im
        leftOn.2.1 leftOn.2.2 rightOn.2.1 rightOn.2.2 clearance

/-- Restrict an ambient-contained clear segment to two rational unit-interval
parameters, retaining the containment proof together with the segment. -/
def castStart {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian}
    (segment : ClearSegment polynomial ambient left finish)
    (equal : left = right) :
    ClearSegment polynomial ambient right finish := by
  subst right
  exact segment

def castFinish {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian}
    (segment : ClearSegment polynomial ambient start left)
    (equal : left = right) :
    ClearSegment polynomial ambient start right := by
  subst right
  exact segment

theorem castStart_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian}
    (segment : ClearSegment polynomial ambient left finish)
    (within : segment.WithinAmbient) (equal : left = right) :
    (segment.castStart equal).WithinAmbient := by
  subst right
  exact within

theorem castFinish_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian}
    (segment : ClearSegment polynomial ambient start left)
    (within : segment.WithinAmbient) (equal : left = right) :
    (segment.castFinish equal).WithinAmbient := by
  subst right
  exact within

@[simp] theorem castStart_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian}
    (segment : ClearSegment polynomial ambient left finish)
    (equal : left = right) :
    (segment.castStart equal).clearanceBound = segment.clearanceBound := by
  subst right
  rfl

@[simp] theorem castFinish_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian}
    (segment : ClearSegment polynomial ambient start left)
    (equal : left = right) :
    (segment.castFinish equal).clearanceBound = segment.clearanceBound := by
  subst right
  rfl

def restriction {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    { restricted : ClearSegment polynomial ambient
        (segment.pointAt left) (segment.pointAt right) //
      restricted.WithinAmbient ∧
        restricted.clearanceBound = segment.clearanceBound } := by
  have leftOn := segment.pointAt_onCertifiedLine left leftInside
  have rightOn := segment.pointAt_onCertifiedLine right rightInside
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq :
          point
              ((ClearSegment.horizontal xStart xFinish y startLower startUpper
                finishLower finishUpper clearance).pointAt left).re y =
            (ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt left := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact leftOn.1.symm
      have rightEq :
          point
              ((ClearSegment.horizontal xStart xFinish y startLower startUpper
                finishLower finishUpper clearance).pointAt right).re y =
            (ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt right := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · rfl
        · exact rightOn.1.symm
      let raw : ClearSegment polynomial ambient
          (point
            ((ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt left).re y)
          (point
            ((ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt right).re y) :=
        .horizontal _ _ y leftOn.2.1 leftOn.2.2
          rightOn.2.1 rightOn.2.2 clearance
      exact ⟨(raw.castStart leftEq).castFinish rightEq,
        castFinish_withinAmbient (raw.castStart leftEq)
          (raw.castStart_withinAmbient within leftEq) rightEq,
        by
          calc
            ((raw.castStart leftEq).castFinish rightEq).clearanceBound =
                (raw.castStart leftEq).clearanceBound :=
              castFinish_clearanceBound (raw.castStart leftEq) rightEq
            _ = raw.clearanceBound := castStart_clearanceBound raw leftEq
            _ = (ClearSegment.horizontal xStart xFinish y startLower
                startUpper finishLower finishUpper clearance).clearanceBound :=
              rfl⟩
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq :
          point x
              ((ClearSegment.vertical x yStart yFinish startLower startUpper
                finishLower finishUpper clearance).pointAt left).im =
            (ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt left := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact leftOn.1.symm
        · rfl
      have rightEq :
          point x
              ((ClearSegment.vertical x yStart yFinish startLower startUpper
                finishLower finishUpper clearance).pointAt right).im =
            (ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt right := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext
        · exact rightOn.1.symm
        · rfl
      let raw : ClearSegment polynomial ambient
          (point x
            ((ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt left).im)
          (point x
            ((ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt right).im) :=
        .vertical x _ _ leftOn.2.1 leftOn.2.2
          rightOn.2.1 rightOn.2.2 clearance
      exact ⟨(raw.castStart leftEq).castFinish rightEq,
        castFinish_withinAmbient (raw.castStart leftEq)
          (raw.castStart_withinAmbient within leftEq) rightEq,
        by
          calc
            ((raw.castStart leftEq).castFinish rightEq).clearanceBound =
                (raw.castStart leftEq).clearanceBound :=
              castFinish_clearanceBound (raw.castStart leftEq) rightEq
            _ = raw.clearanceBound := castStart_clearanceBound raw leftEq
            _ = (ClearSegment.vertical x yStart yFinish startLower
                startUpper finishLower finishUpper clearance).clearanceBound :=
              rfl⟩

/-- The segment component of an ambient-contained restriction. -/
def restrict {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    ClearSegment polynomial ambient
      (segment.pointAt left) (segment.pointAt right) :=
  (segment.restriction within left right leftInside rightInside).1

/-- Restricting the displayed endpoints retains the certified coordinate
line and therefore its cached polynomial-clearance bound exactly. -/
@[simp] theorem restrict_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    (segment.restrict within left right leftInside
      rightInside).clearanceBound = segment.clearanceBound :=
  (segment.restriction within left right leftInside rightInside).2.2

theorem restrict_withinAmbient {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Coordinate)
    (leftInside : (0 : Coordinate) <= left ∧ left <= 1)
    (rightInside : (0 : Coordinate) <= right ∧ right <= 1) :
    (segment.restrict within left right leftInside rightInside).WithinAmbient :=
  (segment.restriction within left right leftInside rightInside).2.1

theorem start_onCertifiedLine {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.OnCertifiedLine start := by
  cases segment with
  | horizontal => exact ⟨rfl, ‹_›, ‹_›⟩
  | vertical => exact ⟨rfl, ‹_›, ‹_›⟩

theorem finish_onCertifiedLine {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.OnCertifiedLine finish := by
  cases segment with
  | horizontal => exact ⟨rfl, ‹_›, ‹_›⟩
  | vertical => exact ⟨rfl, ‹_›, ‹_›⟩

theorem start_eval_ne_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    polynomial.eval start ≠ 0 :=
  segment.eval_ne_zero segment.start_onCertifiedLine

theorem finish_eval_ne_zero {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    polynomial.eval finish ≠ 0 :=
  segment.eval_ne_zero segment.finish_onCertifiedLine

end ClearSegment

/-- A finite concatenation of certified axis segments. -/
inductive ClearPath (polynomial : GaussianPolynomial) (ambient : Box) :
    Gaussian -> Gaussian -> Type
  | nil (point : Gaussian) : ClearPath polynomial ambient point point
  | cons {start middle finish : Gaussian}
      (head : ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish) :
      ClearPath polynomial ambient start finish

namespace ClearPath

/-- Every segment of the finite path has its fixed line coordinate inside
the common ambient box. -/
inductive WithinAmbient {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} →
      ClearPath polynomial ambient start finish → Prop
  | nil (point : Gaussian) : WithinAmbient (.nil point)
  | cons {start middle finish : Gaussian}
      {head : ClearSegment polynomial ambient start middle}
      {tail : ClearPath polynomial ambient middle finish}
      (headWithin : head.WithinAmbient)
      (tailWithin : WithinAmbient tail) :
      WithinAmbient (.cons head tail)

theorem WithinAmbient.head {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    {head : ClearSegment polynomial ambient start middle}
    {tail : ClearPath polynomial ambient middle finish}
    (within : WithinAmbient (.cons head tail)) : head.WithinAmbient := by
  cases within with
  | cons headWithin _ => exact headWithin

theorem WithinAmbient.tail {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    {head : ClearSegment polynomial ambient start middle}
    {tail : ClearPath polynomial ambient middle finish}
    (within : WithinAmbient (.cons head tail)) : WithinAmbient tail := by
  cases within with
  | cons _ tailWithin => exact tailWithin

def segmentCount {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      ClearPath polynomial ambient start finish -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.segmentCount + 1

def append {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    (first : ClearPath polynomial ambient start middle)
    (second : ClearPath polynomial ambient middle finish) :
    ClearPath polynomial ambient start finish :=
  match first with
  | .nil _ => second
  | .cons head tail => .cons head (tail.append second)

theorem WithinAmbient.append {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian}
    {first : ClearPath polynomial ambient start middle}
    {second : ClearPath polynomial ambient middle finish}
    (firstWithin : WithinAmbient first)
    (secondWithin : WithinAmbient second) :
    WithinAmbient (first.append second) := by
  induction firstWithin with
  | nil => exact secondWithin
  | cons headWithin tailWithin inductionHypothesis =>
      exact .cons headWithin (inductionHypothesis secondWithin)

/-- Change only the propositionally equal starting-point index. -/
def castStart {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian} (equal : left = right)
    (path : ClearPath polynomial ambient left finish) :
    ClearPath polynomial ambient right finish := by
  subst right
  exact path

/-- Change only the propositionally equal finishing-point index. -/
def castFinish {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian} (equal : left = right)
    (path : ClearPath polynomial ambient start left) :
    ClearPath polynomial ambient start right := by
  subst right
  exact path

@[simp] theorem castStart_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {startLeft startRight finishLeft finishRight : Gaussian}
    (path : ClearPath polynomial ambient startLeft finishLeft)
    (startEqual : startLeft = startRight)
    (finishEqual : finishLeft = finishRight) :
    (path.castStart startEqual).castFinish finishEqual =
      (path.castFinish finishEqual).castStart startEqual := by
  subst startRight
  subst finishRight
  rfl

@[simp] theorem segmentCount_castStart
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian} (equal : left = right)
    (path : ClearPath polynomial ambient left finish) :
    (path.castStart equal).segmentCount = path.segmentCount := by
  subst right
  rfl

@[simp] theorem segmentCount_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian} (equal : left = right)
    (path : ClearPath polynomial ambient start left) :
    (path.castFinish equal).segmentCount = path.segmentCount := by
  subst right
  rfl

@[simp] theorem castFinish_cons
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle left right : Gaussian}
    (head : ClearSegment polynomial ambient start middle)
    (tail : ClearPath polynomial ambient middle left)
    (equal : left = right) :
    (ClearPath.cons head tail).castFinish equal =
      .cons head (tail.castFinish equal) := by
  subst right
  rfl

@[simp] theorem castFinish_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start first second third : Gaussian}
    (path : ClearPath polynomial ambient start first)
    (firstEqual : first = second) (secondEqual : second = third) :
    (path.castFinish firstEqual).castFinish secondEqual =
      path.castFinish (firstEqual.trans secondEqual) := by
  subst second
  subst third
  rfl

@[simp] theorem segmentCount_append {polynomial : GaussianPolynomial}
    {ambient : Box} {start middle finish : Gaussian}
    (first : ClearPath polynomial ambient start middle)
    (second : ClearPath polynomial ambient middle finish) :
    (first.append second).segmentCount =
      first.segmentCount + second.segmentCount := by
  induction first with
  | nil => simp only [append, segmentCount, Nat.zero_add]
  | cons head tail inductionHypothesis =>
      simp only [append, segmentCount, inductionHypothesis]
      omega0

end ClearPath

abbrev Ambient {genus : Nat} (curve : HyperellipticCurve genus) :=
  RFAP.GlobalWinding.largeSquareBox curve.polynomial

/-- The lower-left anchor of the actual initial track box. -/
def trackAnchor {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) : Gaussian :=
  (branches.track degreeGtOne index).initial.box.anchor

theorem trackAnchor_eq_branchAnchor {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) :
    trackAnchor branches degreeGtOne index = branches.anchor index :=
  branches.track_initial_anchor degreeGtOne index

/-- The deterministic nested winding state used at one finite path
refinement. -/
def refinedState {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) :=
  CCL.Riemann.CoherentRoot.state (branches.track degreeGtOne index) refinement

/-- The rational endpoint at one finite refinement of a branch cut.  These
anchors remain nested around the same winding-one owner. -/
def refinedTrackAnchor {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) : Gaussian :=
  (refinedState branches degreeGtOne index refinement).box.anchor

@[simp] theorem refinedTrackAnchor_zero {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) :
    refinedTrackAnchor branches degreeGtOne index 0 =
      trackAnchor branches degreeGtOne index := rfl

/-- The automatic two-segment connector at an arbitrary deterministic root
refinement.  Unlike `finiteConnector`, its endpoints converge coherently to
the two branch occurrences while every finite segment stays on a certified
polynomial-clear ambient line. -/
def finiteConnectorAt {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    ClearPath curve.polynomial (Ambient curve)
      (refinedTrackAnchor branches degreeGtOne left refinement)
      (refinedTrackAnchor branches degreeGtOne right refinement) := by
  let leftState := refinedState branches degreeGtOne left refinement
  let rightState := refinedState branches degreeGtOne right refinement
  exact .cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil (refinedTrackAnchor branches degreeGtOne right refinement)))

@[simp] theorem finiteConnectorAt_segmentCount {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    (finiteConnectorAt branches degreeGtOne left right refinement).segmentCount =
      2 := by
  rfl

theorem finiteConnectorAt_withinAmbient {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    (finiteConnectorAt branches degreeGtOne left right refinement).WithinAmbient := by
  let leftState := refinedState branches degreeGtOne left refinement
  let rightState := refinedState branches degreeGtOne right refinement
  exact .cons
    ⟨leftState.refinesAmbient.2.2.1,
      leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2⟩
    (.cons
      ⟨rightState.refinesAmbient.1,
        rightState.box.x_valid.trans rightState.refinesAmbient.2.1⟩
      (.nil _))

/-- The left endpoint of the automatic finite connector is never a root.
This is witnessed directly by the certified horizontal clearance line. -/
theorem finiteConnectorAt_start_eval_ne_zero {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left _right : Data.Index branches) (refinement : Nat) :
    curve.polynomial.eval
        (refinedTrackAnchor branches degreeGtOne left refinement) ≠ 0 := by
  let state := refinedState branches degreeGtOne left refinement
  exact ClearSegment.horizontal_eval_ne_zero state.ambientBottomClearance
    state.box.xLower state.refinesAmbient.1
      (state.box.x_valid.trans state.refinesAmbient.2.1)

/-- The right endpoint of the automatic finite connector is never a root.
This is witnessed directly by the certified vertical clearance line. -/
theorem finiteConnectorAt_finish_eval_ne_zero {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (_left right : Data.Index branches) (refinement : Nat) :
    curve.polynomial.eval
        (refinedTrackAnchor branches degreeGtOne right refinement) ≠ 0 := by
  let state := refinedState branches degreeGtOne right refinement
  exact ClearSegment.vertical_eval_ne_zero state.ambientLeftClearance
    state.box.yLower state.refinesAmbient.2.2.1
      (state.box.y_valid.trans state.refinesAmbient.2.2.2)

theorem refinedTrackAnchor_residual_le {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (curve.polynomial.eval
          (refinedTrackAnchor branches degreeGtOne index refinement)) <=
      CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.CoherentRoot.residualScale curve.polynomial
          (Ambient curve) (branches.track degreeGtOne index)) refinement :=
  CCL.Riemann.CoherentRoot.sample_residual_le
    (branches.track degreeGtOne index)
    (BranchIsolation.degreePositive curve) refinement

/-- The automatic two-segment connector between two higher-degree branch
boxes. -/
def finiteConnector {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) :
    ClearPath curve.polynomial (Ambient curve)
      (trackAnchor branches degreeGtOne left)
      (trackAnchor branches degreeGtOne right) := by
  let leftState := (branches.track degreeGtOne left).initial
  let rightState := (branches.track degreeGtOne right).initial
  let corner : Gaussian :=
    point rightState.box.xLower leftState.box.yLower
  exact .cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil (trackAnchor branches degreeGtOne right)))

@[simp] theorem finiteConnector_segmentCount {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) :
    (finiteConnector branches degreeGtOne left right).segmentCount = 2 := by
  rfl

/-- A finite representative of a cut to infinity: it reaches the right edge
of the isolator's ambient square along a certified polynomial-clear line. -/
structure InfinityExit {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) where
  boundaryPoint : Gaussian
  onRightBoundary : boundaryPoint.re = (Ambient curve).xUpper
  path : ClearPath curve.polynomial (Ambient curve)
    (trackAnchor branches degreeGtOne finite) boundaryPoint

/-- Automatically exit one finite branch box to the ambient right boundary. -/
def infinityExit {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) :
    InfinityExit branches degreeGtOne finite := by
  let state := (branches.track degreeGtOne finite).initial
  let boundary := point (Ambient curve).xUpper state.box.yLower
  exact
    { boundaryPoint := boundary
      onRightBoundary := rfl
      path := .cons
        (.horizontal state.box.xLower (Ambient curve).xUpper state.box.yLower
          state.refinesAmbient.1
          (state.box.x_valid.trans state.refinesAmbient.2.1)
          (Ambient curve).x_valid
          le_rfl
          state.ambientBottomClearance)
        (.nil boundary) }

@[simp] theorem infinityExit_segmentCount {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) :
    (infinityExit branches degreeGtOne finite).path.segmentCount = 1 := by
  rfl

/-- Refined version of an infinity exit whose finite endpoint follows the
nested owner track. -/
structure RefinedInfinityExit {genus : Nat}
    {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) where
  boundaryPoint : Gaussian
  onRightBoundary : boundaryPoint.re = (Ambient curve).xUpper
  path : ClearPath curve.polynomial (Ambient curve)
    (refinedTrackAnchor branches degreeGtOne finite refinement) boundaryPoint

/-- At every finite refinement, exit the refined owner anchor along its fresh
certified lower line. -/
def infinityExitAt {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    RefinedInfinityExit branches degreeGtOne finite refinement := by
  let state := refinedState branches degreeGtOne finite refinement
  let boundary := point (Ambient curve).xUpper state.box.yLower
  exact
    { boundaryPoint := boundary
      onRightBoundary := rfl
      path := .cons
        (.horizontal state.box.xLower (Ambient curve).xUpper state.box.yLower
          state.refinesAmbient.1
          (state.box.x_valid.trans state.refinesAmbient.2.1)
          (Ambient curve).x_valid le_rfl state.ambientBottomClearance)
        (.nil boundary) }

@[simp] theorem infinityExitAt_segmentCount {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    (infinityExitAt branches degreeGtOne finite refinement).path.segmentCount =
      1 := by
  rfl

theorem infinityExitAt_withinAmbient {genus : Nat}
    {curve : HyperellipticCurve genus} (branches : Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    (infinityExitAt branches degreeGtOne finite refinement).path.WithinAmbient := by
  let state := refinedState branches degreeGtOne finite refinement
  exact .cons
    ⟨state.refinesAmbient.2.2.1,
      state.box.y_valid.trans state.refinesAmbient.2.2.2⟩
    (.nil _)

/-- Certified content of one branch cut with fixed semantic endpoints. -/
inductive Certificate {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) :
    Site curve branches -> Site curve branches -> Type
  | finite (left right : Data.Index branches)
      (different : left ≠ right)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (path : ClearPath curve.polynomial (Ambient curve)
        (trackAnchor branches degreeGtOne left)
        (trackAnchor branches degreeGtOne right)) :
      Certificate curve branches (.finite left) (.finite right)
  | toInfinity (finite : Data.Index branches)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (exit : InfinityExit branches degreeGtOne finite) :
      Certificate curve branches (.finite finite) .infinity
  | fromInfinity (finite : Data.Index branches)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (exit : InfinityExit branches degreeGtOne finite) :
      Certificate curve branches .infinity (.finite finite)
  | linearToInfinity (finite : Data.Index branches)
      (degreeOne : curve.polynomial.natDegree = 1) :
      Certificate curve branches (.finite finite) .infinity
  | infinityToLinear (finite : Data.Index branches)
      (degreeOne : curve.polynomial.natDegree = 1) :
      Certificate curve branches .infinity (.finite finite)

/-- Geometry of one branch cut.  Its endpoints are stored explicitly, so a
cut system can state exact agreement with the branch enumeration. -/
structure Geometry {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) : Type where
  leftSite : Site curve branches
  rightSite : Site curve branches
  different : leftSite ≠ rightSite
  certificate : Certificate curve branches leftSite rightSite

/-- Construct the certified content of a cut between two distinct
ramification sites. -/
def certificateBetween {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (left right : Site curve branches)
    (different : left ≠ right) : Certificate curve branches left right := by
  by_cases higher : 1 < curve.polynomial.natDegree
  · cases left with
    | finite leftIndex =>
        cases right with
        | finite rightIndex =>
            have indexDifferent : leftIndex ≠ rightIndex := by
              intro equal
              apply different
              rw [equal]
            exact .finite leftIndex rightIndex indexDifferent higher
              (finiteConnector branches higher leftIndex rightIndex)
        | infinity =>
            exact .toInfinity leftIndex higher
              (infinityExit branches higher leftIndex)
    | infinity =>
        cases right with
        | finite rightIndex =>
            exact .fromInfinity rightIndex higher
              (infinityExit branches higher rightIndex)
        | infinity => exact (different rfl).elim
  · have degreeOne : curve.polynomial.natDegree = 1 := by
      have positive := degreePositive curve
      omega0
    cases left with
    | finite leftIndex =>
        cases right with
        | finite rightIndex =>
            have equalIndex : leftIndex = rightIndex := by
              apply Fin.ext
              have leftBound := leftIndex.isLt
              have rightBound := rightIndex.isLt
              have countOne : branches.siteCount = 1 :=
                branches.count_eq.trans degreeOne
              have leftBoundOne : leftIndex.val < 1 :=
                leftBound.trans_eq countOne
              have rightBoundOne : rightIndex.val < 1 :=
                rightBound.trans_eq countOne
              omega0
            exact (different (by rw [equalIndex])).elim
        | infinity =>
            exact .linearToInfinity leftIndex degreeOne
    | infinity =>
        cases right with
        | finite rightIndex =>
            exact .infinityToLinear rightIndex degreeOne
        | infinity => exact (different rfl).elim

/-- Construct a cut for any two distinct ramification sites. -/
def geometryBetween {genus : Nat} {curve : HyperellipticCurve genus}
    (branches : Data curve) (left right : Site curve branches)
    (different : left ≠ right) : Geometry curve branches where
  leftSite := left
  rightSite := right
  different := different
  certificate := certificateBetween branches left right different

/-- All `g+1` standard cuts constructed from the one persistent branch
configuration. -/
structure System {genus : Nat} (curve : HyperellipticCurve genus) where
  configuration : Configuration curve
  cutAt : Fin (genus + 1) -> Geometry curve configuration.branches
  left_eq : forall index,
    (cutAt index).leftSite =
      configuration.siteAt (standardPair index).left
  right_eq : forall index,
    (cutAt index).rightSite =
      configuration.siteAt (standardPair index).right

/-- Construct the standard consecutive branch-cut system from any audited
finite branch configuration. -/
def systemOfConfiguration {genus : Nat} (curve : HyperellipticCurve genus)
    (configuration : Configuration curve) : System curve := by
  let cutAt := fun index : Fin (genus + 1) =>
    geometryBetween configuration.branches
      (configuration.siteAt (standardPair index).left)
      (configuration.siteAt (standardPair index).right)
      (cutEndpoints_different configuration index)
  exact
    { configuration := configuration
      cutAt := cutAt
      left_eq := fun index => rfl
      right_eq := fun index => rfl }

/-- Construct the standard consecutive cut system directly from explicit
degree-complete branch data. -/
def systemOfData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : Data curve) : System curve :=
  systemOfConfiguration curve
    (BranchConfiguration.configurationOfData curve branches)

/-- Fully automatic finite branch-cut system. -/
def system {genus : Nat} (curve : HyperellipticCurve genus) : System curve :=
  systemOfConfiguration curve (BranchConfiguration.configuration curve)

/-- The automatically constructed cuts cover every branch label through the
standard consecutive pairing. -/
theorem System.covers {genus : Nat} {curve : HyperellipticCurve genus}
    (system : System curve) (position : Fin (2 * genus + 2)) :
    system.configuration.siteAt position =
        (system.cutAt (pairOf position)).leftSite \/
      system.configuration.siteAt position =
        (system.cutAt (pairOf position)).rightSite := by
  rcases standardPair_covers position with left | right
  · left
    exact (congrArg system.configuration.siteAt left).trans
      (system.left_eq (pairOf position)).symm
  · right
    exact (congrArg system.configuration.siteAt right).trans
      (system.right_eq (pairOf position)).symm

end CCL.Riemann.BranchCuts
