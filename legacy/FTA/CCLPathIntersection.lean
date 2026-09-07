import FTA.ProjectivePath
import FTA.BoxGeometry

/-!
# Finite box tests for projective CCL boundary arcs

A projective path point is a quotient of two Gaussian polynomials.  After the
denominator is known to be nonzero, membership in a rational box is equivalent
to four signs of explicitly computed rational polynomials.  These are the
finite univariate sign conditions sent to the Sturm event decomposition in
Section 10.1.
-/

namespace FTA
namespace CCLPathIntersection

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.ProjectivePath
open FTA.RationalPolynomialBounds

abbrev QI := CCL.GaussianRat
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

def numeratorReal (path : Path) : RatPolynomial := realPart path.numerator
def numeratorImag (path : Path) : RatPolynomial := imagPart path.numerator
def denominatorReal (path : Path) : RatPolynomial := realPart path.denominator
def denominatorImag (path : Path) : RatPolynomial := imagPart path.denominator

@[simp] theorem eval_numeratorReal (path : Path) (t : ℚ) :
    (numeratorReal path).eval t =
      (path.numerator.eval (PathPolynomial.ofRat t)).re := by
  rw [numeratorReal, eval_realPart]

@[simp] theorem eval_numeratorImag (path : Path) (t : ℚ) :
    (numeratorImag path).eval t =
      (path.numerator.eval (PathPolynomial.ofRat t)).im := by
  rw [numeratorImag, eval_imagPart]

@[simp] theorem eval_denominatorReal (path : Path) (t : ℚ) :
    (denominatorReal path).eval t =
      (path.denominator.eval (PathPolynomial.ofRat t)).re := by
  rw [denominatorReal, eval_realPart]

@[simp] theorem eval_denominatorImag (path : Path) (t : ℚ) :
    (denominatorImag path).eval t =
      (path.denominator.eval (PathPolynomial.ofRat t)).im := by
  rw [denominatorImag, eval_imagPart]

/-- Cleared real numerator `Re(P * conj Q)`. -/
def affineRealNumerator (path : Path) : RatPolynomial :=
  numeratorReal path * denominatorReal path +
    numeratorImag path * denominatorImag path

/-- Cleared imaginary numerator `Im(P * conj Q)`. -/
def affineImagNumerator (path : Path) : RatPolynomial :=
  numeratorImag path * denominatorReal path -
    numeratorReal path * denominatorImag path

/-- Positive affine denominator `N(Q)` away from projective poles. -/
def denominatorNorm (path : Path) : RatPolynomial :=
  denominatorReal path * denominatorReal path +
    denominatorImag path * denominatorImag path

@[simp] theorem eval_affineRealNumerator (path : Path) (t : ℚ) :
    (affineRealNumerator path).eval t =
      (path.numerator.eval (PathPolynomial.ofRat t) *
        conj (path.denominator.eval (PathPolynomial.ofRat t))).re := by
  simp [affineRealNumerator, mul_re, conj]

@[simp] theorem eval_affineImagNumerator (path : Path) (t : ℚ) :
    (affineImagNumerator path).eval t =
      (path.numerator.eval (PathPolynomial.ofRat t) *
        conj (path.denominator.eval (PathPolynomial.ofRat t))).im := by
  simp [affineImagNumerator, mul_im, conj]
  ring

@[simp] theorem eval_denominatorNorm (path : Path) (t : ℚ) :
    (denominatorNorm path).eval t =
      normSq (path.denominator.eval (PathPolynomial.ofRat t)) := by
  simp [denominatorNorm, normSq]
  ring

theorem eval_denominatorNorm_pos (path : Path) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    0 < (denominatorNorm path).eval t := by
  rw [eval_denominatorNorm]
  exact normSq_pos hden

/-- One explicitly non-pole parameter certifies that the rational
denominator-norm polynomial is not identically zero. -/
theorem denominatorNorm_isZero_false_of_eval_ne
    (path : Path) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (denominatorNorm path).isZero = false :=
  DensePolynomial.isZero_false_of_eval_ne
    (eval_denominatorNorm_pos path t hden).ne'

theorem path_value_re (path : Path) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (path.value t).re =
      (affineRealNumerator path).eval t / (denominatorNorm path).eval t := by
  rw [eval_affineRealNumerator, eval_denominatorNorm]
  have hnorm : normSq
      (path.denominator.eval (PathPolynomial.ofRat t)) ≠ 0 :=
    (normSq_pos hden).ne'
  simp only [Path.value, mul_re, inv, conj]
  field_simp [hnorm]

theorem path_value_im (path : Path) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (path.value t).im =
      (affineImagNumerator path).eval t / (denominatorNorm path).eval t := by
  rw [eval_affineImagNumerator, eval_denominatorNorm]
  have hnorm : normSq
      (path.denominator.eval (PathPolynomial.ofRat t)) ≠ 0 :=
    (normSq_pos hden).ne'
  simp only [Path.value, mul_im, inv, conj]
  field_simp [hnorm]

/-- The four rational polynomials whose nonnegative signs say that the affine
path point lies in the displayed closed box. -/
structure BoxConditions where
  xLower : RatPolynomial
  xUpper : RatPolynomial
  yLower : RatPolynomial
  yUpper : RatPolynomial
deriving DecidableEq, Repr

def boxConditions (path : Path) (box : CCL.RatBox) : BoxConditions where
  xLower := affineRealNumerator path -
    DensePolynomial.scale box.xLower (denominatorNorm path)
  xUpper := DensePolynomial.scale box.xUpper (denominatorNorm path) -
    affineRealNumerator path
  yLower := affineImagNumerator path -
    DensePolynomial.scale box.yLower (denominatorNorm path)
  yUpper := DensePolynomial.scale box.yUpper (denominatorNorm path) -
    affineImagNumerator path

def BoxConditions.HoldsAt (conditions : BoxConditions) (t : ℚ) : Prop :=
  0 ≤ conditions.xLower.eval t ∧ 0 ≤ conditions.xUpper.eval t ∧
    0 ≤ conditions.yLower.eval t ∧ 0 ≤ conditions.yUpper.eval t

theorem eval_boxConditions_xLower
    (path : Path) (box : CCL.RatBox) (t : ℚ)
    (denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (boxConditions path box).xLower.eval t =
      (denominatorNorm path).eval t *
        ((path.value t).re - box.xLower) := by
  rw [path_value_re path t denominatorNonzero]
  have normNonzero := (eval_denominatorNorm_pos path t denominatorNonzero).ne'
  simp only [boxConditions, eval_sub, eval_scale]
  field_simp

theorem eval_boxConditions_xUpper
    (path : Path) (box : CCL.RatBox) (t : ℚ)
    (denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (boxConditions path box).xUpper.eval t =
      (denominatorNorm path).eval t *
        (box.xUpper - (path.value t).re) := by
  rw [path_value_re path t denominatorNonzero]
  have normNonzero := (eval_denominatorNorm_pos path t denominatorNonzero).ne'
  simp only [boxConditions, eval_sub, eval_scale]
  field_simp

theorem eval_boxConditions_yLower
    (path : Path) (box : CCL.RatBox) (t : ℚ)
    (denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (boxConditions path box).yLower.eval t =
      (denominatorNorm path).eval t *
        ((path.value t).im - box.yLower) := by
  rw [path_value_im path t denominatorNonzero]
  have normNonzero := (eval_denominatorNorm_pos path t denominatorNonzero).ne'
  simp only [boxConditions, eval_sub, eval_scale]
  field_simp

theorem eval_boxConditions_yUpper
    (path : Path) (box : CCL.RatBox) (t : ℚ)
    (denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    (boxConditions path box).yUpper.eval t =
      (denominatorNorm path).eval t *
        (box.yUpper - (path.value t).im) := by
  rw [path_value_im path t denominatorNonzero]
  have normNonzero := (eval_denominatorNorm_pos path t denominatorNonzero).ne'
  simp only [boxConditions, eval_sub, eval_scale]
  field_simp

/-- Executable exact evaluator for the four closed-box sign tests. -/
def BoxConditions.check (conditions : BoxConditions) (t : ℚ) : Bool :=
  decide (0 ≤ conditions.xLower.eval t) &&
    decide (0 ≤ conditions.xUpper.eval t) &&
    decide (0 ≤ conditions.yLower.eval t) &&
    decide (0 ≤ conditions.yUpper.eval t)

theorem BoxConditions.check_eq_true_iff
    (conditions : BoxConditions) (t : ℚ) :
    conditions.check t = true ↔ conditions.HoldsAt t := by
  simp [BoxConditions.check, BoxConditions.HoldsAt]
  tauto

theorem contains_value_iff_holdsAt (path : Path) (box : CCL.RatBox) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    box.Contains (path.value t) ↔ (boxConditions path box).HoldsAt t := by
  have hre := path_value_re path t hden
  have him := path_value_im path t hden
  have hnorm := eval_denominatorNorm_pos path t hden
  dsimp only [CCL.RatBox.Contains]
  rw [hre, him]
  simp only [BoxConditions.HoldsAt, boxConditions, eval_sub, eval_scale,
    sub_nonneg]
  rw [le_div_iff₀ hnorm, div_le_iff₀ hnorm, le_div_iff₀ hnorm,
    div_le_iff₀ hnorm]

theorem contains_value_iff_check (path : Path) (box : CCL.RatBox) (t : ℚ)
    (hden : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    box.Contains (path.value t) ↔ (boxConditions path box).check t = true := by
  rw [contains_value_iff_holdsAt path box t hden]
  exact (BoxConditions.check_eq_true_iff (boxConditions path box) t).symm

/-! ## Whole parameter-cell classification -/

/-- Four finite Lipschitz certificates proving that none of the box-boundary
sign polynomials changes sign on one rational parameter cell. -/
structure StableCell (conditions : BoxConditions) (interval : RationalInterval) where
  xLower : IntervalSignCertificate conditions.xLower interval.lower interval.upper
  xUpper : IntervalSignCertificate conditions.xUpper interval.lower interval.upper
  yLower : IntervalSignCertificate conditions.yLower interval.lower interval.upper
  yUpper : IntervalSignCertificate conditions.yUpper interval.lower interval.upper

/-- Exact midpoint classifier for a proposed parameter cell.  Returning
`none` requests another finite central-third refinement; returning `some`
carries all four whole-cell sign proofs. -/
def stableCell? (conditions : BoxConditions) (interval : RationalInterval)
    (proper : interval.Proper) : Option (StableCell conditions interval) :=
  match midpointSignCertificate? conditions.xLower interval.lower interval.upper
      proper with
  | none => none
  | some xLower =>
      match midpointSignCertificate? conditions.xUpper interval.lower interval.upper
          proper with
      | none => none
      | some xUpper =>
          match midpointSignCertificate? conditions.yLower interval.lower interval.upper
              proper with
          | none => none
          | some yLower =>
              match midpointSignCertificate? conditions.yUpper interval.lower
                  interval.upper proper with
              | none => none
              | some yUpper => some { xLower, xUpper, yLower, yUpper }

private theorem nonneg_iff_of_mul_pos {a b : ℚ} (h : 0 < a * b) :
    0 ≤ a ↔ 0 ≤ b := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨fun _ => hb.le, fun _ => ha.le⟩
  · constructor <;> intro hnonneg <;> linarith

theorem StableCell.holdsAt_iff
    {conditions : BoxConditions} {interval : RationalInterval}
    (cell : StableCell conditions interval) {s t : ℚ}
    (hsLower : interval.lower ≤ s) (hsUpper : s ≤ interval.upper)
    (htLower : interval.lower ≤ t) (htUpper : t ≤ interval.upper) :
    conditions.HoldsAt s ↔ conditions.HoldsAt t := by
  have hxLower := nonneg_iff_of_mul_pos
    (cell.xLower.eval_mul_pos_between hsLower hsUpper htLower htUpper)
  have hxUpper := nonneg_iff_of_mul_pos
    (cell.xUpper.eval_mul_pos_between hsLower hsUpper htLower htUpper)
  have hyLower := nonneg_iff_of_mul_pos
    (cell.yLower.eval_mul_pos_between hsLower hsUpper htLower htUpper)
  have hyUpper := nonneg_iff_of_mul_pos
    (cell.yUpper.eval_mul_pos_between hsLower hsUpper htLower htUpper)
  exact and_congr hxLower (and_congr hxUpper (and_congr hyLower hyUpper))

theorem StableCell.check_eq_true_iff
    {conditions : BoxConditions} {interval : RationalInterval}
    (cell : StableCell conditions interval) {s t : ℚ}
    (hsLower : interval.lower ≤ s) (hsUpper : s ≤ interval.upper)
    (htLower : interval.lower ≤ t) (htUpper : t ≤ interval.upper) :
    conditions.check s = true ↔ conditions.check t = true := by
  rw [BoxConditions.check_eq_true_iff, BoxConditions.check_eq_true_iff]
  exact cell.holdsAt_iff hsLower hsUpper htLower htUpper

/-- On a successfully classified parameter cell, one exact sample decides
whether every affine path point in the cell lies in the box or every one lies
outside it. -/
theorem StableCell.contains_value_iff
    (path : Path) (box : CCL.RatBox) {interval : RationalInterval}
    (cell : StableCell (boxConditions path box) interval) {s t : ℚ}
    (hsLower : interval.lower ≤ s) (hsUpper : s ≤ interval.upper)
    (htLower : interval.lower ≤ t) (htUpper : t ≤ interval.upper)
    (hsDen : path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (htDen : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    box.Contains (path.value s) ↔ box.Contains (path.value t) := by
  rw [contains_value_iff_holdsAt path box s hsDen,
    contains_value_iff_holdsAt path box t htDen]
  exact cell.holdsAt_iff hsLower hsUpper htLower htUpper

end CCLPathIntersection
end FTA
