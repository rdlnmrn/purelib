import mathlib.RFAP.ConstructiveFraction
import mathlib.RFAP.CanonicalGaussian

/-!
# Compatibility facade for canonical Gaussian rationals

The established `RFAP.ConstructiveGaussian` namespace now denotes the
quotient-free structural pair from `CanonicalGaussian`.  The wrappers below
retain the public calculation API while keeping the legacy quotient-valued
implementation outside the active dependency graph.
-/

namespace RFAP.ConstructiveGaussian

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.CanonicalGaussian.Gaussian

namespace Gaussian

/-- Compatibility names for the structural coordinate projections. -/
abbrev re : Gaussian → Coordinate := RFAP.CanonicalGaussian.Gaussian.re
abbrev im : Gaussian → Coordinate := RFAP.CanonicalGaussian.Gaussian.im

@[ext] theorem ext {left right : Gaussian}
    (real : left.re = right.re) (imaginary : left.im = right.im) :
    left = right :=
  RFAP.CanonicalGaussian.Gaussian.ext real imaginary

@[simp] theorem zero_re : (0 : Gaussian).re = 0 := rfl
@[simp] theorem zero_im : (0 : Gaussian).im = 0 := rfl
@[simp] theorem one_re : (1 : Gaussian).re = 1 := rfl
@[simp] theorem one_im : (1 : Gaussian).im = 0 := rfl
@[simp] theorem add_re (left right : Gaussian) :
    (left + right).re = left.re + right.re := rfl
@[simp] theorem add_im (left right : Gaussian) :
    (left + right).im = left.im + right.im := rfl
@[simp] theorem sub_re (left right : Gaussian) :
    (left - right).re = left.re - right.re := rfl
@[simp] theorem sub_im (left right : Gaussian) :
    (left - right).im = left.im - right.im := rfl
@[simp] theorem neg_re (source : Gaussian) : (-source).re = -source.re := rfl
@[simp] theorem neg_im (source : Gaussian) : (-source).im = -source.im := rfl
@[simp] theorem mul_re (left right : Gaussian) :
    (left * right).re = left.re * right.re - left.im * right.im := rfl
@[simp] theorem mul_im (left right : Gaussian) :
    (left * right).im = left.re * right.im + left.im * right.re := rfl

theorem add_assoc (first second third : Gaussian) :
    first + second + third = first + (second + third) :=
  RFAP.CanonicalGaussian.Gaussian.add_assoc first second third

theorem add_comm (left right : Gaussian) : left + right = right + left :=
  RFAP.CanonicalGaussian.Gaussian.add_comm left right

theorem sub_eq_add_neg (left right : Gaussian) :
    left - right = left + -right :=
  RFAP.CanonicalGaussian.Gaussian.sub_eq_add_neg left right

@[simp] theorem zero_add (source : Gaussian) : 0 + source = source :=
  RFAP.CanonicalGaussian.Gaussian.zero_add source

@[simp] theorem add_zero (source : Gaussian) : source + 0 = source :=
  _root_.add_zero source

@[simp] theorem zero_sub (source : Gaussian) : 0 - source = -source := by
  rw [sub_eq_add_neg, zero_add]

@[simp] theorem sub_zero (source : Gaussian) : source - 0 = source :=
  _root_.sub_zero source

@[simp] theorem sub_self (source : Gaussian) : source - source = 0 :=
  _root_.sub_self source

@[simp] theorem one_mul (source : Gaussian) : 1 * source = source :=
  RFAP.CanonicalGaussian.Gaussian.one_mul source

@[simp] theorem mul_one (source : Gaussian) : source * 1 = source :=
  _root_.mul_one source

@[simp] theorem zero_mul (source : Gaussian) : 0 * source = 0 := by
  apply ext
  · change (0 : Coordinate) * source.re - 0 * source.im = 0
    rw [RFAP.ConstructiveFraction.zero_mul_direct,
      RFAP.ConstructiveFraction.zero_mul_direct,
      RFAP.ConstructiveFraction.sub_eq_add_neg_direct, neg_zero,
      RFAP.ConstructiveFraction.zero_add]
  · change (0 : Coordinate) * source.im + 0 * source.re = 0
    rw [RFAP.ConstructiveFraction.zero_mul_direct,
      RFAP.ConstructiveFraction.zero_mul_direct,
      RFAP.ConstructiveFraction.zero_add]

@[simp] theorem mul_zero (source : Gaussian) : source * 0 = 0 := by
  rw [mul_comm]
  exact zero_mul source

theorem mul_comm (left right : Gaussian) : left * right = right * left :=
  RFAP.CanonicalGaussian.Gaussian.mul_comm left right

theorem mul_assoc (first second third : Gaussian) :
    first * second * third = first * (second * third) :=
  RFAP.CanonicalGaussian.Gaussian.mul_assoc first second third

theorem left_distrib (first second third : Gaussian) :
    first * (second + third) = first * second + first * third :=
  RFAP.CanonicalGaussian.Gaussian.left_distrib first second third

theorem right_distrib (first second third : Gaussian) :
    (first + second) * third = first * third + second * third :=
  _root_.add_mul first second third

def conj (source : Gaussian) : Gaussian := ⟨source.re, -source.im⟩

@[simp] theorem conj_zero : conj (0 : Gaussian) = 0 := rfl

@[simp] theorem conj_add (left right : Gaussian) :
    conj (left + right) = conj left + conj right :=
  RFAP.CanonicalGaussian.Gaussian.conj_add left right

@[simp] theorem conj_mul (left right : Gaussian) :
    conj (left * right) = conj left * conj right :=
  RFAP.CanonicalGaussian.Gaussian.conj_mul left right

@[simp] theorem conj_conj (source : Gaussian) : conj (conj source) = source :=
  RFAP.CanonicalGaussian.Gaussian.conj_conj source

/-- Squared Gaussian norm in the established power notation. -/
def normSq (source : Gaussian) : Coordinate :=
  source.re ^ 2 + source.im ^ 2

theorem normSq_eq_canonical (source : Gaussian) :
    normSq source = RFAP.CanonicalGaussian.Gaussian.normSq source := by
  simp only [normSq, RFAP.CanonicalGaussian.Gaussian.normSq, pow_two]

@[simp] theorem normSq_zero : normSq 0 = 0 :=
  by simp only [normSq_eq_canonical,
    RFAP.CanonicalGaussian.Gaussian.normSq_zero]

@[simp] theorem normSq_one : normSq 1 = 1 :=
  by simp only [normSq_eq_canonical,
    RFAP.CanonicalGaussian.Gaussian.normSq_one]

@[simp] theorem normSq_neg (source : Gaussian) : normSq (-source) = normSq source :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_neg source

@[simp] theorem normSq_conj (source : Gaussian) :
    normSq (conj source) = normSq source := by
  change source.re ^ 2 + (-source.im) ^ 2 =
    source.re ^ 2 + source.im ^ 2
  rw [neg_sq]

theorem normSq_nonneg (source : Gaussian) : 0 ≤ normSq source :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_nonneg source

theorem normSq_eq_zero {source : Gaussian} :
    normSq source = 0 ↔ source = 0 :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_eq_zero source

theorem normSq_pos {source : Gaussian} (nonzero : source ≠ 0) :
    0 < normSq source := by
  have nonnegative := normSq_nonneg source
  exact ⟨nonnegative, fun reverse => nonzero
    (normSq_eq_zero.mp
      (RFAP.CanonicalFraction.le_antisymm _ _ reverse nonnegative))⟩

theorem normSq_mul (left right : Gaussian) :
    normSq (left * right) = normSq left * normSq right :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_mul left right

private theorem add_sq_le_two_squares (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  have differenceNonnegative :
      0 ≤ left ^ 2 - 2 * left * right + right ^ 2 := by
    rw [← sub_sq]
    exact RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)
  have crossTermBound :
      2 * left * right ≤ left ^ 2 + right ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ left ^ 2 - 2 * left * right + right ^ 2 :=
        differenceNonnegative
      _ = left ^ 2 + right ^ 2 - 2 * left * right := by
        rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
          RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
        simp only [RFAP.ConstructiveFraction.add_assoc,
          RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm]
  rw [add_sq]
  calc
    left ^ 2 + 2 * left * right + right ^ 2 =
        2 * left * right + (left ^ 2 + right ^ 2) := by
      simp only [RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm]
    _ ≤ (left ^ 2 + right ^ 2) + (left ^ 2 + right ^ 2) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct crossTermBound _
    _ = 2 * (left ^ 2 + right ^ 2) := (two_mul _).symm

private theorem sub_sq_le_two_squares (left right : Coordinate) :
    (left - right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
  calc
    (left + -right) ^ 2 ≤ 2 * (left ^ 2 + (-right) ^ 2) :=
      add_sq_le_two_squares left (-right)
    _ = 2 * (left ^ 2 + right ^ 2) := by rw [neg_sq]

theorem normSq_add_le_two (left right : Gaussian) :
    normSq (left + right) ≤ 2 * (normSq left + normSq right) := by
  simp only [normSq, add_re, add_im]
  calc
    (left.re + right.re) ^ 2 + (left.im + right.im) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) +
          2 * (left.im ^ 2 + right.im ^ 2) :=
      RFAP.ConstructiveFraction.add_le_add_direct
        (add_sq_le_two_squares left.re right.re)
        (add_sq_le_two_squares left.im right.im)
    _ = 2 * ((left.re ^ 2 + left.im ^ 2) +
        (right.re ^ 2 + right.im ^ 2)) := by
      simp only [two_mul]
      simp only [RFAP.ConstructiveFraction.add_assoc,
        RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm]

theorem normSq_sub_le_two (left right : Gaussian) :
    normSq (left - right) ≤ 2 * (normSq left + normSq right) := by
  simp only [normSq, sub_re, sub_im]
  calc
    (left.re - right.re) ^ 2 + (left.im - right.im) ^ 2 ≤
        2 * (left.re ^ 2 + right.re ^ 2) +
          2 * (left.im ^ 2 + right.im ^ 2) :=
      RFAP.ConstructiveFraction.add_le_add_direct
        (sub_sq_le_two_squares left.re right.re)
        (sub_sq_le_two_squares left.im right.im)
    _ = 2 * ((left.re ^ 2 + left.im ^ 2) +
        (right.re ^ 2 + right.im ^ 2)) := by
      simp only [two_mul]
      simp only [RFAP.ConstructiveFraction.add_assoc,
        RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm]

private theorem coordinate_sub_via
    (left middle right : Coordinate) :
    left - right = (left - middle) + (middle - right) := by
  rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
    RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
    RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
  symm
  calc
    (left + -middle) + (middle + -right) =
        left + (-middle + (middle + -right)) :=
      RFAP.ConstructiveFraction.add_assoc _ _ _
    _ = left + ((-middle + middle) + -right) := by
      rw [RFAP.ConstructiveFraction.add_assoc]
    _ = left + (0 + -right) := by rw [neg_add_cancel]
    _ = left + -right := by rw [RFAP.ConstructiveFraction.zero_add]

private theorem coordinate_sub_add_cancel (left right : Coordinate) :
    left - right + right = left := by
  rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
    RFAP.ConstructiveFraction.add_assoc, neg_add_cancel,
    _root_.add_zero]

/-- Square-root-free two-leg path bound through one displayed intermediate
Gaussian rational. -/
theorem normSq_sub_le_via (left middle right : Gaussian) :
    normSq (left - right) ≤
      2 * (normSq (left - middle) + normSq (middle - right)) := by
  have identity : left - right =
      (left - middle) + (middle - right) := by
    apply ext
    · exact coordinate_sub_via left.re middle.re right.re
    · exact coordinate_sub_via left.im middle.im right.im
  rw [identity]
  exact normSq_add_le_two _ _

theorem half_normSq_sub_le_normSq_sub (left right : Gaussian) :
    normSq left / 2 - normSq right ≤ normSq (left - right) := by
  have bound := normSq_add_le_two (left - right) right
  have reconstruction : left - right + right = left := by
    apply ext
    · exact coordinate_sub_add_cancel left.re right.re
    · exact coordinate_sub_add_cancel left.im right.im
  rw [reconstruction] at bound
  have quotientBound :
      normSq left / 2 ≤ normSq (left - right) + normSq right := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 2) (by decide))).mpr
    calc
      normSq left ≤ 2 * (normSq (left - right) + normSq right) := bound
      _ = (normSq (left - right) + normSq right) * 2 :=
        RFAP.ConstructiveFraction.mul_comm _ _
  have translated := RFAP.ConstructiveFraction.add_le_add_right_direct
    quotientBound (-normSq right)
  calc
    normSq left / 2 - normSq right =
        normSq left / 2 + -normSq right :=
      RFAP.ConstructiveFraction.sub_eq_add_neg_direct _ _
    _ ≤ (normSq (left - right) + normSq right) + -normSq right := translated
    _ = normSq (left - right) := by
      rw [RFAP.ConstructiveFraction.add_assoc, add_neg_cancel,
        _root_.add_zero]

private theorem twice_self_mul_sum (left right : Coordinate) :
    2 * (left * (left + right)) =
      left ^ 2 - right ^ 2 + (left + right) ^ 2 := by
  rw [add_sq, RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
  simp only [pow_two, two_mul, _root_.mul_add, _root_.add_mul,
    RFAP.ConstructiveFraction.add_assoc,
    RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm,
    add_neg_cancel, _root_.add_zero]

/-- A positive displayed gap between two squared norms gives a
square-root-free lower bound for the squared norm of their sum. -/
theorem normSq_add_lower_of_gap
    {left right : Gaussian} {margin : Coordinate}
    (marginPositive : 0 < margin)
    (gap : margin ≤ normSq left - normSq right) :
    margin ^ 2 / (4 * normSq left) ≤ normSq (left + right) := by
  let sum := left + right
  let product := conj left * sum
  let dot := product.re
  have leftNormPositive : 0 < normSq left := by
    have gapLeNorm : margin ≤ normSq left :=
      gap.trans (sub_le_self _ (normSq_nonneg right))
    exact marginPositive.trans_le gapLeNorm
  have fourPositive : (0 : Coordinate) < 4 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide)
  have denominatorPositive : 0 < 4 * normSq left :=
    RFAP.ConstructiveFraction.mul_pos_direct fourPositive leftNormPositive
  have sumNormNonnegative : 0 ≤ normSq sum := normSq_nonneg sum
  have doubledDot : 2 * dot =
      (normSq left - normSq right) + normSq sum := by
    have productReal :
        dot = left.re * sum.re + left.im * sum.im := by
      dsimp only [dot, product]
      change left.re * sum.re - (-left.im) * sum.im =
        left.re * sum.re + left.im * sum.im
      simp only [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
        _root_.neg_mul, neg_neg]
    rw [productReal]
    dsimp only [sum]
    simp only [normSq, add_re, add_im]
    rw [_root_.mul_add]
    rw [twice_self_mul_sum left.re right.re,
      twice_self_mul_sum left.im right.im]
    rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
      RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
      RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
    simp only [_root_.neg_add_rev, RFAP.ConstructiveFraction.add_assoc,
      RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm]
  have marginLeDoubledDot : margin ≤ 2 * dot := by
    rw [doubledDot]
    exact gap.trans (le_add_of_nonneg_right sumNormNonnegative)
  have squaredMargin : margin ^ 2 ≤ (2 * dot) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct marginPositive.le
      marginLeDoubledDot 2
  have dotCauchy : dot ^ 2 ≤ normSq left * normSq sum := by
    calc
      dot ^ 2 ≤ dot ^ 2 + product.im ^ 2 :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct product.im)
      _ = normSq product := by rfl
      _ = normSq (conj left) * normSq sum := normSq_mul _ _
      _ = normSq left * normSq sum := by rw [normSq_conj]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    denominatorPositive).2
  rw [RFAP.ConstructiveFraction.mul_comm (normSq sum)]
  calc
    margin ^ 2 ≤ (2 * dot) ^ 2 := squaredMargin
    _ = 4 * dot ^ 2 := by
      rw [mul_pow]
      have twoSquared : (2 : Coordinate) ^ 2 = 4 := by decide
      rw [twoSquared]
    _ ≤ 4 * (normSq left * normSq sum) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        dotCauchy fourPositive.le
    _ = (4 * normSq left) * normSq sum :=
      (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm

/-- Square-root-free Cauchy--Schwarz for one displayed rational projection.
The left side is the square of the ordinary real dot product. -/
theorem projection_sq_le_normSq_mul (direction sample : Gaussian) :
    (direction.re * sample.re + direction.im * sample.im) ^ 2 <=
      normSq direction * normSq sample := by
  let product := conj direction * sample
  have productReal :
      product.re = direction.re * sample.re + direction.im * sample.im := by
    simp only [product, conj, mul_re]
    ring1
  calc
    (direction.re * sample.re + direction.im * sample.im) ^ 2 =
        product.re ^ 2 := by rw [productReal]
    _ <= product.re ^ 2 + product.im ^ 2 :=
      le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct product.im)
    _ = normSq product := rfl
    _ = normSq direction * normSq sample := by
      dsimp only [product]
      rw [normSq_mul, normSq_conj]

/-- Canonical Gaussian values already contain canonical coordinates. -/
def canonical (source : Gaussian) : Gaussian := source

theorem canonical_eq (source : Gaussian) : canonical source = source := rfl

def inv (source : Gaussian) : Gaussian :=
  ⟨source.re / normSq source, -source.im / normSq source⟩

@[simp] theorem inv_eq (source : Gaussian) : source⁻¹ = inv source := by
  change RFAP.CanonicalGaussian.Gaussian.inv source = inv source
  apply ext
  · change source.re / RFAP.CanonicalGaussian.Gaussian.normSq source =
      source.re / normSq source
    rw [normSq_eq_canonical]
  · change -source.im / RFAP.CanonicalGaussian.Gaussian.normSq source =
      -source.im / normSq source
    rw [normSq_eq_canonical]

@[simp] theorem inv_zero : inv 0 = 0 := by
  decide

@[simp] theorem inv_one_direct : inv 1 = 1 := by decide

theorem mul_inv (source : Gaussian) (nonzero : source ≠ 0) :
    source * inv source = 1 := by
  rw [← inv_eq]
  exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel source nonzero

theorem inv_mul (source : Gaussian) (nonzero : source ≠ 0) :
    inv source * source = 1 := by
  rw [mul_comm]
  exact mul_inv source nonzero

theorem mul_right_cancel_of_ne {left right factor : Gaussian}
    (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right :=
  RFAP.CanonicalGaussian.Gaussian.mul_right_cancel_of_nonzero
    factorNonzero productsEqual

theorem mul_ne_zero_direct {left right : Gaussian}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 :=
  RFAP.CanonicalGaussian.Gaussian.mul_ne_zero leftNonzero rightNonzero

theorem inv_ne_zero_direct {source : Gaussian} (nonzero : source ≠ 0) :
    source⁻¹ ≠ 0 :=
  RFAP.CanonicalGaussian.Gaussian.inv_ne_zero nonzero

theorem neg_ne_zero_direct {source : Gaussian} (nonzero : source ≠ 0) :
    -source ≠ 0 := neg_ne_zero.mpr nonzero

theorem inv_neg_direct (source : Gaussian) : inv (-source) = -inv source :=
  by rw [← inv_eq, ← inv_eq]
     exact RFAP.CanonicalGaussian.Gaussian.inv_neg source

theorem normSq_inv (source : Gaussian) (nonzero : source ≠ 0) :
    normSq (inv source) = (normSq source)⁻¹ := by
  rw [← inv_eq]
  simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_inv source nonzero

theorem normSq_div (left right : Gaussian) (rightNonzero : right ≠ 0) :
    normSq (left / right) = normSq left * (normSq right)⁻¹ :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_div left right rightNonzero

abbrev gamma := RFAP.CanonicalGaussian.Gaussian.gamma

@[simp] theorem normSq_gamma : normSq gamma = 2 :=
  by simpa only [normSq_eq_canonical] using
    RFAP.CanonicalGaussian.Gaussian.normSq_gamma

def natPow (source : Gaussian) : Nat → Gaussian
  | 0 => 1
  | exponent + 1 => natPow source exponent * source

@[simp] theorem natPow_zero (source : Gaussian) : natPow source 0 = 1 := rfl

@[simp] theorem natPow_succ (source : Gaussian) (exponent : Nat) :
    natPow source (exponent + 1) = natPow source exponent * source := rfl

theorem normSq_natPow (source : Gaussian) (exponent : Nat) :
    normSq (natPow source exponent) = normSq source ^ exponent := by
  induction exponent with
  | zero => exact normSq_one
  | succ exponent inductionHypothesis =>
      rw [natPow_succ, normSq_mul, inductionHypothesis, pow_succ]

theorem natPow_ne_zero_direct (source : Gaussian) (nonzero : source ≠ 0) :
    ∀ exponent : Nat, natPow source exponent ≠ 0
  | 0 => one_ne_zero
  | exponent + 1 =>
      mul_ne_zero_direct (natPow_ne_zero_direct source nonzero exponent) nonzero

theorem normSq_gamma_pow_mul (exponent : Nat) (source : Gaussian) :
    normSq (natPow gamma exponent * source) =
      (2 : Coordinate) ^ exponent * normSq source := by
  rw [normSq_mul, normSq_natPow, normSq_gamma]

@[simp] theorem natCast_re (value : Nat) :
    ((value : Gaussian).re) = (value : Coordinate) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, add_re, inductionHypothesis, one_re, Nat.cast_succ]

@[simp] theorem natCast_im (value : Nat) : ((value : Gaussian).im) = 0 := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, add_im, inductionHypothesis, one_im]
      exact RFAP.ConstructiveFraction.zero_add 0

theorem normSq_pow (source : Gaussian) (exponent : Nat) :
    normSq (source ^ exponent) = normSq source ^ exponent := by
  induction exponent with
  | zero => exact normSq_one
  | succ exponent inductionHypothesis =>
      rw [pow_succ, normSq_mul, inductionHypothesis, pow_succ]

theorem pow_ne_zero_direct (source : Gaussian) (nonzero : source ≠ 0) :
    ∀ exponent : Nat, source ^ exponent ≠ 0
  | 0 => one_ne_zero
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_ne_zero_direct (pow_ne_zero_direct source nonzero exponent)
        nonzero

end Gaussian

end RFAP.ConstructiveGaussian
