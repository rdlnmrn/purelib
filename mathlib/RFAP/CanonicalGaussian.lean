import mathlib.Tactic.QuotientFreeRing
import Mathlib.Algebra.Ring.MinimalAxioms
import mathlib.RFAP.CanonicalFractionSize

/-!
# Canonical Gaussian rationals

Gaussian values are structural pairs of quotient-free canonical rationals.
All operations remain finite component calculations.  In particular, the
proof that the norm denominator is nonzero inspects the signs of the stored
rational numerators; it does not embed the pair in a completed complex field.
-/

namespace RFAP.CanonicalFraction

/-- Weak positivity is exactly weak positivity of the stored numerator. -/
theorem zero_le_iff_num_nonneg (source : Rational) :
    0 ≤ source ↔ 0 ≤ source.num := by
  change (0 : Int) * (source.den : Int) ≤ source.num * 1 ↔ 0 ≤ source.num
  simp only [Int.zero_mul, Int.mul_one]

/-- A finite rational square is nonnegative in the concrete cross order. -/
theorem mul_self_nonneg (source : Rational) : 0 ≤ source * source := by
  rw [zero_le_iff_num_nonneg]
  by_cases sourceZero : source = 0
  · rw [sourceZero, zero_mul]
    rfl
  · have numeratorNonzero : source.num ≠ 0 := fun numeratorZero =>
      sourceZero ((eq_zero_iff_num_zero source).mpr numeratorZero)
    have rawPositive : 0 < (referenceMulRaw source source).num := by
      change 0 < source.num * source.num
      by_cases numeratorPositive : 0 < source.num
      · exact Int.mul_pos numeratorPositive numeratorPositive
      · have numeratorNegative : source.num < 0 :=
          lt_of_le_of_ne (Int.le_of_not_gt numeratorPositive)
            numeratorNonzero
        exact Int.mul_pos_of_neg_of_neg numeratorNegative numeratorNegative
    exact Int.le_of_lt
      ((numerator_pos_iff_of_equivalent (mul_equivalent source source)).mpr
        rawPositive)

/-- A finite rational square is zero exactly when its factor is zero. -/
theorem mul_self_eq_zero (source : Rational) :
    source * source = 0 ↔ source = 0 := by
  constructor
  · intro squareZero
    by_cases sourceZero : source = 0
    · exact sourceZero
    · exact (mul_ne_zero sourceZero sourceZero squareZero).elim
  · intro sourceZero
    rw [sourceZero, zero_mul]

end RFAP.CanonicalFraction

namespace RFAP.CanonicalGaussian

abbrev Coordinate := RFAP.CanonicalFraction.Rational

/-- A structural Gaussian pair `re + im i`. -/
@[ext]
structure Gaussian where
  re : Coordinate
  im : Coordinate
deriving DecidableEq

namespace Gaussian

/-- Subtraction on the canonical coordinate carrier was installed before its
ring structure, so expose its computational definition explicitly to the
small ring normalizer. -/
private theorem coordinate_sub_eq_add_neg (left right : Coordinate) :
    left - right = left + -right := rfl

private theorem coordinate_add_left_comm (first second third : Coordinate) :
    first + (second + third) = second + (first + third) := by
  calc
    first + (second + third) = (first + second) + third :=
      (RFAP.CanonicalFraction.add_assoc first second third).symm
    _ = (second + first) + third := by
      rw [RFAP.CanonicalFraction.add_comm first second]
    _ = second + (first + third) :=
      RFAP.CanonicalFraction.add_assoc second first third

private theorem coordinate_add_four_real
    (first second third fourth : Coordinate) :
    (first + second) + (third + fourth) =
      (first + fourth) + (second + third) := by
  calc
    (first + second) + (third + fourth) =
        first + (second + (third + fourth)) :=
      RFAP.CanonicalFraction.add_assoc first second (third + fourth)
    _ = first + (fourth + (second + third)) := by
      rw [← RFAP.CanonicalFraction.add_assoc second third fourth,
        RFAP.CanonicalFraction.add_comm (second + third) fourth]
    _ = (first + fourth) + (second + third) :=
      (RFAP.CanonicalFraction.add_assoc first fourth (second + third)).symm

private theorem coordinate_add_four_imaginary
    (first second third fourth : Coordinate) :
    (first + second) + (third + fourth) =
      (first + third) + (fourth + second) := by
  calc
    (first + second) + (third + fourth) =
        first + (second + (third + fourth)) :=
      RFAP.CanonicalFraction.add_assoc first second (third + fourth)
    _ = first + (third + (fourth + second)) := by
      rw [coordinate_add_left_comm second third fourth,
        RFAP.CanonicalFraction.add_comm second fourth]
    _ = (first + third) + (fourth + second) :=
      (RFAP.CanonicalFraction.add_assoc first third (fourth + second)).symm

instance : Zero Gaussian := ⟨⟨0, 0⟩⟩
instance : One Gaussian := ⟨⟨1, 0⟩⟩
instance : Add Gaussian :=
  ⟨fun left right => ⟨left.re + right.re, left.im + right.im⟩⟩
instance : Neg Gaussian := ⟨fun source => ⟨-source.re, -source.im⟩⟩
instance : Sub Gaussian :=
  ⟨fun left right => ⟨left.re - right.re, left.im - right.im⟩⟩
instance : Mul Gaussian :=
  ⟨fun left right =>
    ⟨left.re * right.re - left.im * right.im,
      left.re * right.im + left.im * right.re⟩⟩

@[simp] theorem zero_re : (0 : Gaussian).re = 0 := rfl
@[simp] theorem zero_im : (0 : Gaussian).im = 0 := rfl
@[simp] theorem one_re : (1 : Gaussian).re = 1 := rfl
@[simp] theorem one_im : (1 : Gaussian).im = 0 := rfl
@[simp] theorem add_re (left right : Gaussian) :
    (left + right).re = left.re + right.re := rfl
@[simp] theorem add_im (left right : Gaussian) :
    (left + right).im = left.im + right.im := rfl
@[simp] theorem neg_re (source : Gaussian) : (-source).re = -source.re := rfl
@[simp] theorem neg_im (source : Gaussian) : (-source).im = -source.im := rfl
@[simp] theorem sub_re (left right : Gaussian) :
    (left - right).re = left.re - right.re := rfl
@[simp] theorem sub_im (left right : Gaussian) :
    (left - right).im = left.im - right.im := rfl
@[simp] theorem mul_re (left right : Gaussian) :
    (left * right).re = left.re * right.re - left.im * right.im := rfl
@[simp] theorem mul_im (left right : Gaussian) :
    (left * right).im = left.re * right.im + left.im * right.re := rfl

theorem sub_eq_add_neg (left right : Gaussian) :
    left - right = left + -right := rfl

theorem add_assoc (first second third : Gaussian) :
    first + second + third = first + (second + third) := by
  apply Gaussian.ext <;> simp only [add_re, add_im] <;> ring1

theorem add_comm (left right : Gaussian) : left + right = right + left := by
  apply Gaussian.ext <;> simp only [add_re, add_im] <;> ring1

theorem zero_add (source : Gaussian) : 0 + source = source := by
  apply Gaussian.ext <;> change (0 : Coordinate) + _ = _ <;> ring1

theorem neg_add_cancel (source : Gaussian) : -source + source = 0 := by
  apply Gaussian.ext <;> change -(_ : Coordinate) + _ = 0 <;> ring1

theorem mul_assoc (first second third : Gaussian) :
    first * second * third = first * (second * third) := by
  apply Gaussian.ext
  · simp only [mul_re, mul_im, coordinate_sub_eq_add_neg, _root_.add_mul,
      _root_.mul_add, _root_.neg_mul, _root_.mul_neg,
      _root_.neg_add_rev, RFAP.CanonicalFraction.mul_assoc]
    exact coordinate_add_four_real
      (first.re * (second.re * third.re))
      (-(first.im * (second.im * third.re)))
      (-(first.im * (second.re * third.im)))
      (-(first.re * (second.im * third.im)))
  · simp only [mul_re, mul_im, coordinate_sub_eq_add_neg, _root_.add_mul,
      _root_.mul_add, _root_.neg_mul, _root_.mul_neg,
      RFAP.CanonicalFraction.mul_assoc]
    exact coordinate_add_four_imaginary
      (first.re * (second.re * third.im))
      (-(first.im * (second.im * third.im)))
      (first.re * (second.im * third.re))
      (first.im * (second.re * third.re))

theorem mul_comm (left right : Gaussian) : left * right = right * left := by
  apply Gaussian.ext <;>
    simp only [mul_re, mul_im, coordinate_sub_eq_add_neg] <;> ring1

theorem one_mul (source : Gaussian) : 1 * source = source := by
  apply Gaussian.ext
  · change (1 : Coordinate) * source.re - 0 * source.im = source.re
    rw [coordinate_sub_eq_add_neg]
    ring1
  · change (1 : Coordinate) * source.im + 0 * source.re = source.im
    ring1

theorem left_distrib (first second third : Gaussian) :
    first * (second + third) = first * second + first * third := by
  apply Gaussian.ext <;>
    simp only [mul_re, mul_im, add_re, add_im,
      coordinate_sub_eq_add_neg] <;> ring1

instance instCommRing : CommRing Gaussian :=
  { CommRing.ofMinimalAxioms
      add_assoc zero_add neg_add_cancel mul_assoc mul_comm one_mul left_distrib with
    sub := fun left right => ⟨left.re - right.re, left.im - right.im⟩
    sub_eq_add_neg := fun _ _ => rfl }

theorem sub_sub_right (base correction : Gaussian) :
    (base - correction) - base = -correction := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  have cancel : base + -base = 0 := by
    rw [add_comm base (-base)]
    exact neg_add_cancel base
  calc
    base + -correction + -base = base + (-correction + -base) :=
      add_assoc base (-correction) (-base)
    _ = base + (-base + -correction) := by
      rw [add_comm (-correction) (-base)]
    _ = (base + -base) + -correction :=
      (add_assoc base (-base) (-correction)).symm
    _ = 0 + -correction := by rw [cancel]
    _ = -correction := zero_add (-correction)

theorem zero_ne_one : (0 : Gaussian) ≠ 1 := by
  intro equal
  have realEqual := congrArg Gaussian.re equal
  exact RFAP.CanonicalFraction.zero_ne_one realEqual

instance : Nontrivial Gaussian := ⟨0, 1, zero_ne_one⟩

/-- Gaussian conjugation. -/
def conj (source : Gaussian) : Gaussian := ⟨source.re, -source.im⟩

@[simp] theorem conj_conj (source : Gaussian) : conj (conj source) = source := by
  apply Gaussian.ext
  · rfl
  · change -(-source.im) = source.im
    ring1

@[simp] theorem conj_add (left right : Gaussian) :
    conj (left + right) = conj left + conj right := by
  apply Gaussian.ext
  · rfl
  · change -(left.im + right.im) = -left.im + -right.im
    ring1

@[simp] theorem conj_mul (left right : Gaussian) :
    conj (left * right) = conj left * conj right := by
  apply Gaussian.ext
  · simp only [conj, mul_re, coordinate_sub_eq_add_neg, _root_.neg_mul,
      _root_.mul_neg, _root_.neg_neg]
  · simp only [conj, mul_im, _root_.neg_mul, _root_.mul_neg,
      _root_.neg_add_rev]
    exact RFAP.CanonicalFraction.add_comm _ _

/-- Squared Gaussian quadrance. -/
def normSq (source : Gaussian) : Coordinate :=
  source.re * source.re + source.im * source.im

@[simp] theorem normSq_zero : normSq 0 = 0 := by
  change (0 : Coordinate) * 0 + 0 * 0 = 0
  rw [zero_mul, RFAP.CanonicalFraction.zero_add]

@[simp] theorem normSq_one : normSq 1 = 1 := by
  change (1 : Coordinate) * 1 + 0 * 0 = 1
  rw [RFAP.CanonicalFraction.one_mul, zero_mul, _root_.add_zero]

@[simp] theorem normSq_neg (source : Gaussian) :
    normSq (-source) = normSq source := by
  change (-source.re) * (-source.re) + (-source.im) * (-source.im) =
    source.re * source.re + source.im * source.im
  rw [neg_mul_neg, neg_mul_neg]

theorem normSq_nonneg (source : Gaussian) : 0 ≤ normSq source := by
  rw [RFAP.CanonicalFraction.zero_le_iff_num_nonneg]
  let realSquare := source.re * source.re
  let imaginarySquare := source.im * source.im
  have realNonnegative : 0 ≤ realSquare :=
    RFAP.CanonicalFraction.mul_self_nonneg source.re
  have imaginaryNonnegative : 0 ≤ imaginarySquare :=
    RFAP.CanonicalFraction.mul_self_nonneg source.im
  have realNumeratorNonnegative : 0 ≤ realSquare.num :=
    (RFAP.CanonicalFraction.zero_le_iff_num_nonneg realSquare).mp
      realNonnegative
  have imaginaryNumeratorNonnegative : 0 ≤ imaginarySquare.num :=
    (RFAP.CanonicalFraction.zero_le_iff_num_nonneg imaginarySquare).mp
      imaginaryNonnegative
  have display := RFAP.CanonicalFraction.add_equivalent
    realSquare imaginarySquare
  have displayNumeratorNonnegative :
      0 ≤ (RFAP.CanonicalFraction.referenceAddRaw
        realSquare imaginarySquare).num := by
    change
      0 ≤ realSquare.num * (imaginarySquare.den : Int) +
        imaginarySquare.num * (realSquare.den : Int)
    exact Int.add_nonneg
      (Int.mul_nonneg realNumeratorNonnegative (Int.natCast_nonneg _))
      (Int.mul_nonneg imaginaryNumeratorNonnegative (Int.natCast_nonneg _))
  change 0 ≤ (realSquare + imaginarySquare).num
  by_cases sumNumeratorZero :
      (realSquare + imaginarySquare).num = 0
  · rw [sumNumeratorZero]
  · exact Int.le_of_lt
      ((RFAP.CanonicalFraction.numerator_pos_iff_of_equivalent display).mpr
        (lt_of_le_of_ne displayNumeratorNonnegative
          (fun displayZero => sumNumeratorZero
            ((RFAP.CanonicalFraction.numerator_zero_iff_of_equivalent display).mpr
              displayZero.symm))))

private theorem nonnegative_addends_of_zero
    {left right : Coordinate}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right)
    (sumZero : left + right = 0) : left = 0 ∧ right = 0 := by
  have sumNumeratorZero : (left + right).num = 0 :=
    (RFAP.CanonicalFraction.eq_zero_iff_num_zero (left + right)).mp sumZero
  have display := RFAP.CanonicalFraction.add_equivalent left right
  have rawNumeratorZero :
      (RFAP.CanonicalFraction.referenceAddRaw left right).num = 0 :=
    (RFAP.CanonicalFraction.numerator_zero_iff_of_equivalent display).mp
      sumNumeratorZero
  change
    left.num * (right.den : Int) + right.num * (left.den : Int) = 0
      at rawNumeratorZero
  have leftNumeratorNonnegative : 0 ≤ left.num :=
    (RFAP.CanonicalFraction.zero_le_iff_num_nonneg left).mp leftNonnegative
  have rightNumeratorNonnegative : 0 ≤ right.num :=
    (RFAP.CanonicalFraction.zero_le_iff_num_nonneg right).mp rightNonnegative
  have leftNumeratorZero : left.num = 0 := by
    by_cases leftNumeratorZero : left.num = 0
    · exact leftNumeratorZero
    · have leftNumeratorPositive : 0 < left.num :=
        lt_of_le_of_ne leftNumeratorNonnegative
          (fun zeroEqual => leftNumeratorZero zeroEqual.symm)
      have leftTermPositive :
          0 < left.num * (right.den : Int) :=
        Int.mul_pos leftNumeratorPositive (Int.natCast_pos.mpr right.den_pos)
      have rightTermNonnegative :
          0 ≤ right.num * (left.den : Int) :=
        Int.mul_nonneg rightNumeratorNonnegative (Int.natCast_nonneg _)
      have sumPositive :=
        Int.add_pos_of_pos_of_nonneg leftTermPositive rightTermNonnegative
      rw [rawNumeratorZero] at sumPositive
      exact (Int.lt_irrefl 0 sumPositive).elim
  have rightNumeratorZero : right.num = 0 := by
    by_cases rightNumeratorZero : right.num = 0
    · exact rightNumeratorZero
    · have rightNumeratorPositive : 0 < right.num :=
        lt_of_le_of_ne rightNumeratorNonnegative
          (fun zeroEqual => rightNumeratorZero zeroEqual.symm)
      have leftTermNonnegative :
          0 ≤ left.num * (right.den : Int) :=
        Int.mul_nonneg leftNumeratorNonnegative (Int.natCast_nonneg _)
      have rightTermPositive :
          0 < right.num * (left.den : Int) :=
        Int.mul_pos rightNumeratorPositive (Int.natCast_pos.mpr left.den_pos)
      have sumPositive :=
        Int.add_pos_of_nonneg_of_pos leftTermNonnegative rightTermPositive
      rw [rawNumeratorZero] at sumPositive
      exact (Int.lt_irrefl 0 sumPositive).elim
  exact
    ⟨(RFAP.CanonicalFraction.eq_zero_iff_num_zero left).mpr leftNumeratorZero,
      (RFAP.CanonicalFraction.eq_zero_iff_num_zero right).mpr
        rightNumeratorZero⟩

theorem normSq_eq_zero (source : Gaussian) : normSq source = 0 ↔ source = 0 := by
  constructor
  · intro normZero
    have squaresZero := nonnegative_addends_of_zero
      (RFAP.CanonicalFraction.mul_self_nonneg source.re)
      (RFAP.CanonicalFraction.mul_self_nonneg source.im) normZero
    have realZero :=
      (RFAP.CanonicalFraction.mul_self_eq_zero source.re).mp squaresZero.1
    have imaginaryZero :=
      (RFAP.CanonicalFraction.mul_self_eq_zero source.im).mp squaresZero.2
    exact Gaussian.ext realZero imaginaryZero
  · intro sourceZero
    rw [sourceZero]
    change (0 : Coordinate) * 0 + 0 * 0 = 0
    ring1

theorem mul_conj (source : Gaussian) :
    source * conj source = ⟨normSq source, 0⟩ := by
  apply Gaussian.ext
  · change source.re * source.re - source.im * (-source.im) =
      source.re * source.re + source.im * source.im
    simp only [coordinate_sub_eq_add_neg, _root_.mul_neg,
      _root_.neg_neg]
  · change source.re * (-source.im) + source.im * source.re = 0
    rw [_root_.mul_neg, RFAP.CanonicalFraction.mul_comm source.im source.re]
    exact RFAP.CanonicalFraction.neg_add_cancel (source.re * source.im)

theorem normSq_mul (left right : Gaussian) :
    normSq (left * right) = normSq left * normSq right := by
  have rearranged :
      (left * right) * (conj left * conj right) =
        (left * conj left) * (right * conj right) := by
    calc
      (left * right) * (conj left * conj right) =
          left * (right * (conj left * conj right)) :=
        mul_assoc left right (conj left * conj right)
      _ = left * ((right * conj left) * conj right) := by
        rw [← mul_assoc right (conj left) (conj right)]
      _ = left * ((conj left * right) * conj right) := by
        rw [mul_comm right (conj left)]
      _ = left * (conj left * (right * conj right)) := by
        rw [mul_assoc (conj left) right (conj right)]
      _ = (left * conj left) * (right * conj right) :=
        (mul_assoc left (conj left) (right * conj right)).symm
  calc
    normSq (left * right) = ((left * right) * conj (left * right)).re := by
      exact (congrArg Gaussian.re (mul_conj (left * right))).symm
    _ = ((left * right) * (conj left * conj right)).re := by
      rw [conj_mul]
    _ = ((left * conj left) * (right * conj right)).re := by
      rw [rearranged]
    _ = normSq left * normSq right := by
      rw [mul_conj left, mul_conj right]
      change normSq left * normSq right - (0 : Coordinate) * 0 =
        normSq left * normSq right
      rw [zero_mul, coordinate_sub_eq_add_neg, neg_zero, add_zero]

/-- Total Gaussian reciprocal, computed from conjugation and the rational
quadrance. -/
def inv (source : Gaussian) : Gaussian :=
  ⟨source.re / normSq source, -source.im / normSq source⟩

instance : Inv Gaussian := ⟨inv⟩
instance : Div Gaussian := ⟨fun left right => left * right⁻¹⟩

theorem mul_inv_cancel (source : Gaussian) (sourceNonzero : source ≠ 0) :
    source * source⁻¹ = 1 := by
  have normNonzero : normSq source ≠ 0 := fun normZero =>
    sourceNonzero ((normSq_eq_zero source).mp normZero)
  apply Gaussian.ext
  · change source.re * (source.re / normSq source) -
      source.im * (-source.im / normSq source) = 1
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    calc
      source.re * (source.re * (normSq source)⁻¹) -
            source.im * (-source.im * (normSq source)⁻¹) =
          normSq source * (normSq source)⁻¹ := by
        simp only [normSq, coordinate_sub_eq_add_neg, _root_.add_mul,
          _root_.neg_mul, _root_.mul_neg, _root_.neg_neg]
        exact congrArg₂ (fun left right : Coordinate => left + right)
          (RFAP.CanonicalFraction.mul_assoc source.re source.re
            (normSq source)⁻¹).symm
          (RFAP.CanonicalFraction.mul_assoc source.im source.im
            (normSq source)⁻¹).symm
      _ = 1 := RFAP.CanonicalFraction.mul_inv_cancel _ normNonzero
  · change source.re * (-source.im / normSq source) +
      source.im * (source.re / normSq source) = 0
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    simp only [_root_.neg_mul, _root_.mul_neg]
    have swapped :
        source.im * (source.re * (normSq source)⁻¹) =
          source.re * (source.im * (normSq source)⁻¹) := by
      calc
        source.im * (source.re * (normSq source)⁻¹) =
            (source.im * source.re) * (normSq source)⁻¹ :=
          (RFAP.CanonicalFraction.mul_assoc source.im source.re
            (normSq source)⁻¹).symm
        _ = (source.re * source.im) * (normSq source)⁻¹ := by
          rw [RFAP.CanonicalFraction.mul_comm source.im source.re]
        _ = source.re * (source.im * (normSq source)⁻¹) :=
          RFAP.CanonicalFraction.mul_assoc source.re source.im
            (normSq source)⁻¹
    rw [swapped]
    exact RFAP.CanonicalFraction.neg_add_cancel
      (source.re * (source.im * (normSq source)⁻¹))

theorem inv_mul_cancel (source : Gaussian) (sourceNonzero : source ≠ 0) :
    source⁻¹ * source = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel source sourceNonzero

theorem normSq_inv (source : Gaussian) (sourceNonzero : source ≠ 0) :
    normSq source⁻¹ = (normSq source)⁻¹ := by
  have normNonzero : normSq source ≠ 0 := fun normZero =>
    sourceNonzero ((normSq_eq_zero source).mp normZero)
  apply RFAP.CanonicalFraction.mul_left_cancel_of_nonzero normNonzero
  calc
    normSq source * normSq source⁻¹ = normSq (source * source⁻¹) :=
      (normSq_mul source source⁻¹).symm
    _ = normSq 1 := by rw [mul_inv_cancel source sourceNonzero]
    _ = 1 := normSq_one
    _ = normSq source * (normSq source)⁻¹ :=
      (RFAP.CanonicalFraction.mul_inv_cancel
        (normSq source) normNonzero).symm

theorem normSq_div (left right : Gaussian) (rightNonzero : right ≠ 0) :
    normSq (left / right) = normSq left * (normSq right)⁻¹ := by
  change normSq (left * right⁻¹) = _
  rw [normSq_mul, normSq_inv right rightNonzero]

theorem mul_right_cancel_of_nonzero {left right factor : Gaussian}
    (factorNonzero : factor ≠ 0) (equalProducts : left * factor = right * factor) :
    left = right := by
  have multiplied := congrArg (fun value => value * factor⁻¹) equalProducts
  simpa only [mul_assoc, mul_inv_cancel factor factorNonzero,
    _root_.mul_one] using multiplied

theorem mul_ne_zero {left right : Gaussian}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 := by
  intro productZero
  apply leftNonzero
  apply mul_right_cancel_of_nonzero rightNonzero
  rw [productZero, zero_mul]

theorem inv_ne_zero {source : Gaussian} (sourceNonzero : source ≠ 0) :
    source⁻¹ ≠ 0 := by
  intro inverseZero
  have productOne := mul_inv_cancel source sourceNonzero
  rw [inverseZero, mul_zero] at productOne
  exact zero_ne_one productOne

theorem inv_neg (source : Gaussian) : (-source)⁻¹ = -(source⁻¹) := by
  by_cases sourceZero : source = 0
  · rw [sourceZero]
    rfl
  · have negativeNonzero : -source ≠ 0 := neg_ne_zero.mpr sourceZero
    apply mul_right_cancel_of_nonzero negativeNonzero
    calc
      (-source)⁻¹ * (-source) = 1 := by
        rw [mul_comm]
        exact mul_inv_cancel (-source) negativeNonzero
      _ = source⁻¹ * source := by
        rw [mul_comm]
        exact (mul_inv_cancel source sourceZero).symm
      _ = (-(source⁻¹)) * (-source) := (neg_mul_neg source⁻¹ source).symm

instance instExplicitField : RFAP.ExplicitField Gaussian where
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel := mul_inv_cancel
  mul_ne_zero := mul_ne_zero
  inv_ne_zero := inv_ne_zero
  inv_neg := inv_neg

/-- `1 + i`, used by the winding and dyadic Gaussian calculations. -/
def gamma : Gaussian := ⟨1, 1⟩

theorem normSq_gamma : normSq gamma = 2 := by
  change (1 : Coordinate) * 1 + 1 * 1 = 2
  ring1

end Gaussian

end RFAP.CanonicalGaussian
