import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.GaussianProjective
import CCL.Encoding.Sectors

/-!
# Explicit constructive Gaussian integers

This module supplies the finite integral numerator/denominator representation
used by the terminating CCL encoder.  It intentionally does not import
Mathlib's Gaussian integers or its rational field.
-/

namespace CCL.Integral

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2

/-- A Gaussian integer is exactly two displayed integers. -/
@[ext]
structure GaussianInt where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace GaussianInt

instance : Zero GaussianInt := ⟨⟨0, 0⟩⟩
instance : One GaussianInt := ⟨⟨1, 0⟩⟩
instance : Add GaussianInt :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Sub GaussianInt :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Neg GaussianInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul GaussianInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im,
    z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem zero_re : (0 : GaussianInt).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianInt).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussianInt).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussianInt).im = 0 := rfl
@[simp] theorem add_re (z w : GaussianInt) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : GaussianInt) : (z + w).im = z.im + w.im := rfl
@[simp] theorem sub_re (z w : GaussianInt) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : GaussianInt) : (z - w).im = z.im - w.im := rfl
@[simp] theorem neg_re (z : GaussianInt) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : GaussianInt) : (-z).im = -z.im := rfl
@[simp] theorem mul_re (z w : GaussianInt) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : GaussianInt) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

@[simp] theorem zero_add (z : GaussianInt) : 0 + z = z := by
  ext <;> simp only [add_re, add_im, zero_re, zero_im, Int.zero_add]

@[simp] theorem add_zero (z : GaussianInt) : z + 0 = z := by
  ext <;> simp only [add_re, add_im, zero_re, zero_im, Int.add_zero]

theorem add_assoc (x y z : GaussianInt) : x + y + z = x + (y + z) := by
  ext <;> simp only [add_re, add_im] <;> ring1

theorem neg_add_cancel (z : GaussianInt) : -z + z = 0 := by
  ext <;> simp only [neg_re, neg_im, add_re, add_im, zero_re, zero_im] <;>
    ring1

theorem sub_eq_add_neg (z w : GaussianInt) : z - w = z + -w := by
  ext <;> simp only [sub_re, sub_im, add_re, add_im, neg_re, neg_im] <;>
    ring1

@[simp] theorem zero_mul (z : GaussianInt) : 0 * z = 0 := by
  ext <;> simp only [mul_re, mul_im, zero_re, zero_im] <;> ring1

@[simp] theorem mul_zero (z : GaussianInt) : z * 0 = 0 := by
  ext <;> simp only [mul_re, mul_im, zero_re, zero_im] <;> ring1

@[simp] theorem one_mul (z : GaussianInt) : 1 * z = z := by
  ext <;> simp only [mul_re, mul_im, one_re, one_im] <;> ring1

@[simp] theorem mul_one (z : GaussianInt) : z * 1 = z := by
  ext <;> simp only [mul_re, mul_im, one_re, one_im] <;> ring1

theorem mul_assoc (x y z : GaussianInt) : x * y * z = x * (y * z) := by
  ext <;> simp only [mul_re, mul_im] <;> ring1

theorem mul_comm (z w : GaussianInt) : z * w = w * z := by
  ext <;> simp only [mul_re, mul_im] <;> ring1

theorem left_distrib (x y z : GaussianInt) : x * (y + z) = x * y + x * z := by
  ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring1

instance instCommRing : CommRing GaussianInt :=
  CommRing.ofMinimalAxioms
    add_assoc
    zero_add
    neg_add_cancel
    mul_assoc
    mul_comm
    one_mul
    left_distrib

/-- Integer-valued squared norm. -/
def normInt (z : GaussianInt) : Int := z.re * z.re + z.im * z.im

/-- Natural-valued squared norm used as the recursion measure. -/
def normNat (z : GaussianInt) : Nat := (normInt z).natAbs

private theorem int_mul_self_nonneg (value : Int) : 0 ≤ value * value := by
  by_cases nonnegative : 0 ≤ value
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : value ≤ 0 := Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

theorem normInt_nonneg (z : GaussianInt) : 0 ≤ normInt z := by
  exact Int.add_nonneg (int_mul_self_nonneg z.re) (int_mul_self_nonneg z.im)

theorem normInt_eq_zero {z : GaussianInt} : normInt z = 0 ↔ z = 0 := by
  constructor
  · intro normZero
    have realNonnegative : 0 ≤ z.re * z.re := int_mul_self_nonneg z.re
    have imagNonnegative : 0 ≤ z.im * z.im := int_mul_self_nonneg z.im
    have realZero : z.re * z.re = 0 := by
      apply le_antisymm
      · calc
          z.re * z.re ≤ z.re * z.re + z.im * z.im :=
            Int.le_add_of_nonneg_right imagNonnegative
          _ = 0 := normZero
      · exact realNonnegative
    have imagZero : z.im * z.im = 0 := by
      apply le_antisymm
      · calc
          z.im * z.im ≤ z.re * z.re + z.im * z.im :=
            Int.le_add_of_nonneg_left realNonnegative
          _ = 0 := normZero
      · exact imagNonnegative
    have realCoordinateZero : z.re = 0 :=
      (Int.mul_eq_zero.mp realZero).elim id id
    have imagCoordinateZero : z.im = 0 :=
      (Int.mul_eq_zero.mp imagZero).elim id id
    ext <;> assumption
  · rintro rfl
    rfl

theorem normInt_pos {z : GaussianInt} (nonzero : z ≠ 0) : 0 < normInt z := by
  have nonnegative := normInt_nonneg z
  have notZero : normInt z ≠ 0 := fun equal => nonzero (normInt_eq_zero.mp equal)
  exact lt_of_le_of_ne nonnegative (Ne.symm notZero)

private theorem natAbs_pos_of_pos {value : Int} (positive : 0 < value) :
    0 < value.natAbs := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => exact (Int.lt_irrefl 0 positive).elim
      | succ value => exact Nat.zero_lt_succ value
  | negSucc value =>
      exact (Int.not_lt_of_ge (Int.le_of_lt (Int.negSucc_lt_zero value))
        positive).elim

theorem normNat_pos {z : GaussianInt} (nonzero : z ≠ 0) : 0 < normNat z := by
  exact natAbs_pos_of_pos (normInt_pos nonzero)

theorem normInt_mul (z w : GaussianInt) :
    normInt (z * w) = normInt z * normInt w := by
  simp only [normInt, mul_re, mul_im]
  ring1

theorem eq_zero_or_eq_zero_of_mul_eq_zero {z w : GaussianInt}
    (productZero : z * w = 0) : z = 0 ∨ w = 0 := by
  have normProduct : normInt z * normInt w = 0 := by
    rw [← normInt_mul, productZero]
    rfl
  rcases Int.mul_eq_zero.mp normProduct with leftZero | rightZero
  · exact Or.inl (normInt_eq_zero.mp leftZero)
  · exact Or.inr (normInt_eq_zero.mp rightZero)

theorem mul_ne_zero {z w : GaussianInt} (leftNonzero : z ≠ 0)
    (rightNonzero : w ≠ 0) : z * w ≠ 0 := by
  intro productZero
  rcases eq_zero_or_eq_zero_of_mul_eq_zero productZero with
    leftZero | rightZero
  · exact leftNonzero leftZero
  · exact rightNonzero rightZero

theorem mul_right_cancel_of_ne {x y z : GaussianInt} (zNonzero : z ≠ 0)
    (productsEqual : x * z = y * z) : x = y := by
  have differenceProduct : (x - y) * z = 0 := by
    rw [sub_eq_add_neg]
    calc
      (x + -y) * z = x * z + (-y) * z := by ring1
      _ = y * z + (-y) * z := by rw [productsEqual]
      _ = 0 := by ring1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero differenceProduct with
    differenceZero | zZero
  · apply GaussianInt.ext
    · have coordinateZero := congrArg (fun value => value.re) differenceZero
      simp only [sub_re, zero_re] at coordinateZero
      exact Int.sub_eq_zero.mp coordinateZero
    · have coordinateZero := congrArg (fun value => value.im) differenceZero
      simp only [sub_im, zero_im] at coordinateZero
      exact Int.sub_eq_zero.mp coordinateZero
  · exact (zNonzero zZero).elim

/-- Cross-multiplication equivalence is transitive through an explicitly
nonzero middle denominator, using direct Gaussian-integer cancellation. -/
theorem equivalent_trans_of_mid_q {left middle right : CCL.Proj GaussianInt}
    (leftMiddle : CCL.Proj.Equivalent left middle)
    (middleRight : CCL.Proj.Equivalent middle right)
    (middleDenominatorNonzero : middle.q ≠ 0) :
    CCL.Proj.Equivalent left right := by
  dsimp only [CCL.Proj.Equivalent] at leftMiddle middleRight ⊢
  apply mul_right_cancel_of_ne middleDenominatorNonzero
  calc
    (left.p * right.q) * middle.q =
        right.q * (left.p * middle.q) := by ring1
    _ = right.q * (middle.p * left.q) := by rw [leftMiddle]
    _ = left.q * (middle.p * right.q) := by ring1
    _ = left.q * (right.p * middle.q) := by rw [middleRight]
    _ = (right.p * left.q) * middle.q := by ring1

instance instNontrivial : Nontrivial GaussianInt where
  exists_pair_ne := ⟨0, 1, by decide⟩

@[simp] theorem normNat_mul (z w : GaussianInt) :
    normNat (z * w) = normNat z * normNat w := by
  rw [normNat, normInt_mul, Int.natAbs_mul]
  rfl

/-- Transparent natural power. -/
def natPow (z : GaussianInt) : Nat → GaussianInt
  | 0 => 1
  | exponent + 1 => natPow z exponent * z

@[simp] theorem natPow_zero (z : GaussianInt) : natPow z 0 = 1 := rfl

@[simp] theorem natPow_succ (z : GaussianInt) (exponent : Nat) :
    natPow z (exponent + 1) = natPow z exponent * z := rfl

theorem natPow_ne_zero (z : GaussianInt) (nonzero : z ≠ 0) :
    ∀ exponent : Nat, natPow z exponent ≠ 0
  | 0 => by
      intro oneZero
      have realOneZero := congrArg GaussianInt.re oneZero
      exact (show (1 : Int) ≠ 0 by decide) realOneZero
  | exponent + 1 => by
      intro productZero
      have normProduct :
          normInt (natPow z exponent) * normInt z = 0 := by
        rw [← normInt_mul]
        exact normInt_eq_zero.mpr productZero
      rcases Int.mul_eq_zero.mp normProduct with leftZero | rightZero
      · exact natPow_ne_zero z nonzero exponent (normInt_eq_zero.mp leftZero)
      · exact nonzero (normInt_eq_zero.mp rightZero)

/-- Coordinatewise embedding into constructive Gaussian fractions. -/
def toGaussian (z : GaussianInt) : Gaussian := ⟨z.re, z.im⟩

@[simp] theorem toGaussian_zero : toGaussian 0 = 0 := rfl
@[simp] theorem toGaussian_one : toGaussian 1 = 1 := rfl

@[simp] theorem toGaussian_add (z w : GaussianInt) :
    toGaussian (z + w) = toGaussian z + toGaussian w := by
  ext <;> simp only [toGaussian, add_re, add_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_add]

@[simp] theorem toGaussian_neg (z : GaussianInt) :
    toGaussian (-z) = -toGaussian z := by
  ext <;> simp only [toGaussian, neg_re, neg_im,
    RFAP.ConstructiveGaussian.Gaussian.neg_re,
    RFAP.ConstructiveGaussian.Gaussian.neg_im, Int.cast_neg]

@[simp] theorem toGaussian_sub (z w : GaussianInt) :
    toGaussian (z - w) = toGaussian z - toGaussian w := by
  ext <;> simp only [toGaussian, sub_re, sub_im,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_sub]

@[simp] theorem toGaussian_mul (z w : GaussianInt) :
    toGaussian (z * w) = toGaussian z * toGaussian w := by
  ext <;> simp only [toGaussian, mul_re, mul_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_sub, Int.cast_add,
    QuotientFreeRing.intCast_mul]

theorem toGaussian_injective : Function.Injective toGaussian := by
  intro z w equal
  apply GaussianInt.ext
  · exact RFAP.ConstructiveFraction.intCast_injective_direct
      (congrArg RFAP.ConstructiveGaussian.Gaussian.re equal)
  · exact RFAP.ConstructiveFraction.intCast_injective_direct
      (congrArg RFAP.ConstructiveGaussian.Gaussian.im equal)

@[simp] theorem toGaussian_eq_zero {z : GaussianInt} :
    toGaussian z = 0 ↔ z = 0 := by
  constructor
  · intro zero
    exact toGaussian_injective (zero.trans toGaussian_zero.symm)
  · rintro rfl
    exact toGaussian_zero

theorem normSq_toGaussian (z : GaussianInt) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (toGaussian z) =
      (normNat z : Coordinate) := by
  rw [← Int.cast_natCast]
  rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg z)]
  change (z.re : Coordinate) ^ 2 + (z.im : Coordinate) ^ 2 =
    ((normInt z : Int) : Coordinate)
  simp only [normInt, pow_two, Int.cast_add, QuotientFreeRing.intCast_mul]

/-- `1+i` in the explicit integral representation. -/
def gammaInt : GaussianInt := ⟨1, 1⟩

@[simp] theorem normNat_gammaInt : normNat gammaInt = 2 := rfl

@[simp] theorem toGaussian_gammaInt :
    toGaussian gammaInt = RFAP.ConstructiveGaussian.Gaussian.gamma := rfl

@[simp] theorem normNat_gammaInt_pow (exponent : Nat) :
    normNat (natPow gammaInt exponent) = 2 ^ exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [natPow_succ, normNat_mul, inductionHypothesis, normNat_gammaInt,
        Nat.pow_succ]

@[simp] theorem toGaussian_gammaInt_pow (exponent : Nat) :
    toGaussian (natPow gammaInt exponent) =
      RFAP.ConstructiveGaussian.Gaussian.natPow
        RFAP.ConstructiveGaussian.Gaussian.gamma exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent inductionHypothesis =>
      rw [natPow_succ, toGaussian_mul, inductionHypothesis,
        RFAP.ConstructiveGaussian.Gaussian.natPow_succ,
        toGaussian_gammaInt]

/-- The eight finite sector representatives as Gaussian integers. -/
def sectorInt : Sector → GaussianInt
  | .east => ⟨1, 0⟩
  | .northEast => ⟨1, 1⟩
  | .north => ⟨0, 1⟩
  | .northWest => ⟨-1, 1⟩
  | .west => ⟨-1, 0⟩
  | .southWest => ⟨-1, -1⟩
  | .south => ⟨0, -1⟩
  | .southEast => ⟨1, -1⟩

@[simp] theorem toGaussian_sectorInt (sector : Sector) :
    toGaussian (sectorInt sector) = sector.rep := by
  cases sector <;> rfl

end GaussianInt

/-- An uncancelled Gaussian-integer fraction with explicit nonzero
denominator evidence. -/
structure Frac where
  num : GaussianInt
  den : GaussianInt
  den_ne : den ≠ 0
deriving Repr

namespace Frac

open RFAP.ConstructiveGaussian.Gaussian
open GaussianInt

/-- Exact constructive Gaussian value of an uncancelled fraction. -/
def value (fraction : Frac) : Gaussian :=
  toGaussian fraction.num * (toGaussian fraction.den)⁻¹

theorem den_toGaussian_ne (fraction : Frac) :
    toGaussian fraction.den ≠ 0 := by
  intro denominatorZero
  exact fraction.den_ne (toGaussian_eq_zero.mp denominatorZero)

/-- Cross-multiplied value identity `P = (P/Q)Q`. -/
theorem value_mul_den (fraction : Frac) :
    fraction.value * toGaussian fraction.den = toGaussian fraction.num := by
  dsimp only [value]
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.inv_mul _ fraction.den_toGaussian_ne,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- Exact norm quotient for an uncancelled integral fraction. -/
theorem normSq_value (fraction : Frac) :
    normSq fraction.value =
      (GaussianInt.normNat fraction.num : Coordinate) /
        GaussianInt.normNat fraction.den := by
  rw [value, normSq_mul, inv_eq, normSq_inv _ fraction.den_toGaussian_ne,
    GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
  exact (RFAP.ExplicitField.div_eq_mul_inv _ _).symm

theorem value_ne_zero (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    fraction.value ≠ 0 := by
  intro valueZero
  have productZero := congrArg (fun value =>
    value * GaussianInt.toGaussian fraction.den) valueZero
  rw [fraction.value_mul_den,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul] at productZero
  exact numeratorNonzero (GaussianInt.toGaussian_eq_zero.mp productZero)

/-- Canonical uncancelled Gaussian-integer fraction for a constructive
Gaussian rational.  Both coordinate representatives are computed by the
choice-free gcd normalization in `ConstructiveFraction`. -/
def ofGaussian (value : Gaussian) : Frac := by
  let real := RFAP.ConstructiveFraction.representative value.re
  let imaginary := RFAP.ConstructiveFraction.representative value.im
  let denominatorNat := real.den * imaginary.den
  have denominatorNatPositive : 0 < denominatorNat :=
    Nat.mul_pos real.den_pos imaginary.den_pos
  let numerator : GaussianInt :=
    ⟨real.num * (imaginary.den : Int),
      imaginary.num * (real.den : Int)⟩
  let denominator : GaussianInt := ⟨(denominatorNat : Int), 0⟩
  have denominatorNonzero : denominator ≠ 0 := by
    intro zero
    have realZero := congrArg GaussianInt.re zero
    dsimp only [denominator] at realZero
    simp only [GaussianInt.zero_re] at realZero
    have denominatorNatZero : denominatorNat = 0 := Int.ofNat.inj realZero
    exact (Nat.ne_of_gt denominatorNatPositive) denominatorNatZero
  exact ⟨numerator, denominator, denominatorNonzero⟩

private theorem representative_mul_den (value : Coordinate) :
    value * ((RFAP.ConstructiveFraction.representative value).den :
      Coordinate) =
      ((RFAP.ConstructiveFraction.representative value).num : Coordinate) := by
  let representative := RFAP.ConstructiveFraction.representative value
  calc
    value * (representative.den : Coordinate) =
        RFAP.ConstructiveFraction.ofFraction representative.toFraction *
          (representative.den : Coordinate) := by
      exact congrArg (fun coordinate =>
        coordinate * (representative.den : Coordinate))
          (RFAP.ConstructiveFraction.representative_spec value).symm
    _ = (representative.num : Coordinate) := by
      simpa only [representative,
        RFAP.ConstructiveFraction.ReducedFraction.toFraction,
        Int.cast_natCast] using
        RFAP.ConstructiveFraction.ofFraction_mul_den
          representative.toFraction

/-- The computed integral fraction denotes the supplied Gaussian exactly. -/
theorem ofGaussian_value (source : Gaussian) :
    (ofGaussian source).value = source := by
  let real := RFAP.ConstructiveFraction.representative source.re
  let imaginary := RFAP.ConstructiveFraction.representative source.im
  let denominatorNat := real.den * imaginary.den
  have denominatorNonzero : toGaussian (ofGaussian source).den ≠ 0 :=
    (ofGaussian source).den_toGaussian_ne
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorNonzero
  rw [(ofGaussian source).value_mul_den]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change
      ((real.num * (imaginary.den : Int) : Int) : Coordinate) =
        source.re * (denominatorNat : Coordinate) - source.im * 0
    dsimp only [denominatorNat]
    rw [QuotientFreeRing.intCast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      ((real.num : Int) : Coordinate) * (imaginary.den : Coordinate) =
          (source.re * (real.den : Coordinate)) *
            (imaginary.den : Coordinate) := by
        rw [representative_mul_den source.re]
      _ = source.re *
          ((real.den : Coordinate) * (imaginary.den : Coordinate)) := by
        ring1
      _ = source.re *
          ((real.den : Coordinate) * (imaginary.den : Coordinate)) -
            source.im * 0 := by ring1
  · change
      ((imaginary.num * (real.den : Int) : Int) : Coordinate) =
        source.re * 0 + source.im * (denominatorNat : Coordinate)
    dsimp only [denominatorNat]
    rw [QuotientFreeRing.intCast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      ((imaginary.num : Int) : Coordinate) * (real.den : Coordinate) =
          (source.im * (imaginary.den : Coordinate)) *
            (real.den : Coordinate) := by
        rw [representative_mul_den source.im]
      _ = source.im *
          ((real.den : Coordinate) * (imaginary.den : Coordinate)) := by
        ring1
      _ = source.re * 0 + source.im *
          ((real.den : Coordinate) * (imaginary.den : Coordinate)) := by
        ring1

/-- Nonzero Gaussian values compute to fractions with nonzero numerators. -/
theorem ofGaussian_num_ne_zero {source : Gaussian} (nonzero : source ≠ 0) :
    (ofGaussian source).num ≠ 0 := by
  intro numeratorZero
  have valueZero : (ofGaussian source).value = 0 := by
    rw [value, numeratorZero, toGaussian_zero,
      RFAP.ConstructiveGaussian.Gaussian.zero_mul]
  exact nonzero ((ofGaussian_value source).symm.trans valueZero)

end Frac

end CCL.Integral
