import mathlib.Tactic.QuotientFreeRing
import Mathlib.Algebra.Order.Ring.Defs
import mathlib.RFAP.CanonicalFractionField

/-!
# Casts and order for canonical fractions

Natural and integer casts are related directly to denominator-one canonical
records.  Weak order is sign-safe cross multiplication; strict order is its
constructive asymmetric part and is proved equivalent to strict integer
cross multiplication.
-/

namespace RFAP.CanonicalFraction

/-- The canonical denominator-one record for an integer. -/
def fromInt (value : Int) : Rational :=
  ⟨value, 1, by decide,
    ⟨⟨0, 1, by
      simp only [zero_mul, Int.natCast_one, _root_.one_mul,
        _root_.zero_add]⟩⟩⟩

theorem add_fromInt (left right : Int) :
    fromInt left + fromInt right = fromInt (left + right) := by
  apply eq_of_equivalent
  have displayed := add_plain (fromInt left) (fromInt right)
  have plainAddition :
      Equivalent
        (plainAddRaw (fromInt left).toRaw (fromInt right).toRaw)
        (fromInt (left + right)).toRaw := by
    dsimp only [Equivalent, plainAddRaw, Rational.toRaw, fromInt]
    simp only [Int.natCast_one, Int.mul_one, Nat.one_mul]
  exact equivalent_trans displayed plainAddition

/-- Natural casts are exactly denominator-one canonical records. -/
theorem natCast_eq_fromInt (value : Nat) :
    (value : Rational) = fromInt (value : Int) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ, inductionHypothesis]
      change fromInt (value : Int) + fromInt 1 =
        fromInt ((value + 1 : Nat) : Int)
      rw [add_fromInt]
      rfl

/-- Integer casts are exactly denominator-one canonical records. -/
theorem intCast_eq_fromInt (value : Int) :
    (value : Rational) = fromInt value := by
  cases value with
  | ofNat value =>
      change (((value : Nat) : Int) : Rational) = fromInt (value : Int)
      rw [Int.cast_natCast, natCast_eq_fromInt]
  | negSucc value =>
      rw [Int.cast_negSucc, natCast_eq_fromInt]
      apply Rational.ext
      · rfl
      · rfl

/-- Equality of natural casts reflects equality by their stored
numerators. -/
theorem natCast_injective_direct {left right : Nat}
    (equal : (left : Rational) = (right : Rational)) : left = right := by
  rw [natCast_eq_fromInt left, natCast_eq_fromInt right] at equal
  have numeratorEqual := congrArg Rational.num equal
  exact Int.ofNat.inj numeratorEqual

/-- Equality of integer casts reflects equality by their stored
numerators. -/
theorem intCast_injective_direct {left right : Int}
    (equal : (left : Rational) = (right : Rational)) : left = right := by
  rw [intCast_eq_fromInt left, intCast_eq_fromInt right] at equal
  exact congrArg Rational.num equal

/-- Sign-safe cross-multiplication weak order. -/
def LessEqual (left right : Rational) : Prop :=
  left.num * (right.den : Int) ≤ right.num * (left.den : Int)

instance instLE : LE Rational := ⟨LessEqual⟩

/-- Strict comparison is the constructive asymmetric part of weak
comparison. -/
instance instLT : LT Rational :=
  ⟨fun left right => left ≤ right ∧ ¬right ≤ left⟩

instance instDecidableLE : DecidableLE Rational := fun left right =>
  inferInstanceAs (Decidable
    (left.num * (right.den : Int) ≤ right.num * (left.den : Int)))

instance instDecidableLT : DecidableLT Rational := fun left right =>
  inferInstanceAs (Decidable (left ≤ right ∧ ¬right ≤ left))

theorem int_le_of_mul_le_mul_right {left right factor : Int}
    (factorPositive : 0 < factor)
    (scaled : left * factor ≤ right * factor) : left ≤ right := by
  by_cases ordered : left ≤ right
  · exact ordered
  · have reverse : right < left := Int.not_le.mp ordered
    have strictScaled : right * factor < left * factor :=
      Int.mul_lt_mul_of_pos_right reverse factorPositive
    exact ((Int.not_lt_of_ge scaled) strictScaled).elim

theorem le_refl (source : Rational) : source ≤ source :=
  Int.le_refl _

theorem le_trans (first second third : Rational)
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    first ≤ third := by
  apply int_le_of_mul_le_mul_right
    (Int.natCast_pos.mpr second.den_pos)
  have thirdDenominatorNonnegative : 0 ≤ (third.den : Int) :=
    Int.natCast_nonneg _
  have firstDenominatorNonnegative : 0 ≤ (first.den : Int) :=
    Int.natCast_nonneg _
  have firstScaled :=
    Int.mul_le_mul_of_nonneg_right firstSecond thirdDenominatorNonnegative
  have secondScaled :=
    Int.mul_le_mul_of_nonneg_right secondThird firstDenominatorNonnegative
  change
    (first.num * (third.den : Int)) * (second.den : Int) ≤
      (third.num * (first.den : Int)) * (second.den : Int)
  calc
    (first.num * (third.den : Int)) * (second.den : Int) =
        (first.num * (second.den : Int)) * (third.den : Int) := by ring1
    _ ≤ (second.num * (first.den : Int)) * (third.den : Int) := firstScaled
    _ = (second.num * (third.den : Int)) * (first.den : Int) := by ring1
    _ ≤ (third.num * (second.den : Int)) * (first.den : Int) := secondScaled
    _ = (third.num * (first.den : Int)) * (second.den : Int) := by ring1

theorem le_antisymm (left right : Rational)
    (leftRight : left ≤ right) (rightLeft : right ≤ left) : left = right :=
  eq_of_cross (Int.le_antisymm leftRight rightLeft)

instance instPartialOrder : PartialOrder Rational where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

theorem le_total (left right : Rational) : left ≤ right ∨ right ≤ left :=
  Int.le_total (left.num * (right.den : Int))
    (right.num * (left.den : Int))

instance instMin : Min Rational := minOfLe
instance instMax : Max Rational := maxOfLe
instance instOrd : Ord Rational :=
  ⟨fun left right => compareOfLessAndEq left right⟩

instance instLinearOrder : LinearOrder Rational where
  le_total := le_total
  toDecidableLE := instDecidableLE
  toDecidableEq := inferInstance
  toDecidableLT := instDecidableLT
  compare_eq_compareOfLessAndEq := by intros; rfl

/-- Strict order is strict integer cross multiplication. -/
theorem lt_iff_cross (left right : Rational) :
    left < right ↔
      left.num * (right.den : Int) < right.num * (left.den : Int) :=
  by
    change
      (left.num * (right.den : Int) ≤ right.num * (left.den : Int) ∧
        ¬right.num * (left.den : Int) ≤ left.num * (right.den : Int)) ↔ _
    exact Int.lt_iff_le_and_not_ge.symm

/-- The sign of a canonical rational is the sign of its stored numerator. -/
theorem zero_lt_iff_num_pos (source : Rational) :
    0 < source ↔ 0 < source.num := by
  rw [lt_iff_cross]
  change (0 : Int) * (source.den : Int) < source.num * 1 ↔ 0 < source.num
  simp only [Int.zero_mul, Int.mul_one]

/-- Equivalent positive-denominator displays have numerators with the same
strict sign. -/
theorem numerator_pos_iff_of_equivalent {left right : RawFraction}
    (equivalent : Equivalent left right) :
    0 < left.num ↔ 0 < right.num := by
  constructor
  · intro leftPositive
    have productPositive :
        0 < left.num * (right.den : Int) :=
      Int.mul_pos leftPositive (Int.natCast_pos.mpr right.den_pos)
    rw [equivalent] at productPositive
    exact Int.pos_of_mul_pos_left productPositive
      (Int.natCast_pos.mpr left.den_pos)
  · intro rightPositive
    have productPositive :
        0 < right.num * (left.den : Int) :=
      Int.mul_pos rightPositive (Int.natCast_pos.mpr left.den_pos)
    rw [← equivalent] at productPositive
    exact Int.pos_of_mul_pos_left productPositive
      (Int.natCast_pos.mpr right.den_pos)

/-- The concrete strict order is exactly positivity of the explicit
difference. -/
theorem lt_iff_zero_lt_sub (left right : Rational) :
    left < right ↔ 0 < right - left := by
  rw [lt_iff_cross, zero_lt_iff_num_pos]
  change
    left.num * (right.den : Int) < right.num * (left.den : Int) ↔
      0 < (sub right left).num
  have differenceDisplay := add_equivalent right (-left)
  have numeratorSigns := numerator_pos_iff_of_equivalent differenceDisplay
  have numeratorSigns' :
      0 < (sub right left).num ↔
        0 < right.num * (left.den : Int) +
          left.num.neg * (right.den : Int) := by
    simpa only [sub, Neg.neg, neg, Rational.toRaw, referenceAddRaw] using
      numeratorSigns
  rw [numeratorSigns']
  have negativeProduct :
      left.num.neg * (right.den : Int) =
        -(left.num * (right.den : Int)) :=
    Int.neg_mul left.num (right.den : Int)
  rw [negativeProduct, ← _root_.sub_eq_add_neg]
  exact Int.sub_pos.symm

end RFAP.CanonicalFraction
