import mathlib.Tactic.QuotientFreeRing
import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.CanonicalFractionOrder
import mathlib.RFAP.CanonicalFractionSize

/-!
# Compatibility surface for canonical constructive fractions

This module provides the public `RFAP.ConstructiveFraction` names over the
quotient-free canonical carrier.  It deliberately does not import either the
public `ConstructiveFraction` facade or the inactive
`LegacyQuotientFraction` implementation.

The signed-denominator `Fraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace RFAP.ConstructiveFraction

/-- The active quotient-free rational carrier. -/
abbrev Rational := RFAP.CanonicalFraction.Rational

/-- Compatibility input syntax with an explicitly positive signed
denominator.  Semantic values normalize this display immediately. -/
structure Fraction where
  num : Int
  den : Int
  den_pos : 0 < den
deriving DecidableEq

/-- Cross-multiplication equivalence of compatibility displays. -/
def Equivalent (left right : Fraction) : Prop :=
  left.num * right.den = right.num * left.den

instance (left right : Fraction) : Decidable (Equivalent left right) :=
  inferInstanceAs
    (Decidable (left.num * right.den = right.num * left.den))

theorem equivalent_refl (fraction : Fraction) :
    Equivalent fraction fraction := rfl

theorem equivalent_symm {left right : Fraction}
    (equivalent : Equivalent left right) : Equivalent right left :=
  equivalent.symm

theorem equivalent_trans {left middle right : Fraction}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right := by
  have productZero :
      (left.num * right.den - right.num * left.den) * middle.den = 0 := by
    dsimp only [Equivalent] at leftMiddle middleRight
    rw [sub_mul]
    calc
      left.num * right.den * middle.den -
          right.num * left.den * middle.den =
          right.den * (left.num * middle.den) -
            left.den * (right.num * middle.den) := by ring1
      _ = right.den * (middle.num * left.den) -
            left.den * (middle.num * right.den) := by
              rw [leftMiddle, ← middleRight]
      _ = 0 := by ring1
  have middleDenominatorNonzero : middle.den ≠ 0 :=
    Int.ne_of_gt middle.den_pos
  have differenceZero :
      left.num * right.den - right.num * left.den = 0 :=
    (Int.mul_eq_zero.mp productZero).resolve_right middleDenominatorNonzero
  exact Int.sub_eq_zero.mp differenceZero

/-- Positivity survives the executable conversion from a positive integer to
a natural number. -/
theorem toNat_pos_direct {value : Int} (positive : 0 < value) :
    0 < value.toNat := by
  cases value with
  | ofNat value =>
      change 0 < value
      change Int.ofNat 0 < Int.ofNat value at positive
      exact Int.ofNat_lt.mp positive
  | negSucc value =>
      exact (Int.not_lt_of_ge
        (Int.le_of_lt (Int.negSucc_lt_zero value)) positive).elim

/-- Convert compatibility input syntax to the canonical raw display. -/
def Fraction.toRaw (fraction : Fraction) : RFAP.CanonicalFraction.RawFraction :=
  ⟨fraction.num, fraction.den.toNat, toNat_pos_direct fraction.den_pos⟩

theorem fraction_toRaw_equivalent_iff (left right : Fraction) :
    RFAP.CanonicalFraction.Equivalent left.toRaw right.toRaw ↔ Equivalent left right := by
  have leftDenominator : (left.den.toNat : Int) = left.den :=
    Int.toNat_of_nonneg left.den_pos.le
  have rightDenominator : (right.den.toNat : Int) = right.den :=
    Int.toNat_of_nonneg right.den_pos.le
  simp only [RFAP.CanonicalFraction.Equivalent, Fraction.toRaw, Equivalent,
    leftDenominator, rightDenominator]

/-- Normalize a displayed fraction to the quotient-free semantic carrier. -/
def ofFraction (fraction : Fraction) : Rational :=
  RFAP.CanonicalFraction.normalize fraction.toRaw

theorem ofFraction_eq_of_equivalent {left right : Fraction}
    (equivalent : Equivalent left right) :
    ofFraction left = ofFraction right := by
  apply RFAP.CanonicalFraction.normalize_respects
  exact (fraction_toRaw_equivalent_iff left right).mpr equivalent

theorem ofFraction_eq_iff (left right : Fraction) :
    ofFraction left = ofFraction right ↔ Equivalent left right := by
  rw [ofFraction, ofFraction,
    ← RFAP.CanonicalFraction.equivalent_iff_normalize_eq,
    fraction_toRaw_equivalent_iff]

def zeroFraction : Fraction := ⟨0, 1, by decide⟩
def oneFraction : Fraction := ⟨1, 1, by decide⟩

def addFraction (left right : Fraction) : Fraction :=
  ⟨left.num * right.den + right.num * left.den,
    left.den * right.den, Int.mul_pos left.den_pos right.den_pos⟩

def negFraction (fraction : Fraction) : Fraction :=
  ⟨-fraction.num, fraction.den, fraction.den_pos⟩

def mulFraction (left right : Fraction) : Fraction :=
  ⟨left.num * right.num, left.den * right.den,
    Int.mul_pos left.den_pos right.den_pos⟩

private theorem int_mul_self_pos {value : Int} (nonzero : value ≠ 0) :
    0 < value * value := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => exact (nonzero rfl).elim
      | succ value =>
          exact Int.mul_pos (Int.ofNat_succ_pos value)
            (Int.ofNat_succ_pos value)
  | negSucc value =>
      exact Int.mul_pos_of_neg_of_neg
        (Int.negSucc_lt_zero value) (Int.negSucc_lt_zero value)

/-- The compatibility display for reciprocal is rebuilt from the executable
canonical reciprocal. -/
def invFraction (fraction : Fraction) : Fraction :=
  let reciprocal := (ofFraction fraction)⁻¹
  ⟨reciprocal.num, (reciprocal.den : Int),
    Int.natCast_pos.mpr reciprocal.den_pos⟩

theorem ofFraction_invFraction (fraction : Fraction) :
    ofFraction (invFraction fraction) = (ofFraction fraction)⁻¹ := by
  let reciprocal := (ofFraction fraction)⁻¹
  change RFAP.CanonicalFraction.normalize
    ⟨reciprocal.num, Int.toNat (reciprocal.den : Int),
      toNat_pos_direct (Int.natCast_pos.mpr reciprocal.den_pos)⟩ = reciprocal
  have displayEqual :
      (⟨reciprocal.num, Int.toNat (reciprocal.den : Int),
        toNat_pos_direct (Int.natCast_pos.mpr reciprocal.den_pos)⟩ :
        RFAP.CanonicalFraction.RawFraction) = reciprocal.toRaw := by
    cases reciprocal with
    | mk num den den_pos reduced =>
        simp only [RFAP.CanonicalFraction.Rational.toRaw,
          Int.toNat_natCast]
  rw [displayEqual, RFAP.CanonicalFraction.normalize_idempotent]

theorem add_comm (left right : Rational) : left + right = right + left :=
  RFAP.CanonicalFraction.add_comm left right

theorem add_assoc (first second third : Rational) :
    first + second + third = first + (second + third) :=
  RFAP.CanonicalFraction.add_assoc first second third

theorem zero_add (source : Rational) : 0 + source = source :=
  RFAP.CanonicalFraction.zero_add source

theorem le_antisymm (a b : Rational) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  RFAP.CanonicalFraction.le_antisymm a b hab hba

theorem neg_add_cancel (source : Rational) : -source + source = 0 :=
  RFAP.CanonicalFraction.neg_add_cancel source

theorem mul_comm (left right : Rational) : left * right = right * left :=
  RFAP.CanonicalFraction.mul_comm left right

theorem mul_assoc (first second third : Rational) :
    first * second * third = first * (second * third) :=
  RFAP.CanonicalFraction.mul_assoc first second third

theorem one_mul (source : Rational) : 1 * source = source :=
  RFAP.CanonicalFraction.one_mul source

theorem left_distrib (first second third : Rational) :
    first * (second + third) = first * second + first * third :=
  RFAP.CanonicalFraction.left_distrib first second third

theorem mul_inv_cancel (source : Rational) (nonzero : source ≠ 0) :
    source * source⁻¹ = 1 :=
  RFAP.CanonicalFraction.mul_inv_cancel source nonzero

theorem inv_zero : (0 : Rational)⁻¹ = 0 :=
  RFAP.CanonicalFraction.inv_zero

theorem zero_ne_one : (0 : Rational) ≠ 1 :=
  RFAP.CanonicalFraction.zero_ne_one

/-- Reassociate four factors and exchange only the middle two. -/
theorem mul_pair_swap (first second third fourth : Rational) :
    (first * second) * (third * fourth) =
      (first * third) * (second * fourth) := by
  ring1

/-- Natural casts have their denominator-one compatibility display. -/
theorem natCast_eq_fraction (value : Nat) :
    (value : Rational) =
      ofFraction ⟨Int.ofNat value, 1, by decide⟩ := by
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt]
  change RFAP.CanonicalFraction.fromInt (Int.ofNat value) =
    RFAP.CanonicalFraction.normalize
      ⟨Int.ofNat value, Int.toNat 1, toNat_pos_direct (by decide)⟩
  have displayEqual :
      (⟨Int.ofNat value, Int.toNat 1,
        toNat_pos_direct (by decide)⟩ : RFAP.CanonicalFraction.RawFraction) =
        (RFAP.CanonicalFraction.fromInt (Int.ofNat value)).toRaw := by
    rfl
  rw [displayEqual, RFAP.CanonicalFraction.normalize_idempotent]

/-- Integer casts have their denominator-one compatibility display. -/
theorem intCast_eq_fraction (value : Int) :
    (value : Rational) = ofFraction ⟨value, 1, by decide⟩ := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt]
  change RFAP.CanonicalFraction.fromInt value =
    RFAP.CanonicalFraction.normalize ⟨value, Int.toNat 1,
      toNat_pos_direct (by decide)⟩
  have displayEqual :
      (⟨value, Int.toNat 1,
        toNat_pos_direct (by decide)⟩ : RFAP.CanonicalFraction.RawFraction) =
        (RFAP.CanonicalFraction.fromInt value).toRaw := by
    rfl
  rw [displayEqual, RFAP.CanonicalFraction.normalize_idempotent]

/-- Integer addition is preserved by the canonical denominator-one
embedding.  This direct route avoids the generic cast theorem's quotient
extensionality dependency. -/
theorem intCast_add_direct (left right : Int) :
    ((left + right : Int) : Rational) =
      (left : Rational) + (right : Rational) := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt]
  exact (RFAP.CanonicalFraction.add_fromInt left right).symm

/-- Integer multiplication is preserved by the canonical denominator-one
embedding, proved directly from the displayed cross-products.  This avoids
the generic cast theorem whose upstream proof route uses quotient
extensionality. -/
theorem intCast_mul_direct (left right : Int) :
    ((left * right : Int) : Rational) =
      (left : Rational) * (right : Rational) := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt]
  apply RFAP.CanonicalFraction.eq_of_equivalent
  have plainResult : RFAP.CanonicalFraction.Equivalent
      (RFAP.CanonicalFraction.fromInt (left * right)).toRaw
      (RFAP.CanonicalFraction.plainMulRaw
        (RFAP.CanonicalFraction.fromInt left).toRaw
        (RFAP.CanonicalFraction.fromInt right).toRaw) := by
    dsimp only [RFAP.CanonicalFraction.Equivalent,
      RFAP.CanonicalFraction.plainMulRaw,
      RFAP.CanonicalFraction.Rational.toRaw,
      RFAP.CanonicalFraction.fromInt]
  exact RFAP.CanonicalFraction.equivalent_trans plainResult
    (RFAP.CanonicalFraction.mul_plain
      (RFAP.CanonicalFraction.fromInt left)
      (RFAP.CanonicalFraction.fromInt right)).symm

/-- The canonical carrier's structural equality test. -/
def equal (left right : Rational) : Bool := decide (left = right)

theorem equal_eq_true_iff (left right : Rational) :
    equal left right = true ↔ left = right := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

def rationalDecEq (left right : Rational) : Decidable (left = right) :=
  inferInstance

def rationalDecLE (left right : Rational) : Decidable (left ≤ right) :=
  inferInstance

def rationalDecLT (left right : Rational) : Decidable (left < right) :=
  inferInstance

/-! ## Direct ordered arithmetic -/

/-- Weak comparison of signed-denominator input displays. -/
def LessEqFraction (left right : Fraction) : Prop :=
  left.num * right.den ≤ right.num * left.den

instance (left right : Fraction) : Decidable (LessEqFraction left right) :=
  inferInstanceAs
    (Decidable (left.num * right.den ≤ right.num * left.den))

private theorem lessEqFraction_imp {left left' right right' : Fraction}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    LessEqFraction left right → LessEqFraction left' right' := by
  intro lessEqual
  have positiveScale : 0 < left.den * right.den :=
    Int.mul_pos left.den_pos right.den_pos
  apply RFAP.CanonicalFraction.int_le_of_mul_le_mul_right positiveScale
  have replacementScaleNonnegative : 0 ≤ left'.den * right'.den :=
    (Int.mul_pos left'.den_pos right'.den_pos).le
  have scaled := Int.mul_le_mul_of_nonneg_right lessEqual
    replacementScaleNonnegative
  dsimp only [LessEqFraction] at lessEqual scaled ⊢
  dsimp only [Equivalent] at leftEquivalent rightEquivalent
  calc
    left'.num * right'.den * (left.den * right.den) =
        (left'.num * left.den) * (right'.den * right.den) := by ring1
    _ = (left.num * left'.den) * (right.den * right'.den) := by
      rw [← leftEquivalent]
      ring1
    _ = (left.num * right.den) * (left'.den * right'.den) := by ring1
    _ ≤ (right.num * left.den) * (left'.den * right'.den) := scaled
    _ = (right.num * right'.den) * (left.den * left'.den) := by ring1
    _ = (right'.num * right.den) * (left'.den * left.den) := by
      rw [rightEquivalent]
      ring1
    _ = right'.num * left'.den * (left.den * right.den) := by ring1

private theorem lessEqFraction_congr {left left' right right' : Fraction}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    LessEqFraction left right ↔ LessEqFraction left' right' :=
  ⟨lessEqFraction_imp leftEquivalent rightEquivalent,
    lessEqFraction_imp leftEquivalent.symm rightEquivalent.symm⟩

theorem sub_eq_add_neg_direct (left right : Rational) :
    left - right = left + -right := rfl

/-- Strict right translation, reduced to the canonical difference test. -/
theorem add_lt_add_right_direct {left right : Rational}
    (less : left < right) (shift : Rational) :
    left + shift < right + shift := by
  rw [RFAP.CanonicalFraction.lt_iff_zero_lt_sub] at less ⊢
  have differenceIdentity :
      right + shift - (left + shift) = right - left := by
    rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
    ring1
  rw [differenceIdentity]
  exact less

/-- Weak right translation, obtained by the finite equality/strict split. -/
theorem add_le_add_right_direct {left right : Rational}
    (lessEqual : left ≤ right) (shift : Rational) :
    left + shift ≤ right + shift := by
  by_cases equal : left = right
  · rw [equal]
  · exact (add_lt_add_right_direct
      ⟨lessEqual, fun reverse => equal
        (RFAP.CanonicalFraction.le_antisymm left right lessEqual reverse)⟩
      shift).le

/-- Weak addition in both arguments. -/
theorem add_le_add_direct {first second third fourth : Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth) :
    first + third ≤ second + fourth := by
  calc
    first + third ≤ second + third :=
      add_le_add_right_direct firstSecond third
    _ = third + second := by ring1
    _ ≤ fourth + second := add_le_add_right_direct thirdFourth second
    _ = second + fourth := by ring1

private theorem add_le_add_left_canonical
    (left right : Rational) (lessEqual : left ≤ right) (shift : Rational) :
    shift + left ≤ shift + right := by
  rw [add_comm shift left, add_comm shift right]
  exact add_le_add_right_direct lessEqual shift

private theorem le_of_add_le_add_left_canonical
    (shift left right : Rational)
    (lessEqual : shift + left ≤ shift + right) : left ≤ right := by
  have translated := add_le_add_right_direct lessEqual (-shift)
  calc
    left = (shift + left) + -shift := by ring1
    _ ≤ (shift + right) + -shift := translated
    _ = right := by ring1

instance instIsOrderedAddMonoid : IsOrderedAddMonoid Rational where
  add_le_add_left := fun _ _ lessEqual shift =>
    add_le_add_right_direct lessEqual shift

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Rational where
  add_le_add_left := fun _ _ lessEqual shift =>
    add_le_add_right_direct lessEqual shift
  le_of_add_le_add_left := fun shift left right lessEqual =>
    le_of_add_le_add_left_canonical shift left right lessEqual

/-! The generic commutative derivation of `AddRightMono` passes through
function swapping and currently reaches `Quot.sound`.  Supply the stored
right-translation proof directly so ordinary ordered-addition lemmas retain
the quotient-free closure. -/
instance instAddRightMono : AddRightMono Rational where
  elim shift _ _ lessEqual := add_le_add_right_direct lessEqual shift

instance instZeroLEOneClass : ZeroLEOneClass Rational where
  zero_le_one := by decide

/-- Recover weak comparison from failure of the reverse strict comparison. -/
theorem le_of_not_gt_direct {left right : Rational}
    (notGreater : ¬ right < left) : left ≤ right := by
  rcases RFAP.CanonicalFraction.le_total left right with direct | reverse
  · exact direct
  · by_cases direct : left ≤ right
    · exact direct
    · exact (notGreater ⟨reverse, direct⟩).elim

/-- Recover strict comparison from failure of the reverse weak comparison. -/
theorem lt_of_not_ge_direct {left right : Rational}
    (notGreaterEqual : ¬ right ≤ left) : left < right := by
  have lessEqual : left ≤ right := by
    rcases RFAP.CanonicalFraction.le_total left right with direct | reverse
    · exact direct
    · exact (notGreaterEqual reverse).elim
  exact ⟨lessEqual, notGreaterEqual⟩

theorem le_of_lt_direct {left right : Rational} (less : left < right) :
    left ≤ right := less.1

theorem le_trans (a b c : Rational) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  RFAP.CanonicalFraction.le_trans a b c hab hbc

theorem sub_le_sub_right_direct {left right : Rational}
    (lessEqual : left ≤ right) (shift : Rational) :
    left - shift ≤ right - shift := by
  simpa only [sub_eq_add_neg_direct] using
    add_le_add_right_direct lessEqual (-shift)

theorem le_of_add_le_add_right_direct {a b c : Rational}
    (lessEqual : a + c ≤ b + c) : a ≤ b := by
  have translated := add_le_add_right_direct lessEqual (-c)
  simpa only [add_assoc, add_neg_cancel_right] using translated

theorem sub_nonneg_direct {left right : Rational}
    (lessEqual : left ≤ right) : 0 ≤ right - left := by
  have translated := add_le_add_right_direct lessEqual (-left)
  calc
    0 = left + -left := by ring1
    _ ≤ right + -left := translated
    _ = right - left := (sub_eq_add_neg_direct right left).symm

theorem le_of_sub_nonneg_direct {left right : Rational}
    (nonnegative : 0 ≤ right - left) : left ≤ right := by
  have translated := add_le_add_right_direct nonnegative left
  calc
    left = 0 + left := by ring1
    _ ≤ (right - left) + left := translated
    _ = right := by
      rw [sub_eq_add_neg_direct]
      ring1

theorem sub_pos_direct {left right : Rational} (less : left < right) :
    0 < right - left :=
  (RFAP.CanonicalFraction.lt_iff_zero_lt_sub left right).mp less

theorem lt_of_sub_pos_direct {left right : Rational}
    (positive : 0 < right - left) : left < right :=
  (RFAP.CanonicalFraction.lt_iff_zero_lt_sub left right).mpr positive

theorem sub_neg_direct {left right : Rational} (less : left < right) :
    left - right < 0 := by
  have positive := sub_pos_direct less
  have negated : -(right - left) < 0 := neg_neg_of_pos positive
  have identity : -(right - left) = left - right := by
    rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
    ring1
  rw [identity] at negated
  exact negated

theorem lt_of_sub_neg_direct {left right : Rational}
    (negative : left - right < 0) : left < right := by
  have positive : 0 < -(left - right) := neg_pos.mpr negative
  apply lt_of_sub_pos_direct
  have identity : -(left - right) = right - left := by
    rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
    ring1
  rwa [identity] at positive

theorem add_lt_add_left_direct {left right : Rational}
    (less : left < right) (shift : Rational) :
    shift + left < shift + right := by
  simpa only [add_comm shift] using add_lt_add_right_direct less shift

theorem sub_lt_sub_right_direct {left right : Rational}
    (less : left < right) (shift : Rational) :
    left - shift < right - shift := by
  simpa only [sub_eq_add_neg_direct] using
    add_lt_add_right_direct less (-shift)

theorem neg_lt_neg_direct {left right : Rational} (less : left < right) :
    -right < -left := by
  apply lt_of_sub_pos_direct
  have positive := sub_pos_direct less
  have identity : -left - -right = right - left := by
    rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
    ring1
  rwa [identity]

theorem sub_lt_sub_left_direct {a b : Rational}
    (less : a < b) (c : Rational) :
    c - b < c - a := by
  simpa only [sub_eq_add_neg_direct] using
    add_lt_add_left_direct (neg_lt_neg_direct less) c

theorem neg_le_neg_direct {left right : Rational}
    (lessEqual : left ≤ right) : -right ≤ -left := by
  by_cases equal : left = right
  · rw [equal]
  · exact (neg_lt_neg_direct
      ⟨lessEqual, fun reverse => equal
        (RFAP.CanonicalFraction.le_antisymm left right lessEqual reverse)⟩).le

/-- Weak subtraction in both arguments, assembled from the canonical
addition and negation order laws rather than the generic ordered-group
inheritance path. -/
theorem sub_le_sub_direct {first second third fourth : Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth) :
    first - fourth ≤ second - third := by
  rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
  exact add_le_add_direct firstSecond (neg_le_neg_direct thirdFourth)

theorem sub_le_sub_left_direct {left right : Rational}
    (lessEqual : left ≤ right) (shift : Rational) :
    shift - right ≤ shift - left :=
  sub_le_sub_direct le_rfl lessEqual

/-- Absolute value is nonnegative on the canonical carrier, with the sign
split performed explicitly. -/
theorem abs_nonneg_direct (source : Rational) : 0 ≤ |source| := by
  by_cases nonnegative : 0 ≤ source
  · simpa only [abs_of_nonneg nonnegative] using nonnegative
  · have nonpositive : source ≤ 0 :=
      le_of_not_gt_direct fun positive => nonnegative positive.le
    rw [abs_of_nonpos nonpositive]
    exact neg_le_neg_direct nonpositive

theorem neg_le_neg_iff_direct (left right : Rational) :
    -left ≤ -right ↔ right ≤ left := by
  constructor
  · intro lessEqual
    have reversed := neg_le_neg_direct lessEqual
    simpa only [neg_neg] using reversed
  · exact neg_le_neg_direct

theorem add_lt_add_direct {first second third fourth : Rational}
    (firstSecond : first < second) (thirdFourth : third < fourth) :
    first + third < second + fourth :=
  (add_lt_add_right_direct firstSecond third).trans
    (add_lt_add_left_direct thirdFourth second)

theorem lt_of_add_lt_add_right_direct {a b c : Rational}
    (less : a + c < b + c) : a < b := by
  have translated := add_lt_add_right_direct less (-c)
  simpa only [add_assoc, add_neg_cancel_right] using translated

theorem natCast_pos_direct {n : Nat} (hn : 0 < n) :
    (0 : Rational) < (n : Rational) := by
  rw [RFAP.CanonicalFraction.zero_lt_iff_num_pos,
    RFAP.CanonicalFraction.natCast_eq_fromInt]
  exact Int.ofNat_lt.mpr hn

theorem natCast_lt_direct {m n : Nat} (hmn : m < n) :
    (m : Rational) < (n : Rational) := by
  rw [RFAP.CanonicalFraction.lt_iff_cross,
    RFAP.CanonicalFraction.natCast_eq_fromInt,
    RFAP.CanonicalFraction.natCast_eq_fromInt]
  simpa only [RFAP.CanonicalFraction.fromInt, Int.natCast_one,
    Int.mul_one] using Int.ofNat_lt.mpr hmn

theorem natCast_le_direct {m n : Nat} (hmn : m ≤ n) :
    (m : Rational) ≤ (n : Rational) := by
  change
    (m : Rational).num * ((n : Rational).den : Int) ≤
      (n : Rational).num * ((m : Rational).den : Int)
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt,
    RFAP.CanonicalFraction.natCast_eq_fromInt]
  simpa only [RFAP.CanonicalFraction.fromInt, Int.natCast_one,
    Int.mul_one] using Int.ofNat_le.mpr hmn

theorem natCast_injective_direct {left right : Nat}
    (equal : (left : Rational) = (right : Rational)) : left = right :=
  RFAP.CanonicalFraction.natCast_injective_direct equal

theorem natCast_lt_iff_direct {left right : Nat} :
    (left : Rational) < (right : Rational) ↔ left < right := by
  constructor
  · intro less
    rw [RFAP.CanonicalFraction.lt_iff_cross,
      RFAP.CanonicalFraction.natCast_eq_fromInt,
      RFAP.CanonicalFraction.natCast_eq_fromInt] at less
    simpa only [RFAP.CanonicalFraction.fromInt, Int.natCast_one,
      Int.mul_one, Int.ofNat_lt] using less
  · exact natCast_lt_direct

theorem natCast_le_iff_direct {left right : Nat} :
    (left : Rational) ≤ (right : Rational) ↔ left ≤ right := by
  constructor
  · intro lessEqual
    change
      (left : Rational).num * ((right : Rational).den : Int) ≤
        (right : Rational).num * ((left : Rational).den : Int) at lessEqual
    rw [RFAP.CanonicalFraction.natCast_eq_fromInt,
      RFAP.CanonicalFraction.natCast_eq_fromInt] at lessEqual
    simpa only [RFAP.CanonicalFraction.fromInt, Int.natCast_one,
      Int.mul_one, Int.ofNat_le] using lessEqual
  · exact natCast_le_direct

theorem intCast_injective_direct {left right : Int}
    (equal : (left : Rational) = (right : Rational)) : left = right :=
  RFAP.CanonicalFraction.intCast_injective_direct equal

/-- Strict integer comparison is preserved by the denominator-one embedding. -/
theorem intCast_lt_direct {left right : Int} (less : left < right) :
    (left : Rational) < (right : Rational) := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.lt_iff_cross]
  simpa only [RFAP.CanonicalFraction.fromInt, Int.natCast_one,
    Int.mul_one] using less

theorem intCast_le_intCast_iff_direct (left right : Int) :
    (left : Rational) ≤ (right : Rational) ↔ left ≤ right := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt]
  change left * 1 ≤ right * 1 ↔ left ≤ right
  simp only [Int.mul_one]

/-- Positivity of a product from the stored canonical numerators. -/
theorem mul_pos_direct {left right : Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < left * right := by
  rw [RFAP.CanonicalFraction.zero_lt_iff_num_pos] at leftPositive rightPositive ⊢
  exact (RFAP.CanonicalFraction.numerator_pos_iff_of_equivalent
    (RFAP.CanonicalFraction.mul_equivalent left right)).mpr
      (Int.mul_pos leftPositive rightPositive)

theorem mul_lt_mul_of_pos_left_direct {a b c : Rational}
    (ha : 0 < a) (less : b < c) :
    a * b < a * c := by
  apply lt_of_sub_pos_direct
  have differencePositive := mul_pos_direct ha (sub_pos_direct less)
  have identity : a * c - a * b = a * (c - b) := by
    rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct]
    rw [_root_.mul_add, _root_.mul_neg]
  rw [identity]
  exact differencePositive

theorem mul_lt_mul_of_pos_right_direct {a b c : Rational}
    (less : a < b) (hc : 0 < c) :
    a * c < b * c := by
  simpa only [mul_comm c] using
    mul_lt_mul_of_pos_left_direct hc less

theorem mul_pos_of_neg_of_neg_direct {left right : Rational}
    (leftNegative : left < 0) (rightNegative : right < 0) :
    0 < left * right := by
  have positive := mul_pos_direct (neg_pos.mpr leftNegative)
    (neg_pos.mpr rightNegative)
  simpa only [neg_mul_neg] using positive

theorem mul_neg_of_neg_of_pos_direct {left right : Rational}
    (leftNegative : left < 0) (rightPositive : 0 < right) :
    left * right < 0 := by
  have positive := mul_pos_direct (neg_pos.mpr leftNegative) rightPositive
  rw [_root_.neg_mul] at positive
  exact neg_pos.mp positive

theorem mul_neg_of_pos_of_neg_direct {left right : Rational}
    (leftPositive : 0 < left) (rightNegative : right < 0) :
    left * right < 0 := by
  rw [mul_comm]
  exact mul_neg_of_neg_of_pos_direct rightNegative leftPositive

theorem pos_of_mul_pos_right_direct {left right : Rational}
    (productPositive : 0 < left * right) (leftNonnegative : 0 ≤ left) :
    0 < right := by
  rcases lt_trichotomy right 0 with rightNegative | rightZero | rightPositive
  · rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
    · exact (not_lt_of_ge leftNonnegative leftNegative).elim
    · rw [leftZero, zero_mul] at productPositive
      exact (lt_irrefl 0 productPositive).elim
    · have productNegative :=
        mul_neg_of_pos_of_neg_direct leftPositive rightNegative
      exact (lt_asymm productPositive productNegative).elim
  · rw [rightZero, mul_zero] at productPositive
    exact (lt_irrefl 0 productPositive).elim
  · exact rightPositive

instance instPosMulStrictMono : PosMulStrictMono Rational where
  mul_lt_mul_of_pos_left := fun {factor} factorPositive {left right} less =>
    mul_lt_mul_of_pos_left_direct
      (a := factor) (b := left) (c := right) factorPositive less

instance instMulPosStrictMono : MulPosStrictMono Rational where
  mul_lt_mul_of_pos_right := fun {factor} factorPositive {left right} less =>
    mul_lt_mul_of_pos_right_direct
      (a := left) (b := right) (c := factor) less factorPositive

instance instNontrivial : Nontrivial Rational :=
  ⟨⟨0, 1, zero_ne_one⟩⟩

instance instIsStrictOrderedRing : IsStrictOrderedRing Rational where

theorem mul_nonneg_direct {left right : Rational}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    0 ≤ left * right := by
  by_cases leftZero : left = 0
  · rw [leftZero, zero_mul]
  · by_cases rightZero : right = 0
    · rw [rightZero, mul_zero]
    · have leftPositive : 0 < left :=
        ⟨leftNonnegative, fun reverse => leftZero
          (RFAP.CanonicalFraction.le_antisymm left 0 reverse leftNonnegative)⟩
      have rightPositive : 0 < right :=
        ⟨rightNonnegative, fun reverse => rightZero
          (RFAP.CanonicalFraction.le_antisymm right 0 reverse rightNonnegative)⟩
      exact (mul_pos_direct leftPositive rightPositive).le

theorem mul_le_mul_of_nonneg_right_direct {a b c : Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  by_cases factorZero : c = 0
  · rw [factorZero, mul_zero, mul_zero]
  · have factorPositive : 0 < c :=
      ⟨hc, fun reverse => factorZero
        (RFAP.CanonicalFraction.le_antisymm c 0 reverse hc)⟩
    by_cases equal : a = b
    · rw [equal]
    · exact (mul_lt_mul_of_pos_right_direct
        ⟨hab, fun reverse => equal
          (RFAP.CanonicalFraction.le_antisymm a b hab reverse)⟩
        factorPositive).le

theorem mul_le_mul_of_nonneg_left_direct {a b c : Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  simpa only [mul_comm c] using
    mul_le_mul_of_nonneg_right_direct hab hc

theorem sq_nonneg_direct (source : Rational) : 0 ≤ source ^ 2 := by
  by_cases sourceNonnegative : 0 ≤ source
  · simpa only [pow_two] using
      mul_nonneg_direct sourceNonnegative sourceNonnegative
  · have sourceNegative : source < 0 :=
      lt_of_not_ge_direct sourceNonnegative
    exact (by
      simpa only [pow_two] using
        (mul_pos_of_neg_of_neg_direct sourceNegative sourceNegative).le)

theorem sq_eq_zero_direct (source : Rational) : source ^ 2 = 0 ↔ source = 0 := by
  constructor
  · intro squareZero
    by_cases sourceZero : source = 0
    · exact sourceZero
    · have productNonzero :=
        RFAP.CanonicalFraction.mul_ne_zero sourceZero sourceZero
      exact (productNonzero (by simpa only [pow_two] using squareZero)).elim
  · intro sourceZero
    rw [sourceZero]
    rfl

theorem pow_nonneg_direct {source : Rational} (nonnegative : 0 ≤ source) :
    ∀ exponent : Nat, 0 ≤ source ^ exponent
  | 0 => by
      change (0 : Rational) ≤ 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_nonneg_direct (pow_nonneg_direct nonnegative exponent)
        nonnegative

theorem pow_pos_direct {source : Rational} (positive : 0 < source) :
    ∀ exponent : Nat, 0 < source ^ exponent
  | 0 => by
      change (0 : Rational) < 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_pos_direct (pow_pos_direct positive exponent) positive

theorem mul_le_mul_direct {first second third fourth : Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth)
    (thirdNonnegative : 0 ≤ third) (secondNonnegative : 0 ≤ second) :
    first * third ≤ second * fourth :=
  (mul_le_mul_of_nonneg_right_direct firstSecond thirdNonnegative).trans
    (mul_le_mul_of_nonneg_left_direct thirdFourth secondNonnegative)

theorem pow_le_pow_direct {left right : Rational}
    (leftNonnegative : 0 ≤ left) (lessEqual : left ≤ right) :
    ∀ exponent : Nat, left ^ exponent ≤ right ^ exponent
  | 0 => le_rfl
  | exponent + 1 => by
      rw [pow_succ, pow_succ]
      exact mul_le_mul_direct
        (pow_le_pow_direct leftNonnegative lessEqual exponent) lessEqual
        leftNonnegative
        (pow_nonneg_direct (leftNonnegative.trans lessEqual) exponent)

/-! ## Inversion, division, and integer bounds -/

abbrev add := RFAP.CanonicalFraction.add
abbrev neg := RFAP.CanonicalFraction.neg
abbrev mul := RFAP.CanonicalFraction.mul
abbrev inv := RFAP.CanonicalFraction.inv
abbrev le := RFAP.CanonicalFraction.LessEqual

def lessEqual (left right : Rational) : Bool := decide (left ≤ right)

theorem lessEqual_eq_true_iff (left right : Rational) :
    lessEqual left right = true ↔ left ≤ right := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

theorem mul_zero_direct (source : Rational) : source * 0 = 0 :=
  mul_zero source

theorem zero_mul_direct (source : Rational) : 0 * source = 0 :=
  zero_mul source

theorem mul_one_direct (source : Rational) : source * 1 = source :=
  _root_.mul_one source

theorem div_zero_direct (source : Rational) : source / 0 = 0 := by
  change source * (0 : Rational)⁻¹ = 0
  rw [inv_zero, mul_zero_direct]

theorem zero_div_direct (source : Rational) : 0 / source = 0 := by
  change 0 * source⁻¹ = 0
  exact zero_mul_direct _

theorem inv_mul_cancel (source : Rational) (nonzero : source ≠ 0) :
    source⁻¹ * source = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel source nonzero

theorem mul_ne_zero_direct {left right : Rational}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 :=
  RFAP.CanonicalFraction.mul_ne_zero leftNonzero rightNonzero

theorem inv_ne_zero_direct {source : Rational} (nonzero : source ≠ 0) :
    source⁻¹ ≠ 0 :=
  RFAP.CanonicalFraction.inv_ne_zero nonzero

theorem inv_neg_direct (source : Rational) : inv (-source) = -inv source :=
  RFAP.CanonicalFraction.inv_neg source

theorem div_eq_mul_inv_direct (left right : Rational) :
    left / right = left * right⁻¹ := rfl

theorem div_mul_cancel_of_ne (numerator denominator : Rational)
    (denominatorNonzero : denominator ≠ 0) :
    (numerator / denominator) * denominator = numerator := by
  change (numerator * denominator⁻¹) * denominator = numerator
  calc
    (numerator * denominator⁻¹) * denominator =
        numerator * (denominator⁻¹ * denominator) := mul_assoc _ _ _
    _ = numerator * 1 := by rw [inv_mul_cancel denominator denominatorNonzero]
    _ = numerator := mul_one_direct _

/-- Two divisions with nonzero denominators agree when their displayed
cross-products agree.  This is the direct certificate form of equality of
fractions; it does not compare quotient representatives. -/
theorem div_eq_div_of_cross_mul {firstNumerator firstDenominator
    secondNumerator secondDenominator : Rational}
    (firstDenominatorNonzero : firstDenominator ≠ 0)
    (secondDenominatorNonzero : secondDenominator ≠ 0)
    (crossProduct :
      firstNumerator * secondDenominator =
        secondNumerator * firstDenominator) :
    firstNumerator / firstDenominator =
      secondNumerator / secondDenominator := by
  have productNonzero :
      firstDenominator * secondDenominator ≠ 0 :=
    mul_ne_zero_direct firstDenominatorNonzero secondDenominatorNonzero
  apply RFAP.CanonicalFraction.mul_left_cancel_of_nonzero productNonzero
  calc
    (firstDenominator * secondDenominator) *
          (firstNumerator / firstDenominator) =
        (firstNumerator / firstDenominator) *
          (firstDenominator * secondDenominator) := by ring1
    _ = ((firstNumerator / firstDenominator) * firstDenominator) *
          secondDenominator := by rw [mul_assoc]
    _ = firstNumerator * secondDenominator := by
      rw [div_mul_cancel_of_ne _ _ firstDenominatorNonzero]
    _ = secondNumerator * firstDenominator := crossProduct
    _ = ((secondNumerator / secondDenominator) * secondDenominator) *
          firstDenominator := by
      rw [div_mul_cancel_of_ne _ _ secondDenominatorNonzero]
    _ = (firstDenominator * secondDenominator) *
          (secondNumerator / secondDenominator) := by ring1

theorem mul_right_cancel_of_ne {a b c : Rational}
    (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have scaled := congrArg (fun value => value * c⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel c hc,
    mul_one_direct] using scaled

theorem le_of_mul_le_mul_right_direct {a b c : Rational}
    (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  by_cases lessEqual : a ≤ b
  · exact lessEqual
  · have reverse : b ≤ a :=
      (RFAP.CanonicalFraction.le_total b a).resolve_right lessEqual
    have strictScaled : b * c < a * c :=
      mul_lt_mul_of_pos_right_direct ⟨reverse, lessEqual⟩ hc
    exact ((not_lt_of_ge h) strictScaled).elim

theorem lt_of_mul_lt_mul_right_direct {a b c : Rational}
    (h : a * c < b * c) (hc : 0 < c) :
    a < b := by
  by_cases less : a < b
  · exact less
  · have reverse : b ≤ a := le_of_not_gt_direct less
    have reverseScaled :=
      mul_le_mul_of_nonneg_right_direct reverse hc.le
    exact ((not_lt_of_ge reverseScaled) h).elim

theorem le_of_sq_le_sq_direct {source bound : Rational}
    (boundNonnegative : 0 ≤ bound)
    (squares : source ^ 2 ≤ bound ^ 2) : source ≤ bound := by
  by_cases direct : source ≤ bound
  · exact direct
  · have boundLess : bound < source := lt_of_not_ge_direct direct
    have sourcePositive : 0 < source := boundNonnegative.trans_lt boundLess
    have first : bound * bound ≤ bound * source :=
      mul_le_mul_of_nonneg_left_direct boundLess.le boundNonnegative
    have second : bound * source < source * source :=
      mul_lt_mul_of_pos_right_direct boundLess sourcePositive
    have squareLess : bound ^ 2 < source ^ 2 := by
      simpa only [pow_two] using first.trans_lt second
    exact ((not_lt_of_ge squares) squareLess).elim

theorem neg_le_of_sq_le_sq_direct {source bound : Rational}
    (boundNonnegative : 0 ≤ bound)
    (squares : source ^ 2 ≤ bound ^ 2) : -bound ≤ source := by
  have negativeSquares : (-source) ^ 2 ≤ bound ^ 2 := by
    have identity : (-source) ^ 2 = source ^ 2 := by
      simp only [pow_two, neg_mul_neg]
    rw [identity]
    exact squares
  have upper : -source ≤ bound :=
    le_of_sq_le_sq_direct boundNonnegative negativeSquares
  have reversed := neg_le_neg_direct upper
  simpa only [neg_neg] using reversed

theorem div_le_iff_pos {left right denominator : Rational}
    (denominatorPositive : 0 < denominator) :
    left / denominator ≤ right ↔ left ≤ right * denominator := by
  constructor
  · intro lessEqual
    have scaled := mul_le_mul_of_nonneg_right_direct lessEqual
      denominatorPositive.le
    rwa [div_mul_cancel_of_ne left denominator denominatorPositive.ne'] at scaled
  · intro lessEqual
    apply le_of_mul_le_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [div_mul_cancel_of_ne left denominator denominatorPositive.ne']

theorem le_div_iff_pos {left right denominator : Rational}
    (denominatorPositive : 0 < denominator) :
    left ≤ right / denominator ↔ left * denominator ≤ right := by
  constructor
  · intro lessEqual
    have scaled := mul_le_mul_of_nonneg_right_direct lessEqual
      denominatorPositive.le
    rwa [div_mul_cancel_of_ne right denominator denominatorPositive.ne'] at scaled
  · intro lessEqual
    apply le_of_mul_le_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [div_mul_cancel_of_ne right denominator denominatorPositive.ne']

theorem div_lt_iff_pos {left right denominator : Rational}
    (denominatorPositive : 0 < denominator) :
    left / denominator < right ↔ left < right * denominator := by
  constructor
  · intro less
    have scaled := mul_lt_mul_of_pos_right_direct less denominatorPositive
    rwa [div_mul_cancel_of_ne left denominator denominatorPositive.ne'] at scaled
  · intro less
    apply lt_of_mul_lt_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [div_mul_cancel_of_ne left denominator denominatorPositive.ne']

theorem lt_div_iff_pos {left right denominator : Rational}
    (denominatorPositive : 0 < denominator) :
    left < right / denominator ↔ left * denominator < right := by
  constructor
  · intro less
    have scaled := mul_lt_mul_of_pos_right_direct less denominatorPositive
    rwa [div_mul_cancel_of_ne right denominator denominatorPositive.ne'] at scaled
  · intro less
    apply lt_of_mul_lt_mul_right_direct (c := denominator) _
      denominatorPositive
    rwa [div_mul_cancel_of_ne right denominator denominatorPositive.ne']

theorem inv_pos_direct {source : Rational} (positive : 0 < source) :
    0 < source⁻¹ := by
  have productPositive : 0 < source * source⁻¹ := by
    rw [mul_inv_cancel source positive.ne']
    decide
  exact pos_of_mul_pos_right_direct productPositive positive.le

theorem inv_le_inv_of_pos_direct {left right : Rational}
    (leftPositive : 0 < left) (lessEqual : left ≤ right) :
    right⁻¹ ≤ left⁻¹ := by
  have rightPositive : 0 < right := leftPositive.trans_le lessEqual
  apply le_of_mul_le_mul_right_direct (c := left) _ leftPositive
  calc
    right⁻¹ * left ≤ right⁻¹ * right :=
      mul_le_mul_of_nonneg_left_direct lessEqual (inv_pos_direct rightPositive).le
    _ = 1 := inv_mul_cancel right rightPositive.ne'
    _ = left⁻¹ * left := (inv_mul_cancel left leftPositive.ne').symm

theorem div_pos_direct {numerator denominator : Rational}
    (numeratorPositive : 0 < numerator)
    (denominatorPositive : 0 < denominator) :
    0 < numerator / denominator := by
  change 0 < numerator * denominator⁻¹
  exact mul_pos_direct numeratorPositive (inv_pos_direct denominatorPositive)

theorem div_nonneg_direct {numerator denominator : Rational}
    (numeratorNonnegative : 0 ≤ numerator)
    (denominatorNonnegative : 0 ≤ denominator) :
    0 ≤ numerator / denominator := by
  by_cases numeratorZero : numerator = 0
  · rw [numeratorZero, zero_div_direct]
  · by_cases denominatorZero : denominator = 0
    · rw [denominatorZero, div_zero_direct]
    · exact (div_pos_direct
        ⟨numeratorNonnegative, fun reverse => numeratorZero
          (RFAP.CanonicalFraction.le_antisymm numerator 0
            reverse numeratorNonnegative)⟩
        ⟨denominatorNonnegative, fun reverse => denominatorZero
          (RFAP.CanonicalFraction.le_antisymm denominator 0
            reverse denominatorNonnegative)⟩).le

theorem div_le_div_of_nonneg_left_direct {numerator left right : Rational}
    (numeratorNonnegative : 0 ≤ numerator)
    (leftPositive : 0 < left) (lessEqual : left ≤ right) :
    numerator / right ≤ numerator / left := by
  change numerator * right⁻¹ ≤ numerator * left⁻¹
  exact mul_le_mul_of_nonneg_left_direct
    (inv_le_inv_of_pos_direct leftPositive lessEqual)
    numeratorNonnegative

theorem inv_mul_direct (left right : Rational) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  by_cases leftZero : left = 0
  · subst left
    rw [zero_mul_direct, inv_zero, zero_mul_direct]
  · by_cases rightZero : right = 0
    · subst right
      rw [mul_zero_direct, inv_zero, mul_zero_direct]
    · have productNonzero := mul_ne_zero_direct leftZero rightZero
      apply mul_right_cancel_of_ne productNonzero
      calc
        (left * right)⁻¹ * (left * right) = 1 :=
          inv_mul_cancel _ productNonzero
        _ = (left⁻¹ * left) * (right⁻¹ * right) := by
          rw [inv_mul_cancel left leftZero, inv_mul_cancel right rightZero,
            mul_one_direct]
        _ = (left⁻¹ * right⁻¹) * (left * right) :=
          mul_pair_swap _ _ _ _

theorem inv_pow_direct (source : Rational) : ∀ exponent : Nat,
    (source ^ exponent)⁻¹ = source⁻¹ ^ exponent
  | 0 => by
      change (1 : Rational)⁻¹ = 1
      decide
  | exponent + 1 => by
      rw [pow_succ, inv_mul_direct, inv_pow_direct source exponent, pow_succ]

theorem div_mul_div_direct (first second third fourth : Rational) :
    (first / second) * (third / fourth) =
      (first * third) / (second * fourth) := by
  change (first * second⁻¹) * (third * fourth⁻¹) =
    (first * third) * (second * fourth)⁻¹
  rw [inv_mul_direct]
  exact mul_pair_swap _ _ _ _

theorem div_sub_div_direct (first second third fourth : Rational)
    (secondNonzero : second ≠ 0) (fourthNonzero : fourth ≠ 0) :
    first / second - third / fourth =
      (first * fourth - third * second) / (second * fourth) := by
  change first * second⁻¹ - third * fourth⁻¹ =
    (first * fourth - third * second) * (second * fourth)⁻¹
  rw [inv_mul_direct]
  rw [sub_eq_add_neg_direct, sub_eq_add_neg_direct, _root_.add_mul,
    _root_.neg_mul]
  have firstReorder :
      (first * fourth) * (second⁻¹ * fourth⁻¹) =
        first * second⁻¹ := by
    calc
      (first * fourth) * (second⁻¹ * fourth⁻¹) =
          (first * second⁻¹) * (fourth * fourth⁻¹) :=
        mul_pair_swap _ _ _ _
      _ = (first * second⁻¹) * 1 := by
        rw [mul_inv_cancel fourth fourthNonzero]
      _ = first * second⁻¹ := mul_one_direct _
  have secondReorder :
      (third * second) * (second⁻¹ * fourth⁻¹) =
        third * fourth⁻¹ := by
    calc
      (third * second) * (second⁻¹ * fourth⁻¹) =
          (third * fourth⁻¹) * (second * second⁻¹) := by
        rw [mul_comm second⁻¹ fourth⁻¹]
        exact mul_pair_swap _ _ _ _
      _ = (third * fourth⁻¹) * 1 := by
        rw [mul_inv_cancel second secondNonzero]
      _ = third * fourth⁻¹ := mul_one_direct _
  rw [firstReorder, secondReorder]

theorem mul_div_mul_left_direct (factor numerator denominator : Rational)
    (factorNonzero : factor ≠ 0) :
    (factor * numerator) / (factor * denominator) =
      numerator / denominator := by
  change (factor * numerator) * (factor * denominator)⁻¹ =
    numerator * denominator⁻¹
  rw [inv_mul_direct]
  calc
    (factor * numerator) * (factor⁻¹ * denominator⁻¹) =
        (factor * factor⁻¹) * (numerator * denominator⁻¹) :=
      mul_pair_swap _ _ _ _
    _ = 1 * (numerator * denominator⁻¹) := by
      rw [mul_inv_cancel factor factorNonzero]
    _ = numerator * denominator⁻¹ := one_mul _

/-- The Euclidean floor of the stored reduced display. -/
def floor (source : Rational) : Int := source.num / (source.den : Int)

theorem intCast_le_iff_floor (integer : Int) (source : Rational) :
    (integer : Rational) ≤ source ↔ integer ≤ floor source := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt]
  change integer * (source.den : Int) ≤ source.num * 1 ↔
    integer ≤ source.num / (source.den : Int)
  rw [Int.mul_one]
  exact (Int.le_ediv_iff_mul_le (Int.natCast_pos.mpr source.den_pos)).symm

def ceil (source : Rational) : Int := -floor (-source)

theorem ceil_le_intCast_iff (source : Rational) (integer : Int) :
    ceil source ≤ integer ↔ source ≤ (integer : Rational) := by
  rw [ceil]
  constructor
  · intro lessEqual
    have negativeInteger : (-integer : Int) ≤ floor (-source) := by
      simpa only [Int.neg_neg] using Int.neg_le_neg_iff.mpr lessEqual
    have castComparison :=
      (intCast_le_iff_floor (-integer) (-source)).mpr negativeInteger
    rw [Int.cast_neg] at castComparison
    exact (neg_le_neg_iff_direct (integer : Rational) source).mp
      castComparison
  · intro lessEqual
    have negativeComparison : ((-integer : Int) : Rational) ≤ -source := by
      rw [Int.cast_neg]
      exact (neg_le_neg_iff_direct (integer : Rational) source).mpr
        lessEqual
    have floorComparison :=
      (intCast_le_iff_floor (-integer) (-source)).mp negativeComparison
    simpa only [Int.neg_neg] using Int.neg_le_neg_iff.mpr floorComparison

theorem le_intCast_ceil (source : Rational) :
    source ≤ (ceil source : Rational) :=
  (ceil_le_intCast_iff source (ceil source)).mp le_rfl

def ceilNat (source : Rational) : Nat := (ceil source).toNat

theorem le_natCast_ceilNat_of_nonneg {source : Rational}
    (nonnegative : 0 ≤ source) : source ≤ (ceilNat source : Nat) := by
  have castNonnegative : (0 : Rational) ≤ (ceil source : Rational) :=
    nonnegative.trans (le_intCast_ceil source)
  have ceilingNonnegative : (0 : Int) ≤ ceil source :=
    (intCast_le_intCast_iff_direct 0 (ceil source)).mp (by
      simpa only [Int.cast_zero] using castNonnegative)
  have ceilingCast : ((ceil source).toNat : Int) = ceil source :=
    Int.toNat_of_nonneg ceilingNonnegative
  calc
    source ≤ (ceil source : Rational) := le_intCast_ceil source
    _ = (((ceil source).toNat : Int) : Rational) :=
      (congrArg (fun value : Int => (value : Rational)) ceilingCast).symm
    _ = (((ceil source).toNat : Nat) : Rational) := by rw [Int.cast_natCast]
    _ = (ceilNat source : Nat) := rfl

/-! ## Canonical finite representatives -/

/-- Reduced finite data is the semantic carrier itself. -/
abbrev ReducedFraction := Rational

namespace ReducedFraction

/-- Re-embed a canonical value in the compatibility input syntax. -/
def toFraction (fraction : ReducedFraction) : Fraction :=
  ⟨fraction.num, (fraction.den : Int),
    Int.natCast_pos.mpr fraction.den_pos⟩

/-- Compatibility normalization is canonical normalization. -/
def normalize (fraction : Fraction) : ReducedFraction :=
  ofFraction fraction

theorem normalize_equivalent (fraction : Fraction) :
    Equivalent (normalize fraction).toFraction fraction := by
  have canonicalEquivalent := RFAP.CanonicalFraction.normalize_equivalent fraction.toRaw
  change
    (RFAP.CanonicalFraction.normalize fraction.toRaw).num * fraction.den =
      fraction.num * (RFAP.CanonicalFraction.normalize fraction.toRaw).den
  have denominatorCast : (fraction.den.toNat : Int) = fraction.den :=
    Int.toNat_of_nonneg fraction.den_pos.le
  simpa only [RFAP.CanonicalFraction.Equivalent, RFAP.CanonicalFraction.Rational.toRaw,
    Fraction.toRaw, denominatorCast] using canonicalEquivalent

theorem normalize_respects {left right : Fraction}
    (equivalent : Equivalent left right) :
    normalize left = normalize right :=
  ofFraction_eq_of_equivalent equivalent

end ReducedFraction

/-- Comparing normalized compatibility displays is exactly their explicit
positive-denominator cross-product comparison. -/
theorem ofFraction_le_iff (left right : Fraction) :
    ofFraction left ≤ ofFraction right ↔ LessEqFraction left right := by
  change
    LessEqFraction (ReducedFraction.toFraction (ofFraction left))
      (ReducedFraction.toFraction (ofFraction right)) ↔
        LessEqFraction left right
  exact lessEqFraction_congr
    (ReducedFraction.normalize_equivalent left)
    (ReducedFraction.normalize_equivalent right)

/-- Canonical rationals already carry their reduced representative. -/
def representative (value : Rational) : ReducedFraction := value

theorem representative_spec (value : Rational) :
    ofFraction (representative value).toFraction = value := by
  change RFAP.CanonicalFraction.normalize
    ⟨value.num, Int.toNat (value.den : Int),
      toNat_pos_direct (Int.natCast_pos.mpr value.den_pos)⟩ = value
  have displayEqual :
      (⟨value.num, Int.toNat (value.den : Int),
        toNat_pos_direct (Int.natCast_pos.mpr value.den_pos)⟩ :
        RFAP.CanonicalFraction.RawFraction) = value.toRaw := by
    cases value with
    | mk num den den_pos reduced =>
        simp only [RFAP.CanonicalFraction.Rational.toRaw,
          Int.toNat_natCast]
  rw [displayEqual, RFAP.CanonicalFraction.normalize_idempotent]

theorem representative_of_reduced (reduced : ReducedFraction) :
    representative (ofFraction reduced.toFraction) = reduced :=
  representative_spec reduced

/-- Rebuilding a canonical rational is definitionally just the same value. -/
def canonical (value : Rational) : Rational := representative value

theorem canonical_eq (value : Rational) : canonical value = value := rfl

/-- Addition of two compatibility displays agrees with addition of their
canonical values.  The result is justified by the displayed raw
cross-products, rather than quotient soundness. -/
theorem ofFraction_addFraction (left right : Fraction) :
    ofFraction left + ofFraction right =
      ofFraction (addFraction left right) := by
  apply RFAP.CanonicalFraction.eq_of_equivalent
  have sumDisplay := RFAP.CanonicalFraction.add_plain
    (ofFraction left) (ofFraction right)
  have leftNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction left).toRaw left.toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent left.toRaw
  have rightNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction right).toRaw right.toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent right.toRaw
  have replacedInputs := RFAP.CanonicalFraction.plainAddRaw_respects
    leftNormalized rightNormalized
  have displayedSum : RFAP.CanonicalFraction.Equivalent
      (RFAP.CanonicalFraction.plainAddRaw left.toRaw right.toRaw)
      (addFraction left right).toRaw := by
    have leftDenominator : (left.den.toNat : Int) = left.den :=
      Int.toNat_of_nonneg left.den_pos.le
    have rightDenominator : (right.den.toNat : Int) = right.den :=
      Int.toNat_of_nonneg right.den_pos.le
    have sumDenominator : ((left.den * right.den).toNat : Int) =
        left.den * right.den :=
      Int.toNat_of_nonneg (Int.mul_nonneg left.den_pos.le right.den_pos.le)
    dsimp only [RFAP.CanonicalFraction.Equivalent,
      RFAP.CanonicalFraction.plainAddRaw, Fraction.toRaw, addFraction]
    simp only [Int.natCast_mul, leftDenominator, rightDenominator,
      sumDenominator]
  have resultNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction (addFraction left right)).toRaw
      (addFraction left right).toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent (addFraction left right).toRaw
  exact RFAP.CanonicalFraction.equivalent_trans sumDisplay
    (RFAP.CanonicalFraction.equivalent_trans replacedInputs
      (RFAP.CanonicalFraction.equivalent_trans displayedSum
        resultNormalized.symm))

/-- Multiplication of two compatibility displays agrees with multiplication
of their canonical values.  The result is justified by the displayed raw
cross-products, rather than quotient soundness. -/
theorem ofFraction_mulFraction (left right : Fraction) :
    ofFraction left * ofFraction right =
      ofFraction (mulFraction left right) := by
  apply RFAP.CanonicalFraction.eq_of_equivalent
  have productDisplay := RFAP.CanonicalFraction.mul_plain
    (ofFraction left) (ofFraction right)
  have leftNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction left).toRaw left.toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent left.toRaw
  have rightNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction right).toRaw right.toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent right.toRaw
  have replacedInputs := RFAP.CanonicalFraction.plainMulRaw_respects
    leftNormalized rightNormalized
  have displayedProduct : RFAP.CanonicalFraction.Equivalent
      (RFAP.CanonicalFraction.plainMulRaw left.toRaw right.toRaw)
      (mulFraction left right).toRaw := by
    have leftDenominator : (left.den.toNat : Int) = left.den :=
      Int.toNat_of_nonneg left.den_pos.le
    have rightDenominator : (right.den.toNat : Int) = right.den :=
      Int.toNat_of_nonneg right.den_pos.le
    have productDenominator : ((left.den * right.den).toNat : Int) =
        left.den * right.den :=
      Int.toNat_of_nonneg (Int.mul_nonneg left.den_pos.le right.den_pos.le)
    dsimp only [RFAP.CanonicalFraction.Equivalent,
      RFAP.CanonicalFraction.plainMulRaw, Fraction.toRaw, mulFraction]
    simp only [Int.natCast_mul, leftDenominator, rightDenominator,
      productDenominator]
  have resultNormalized : RFAP.CanonicalFraction.Equivalent
      (ofFraction (mulFraction left right)).toRaw
      (mulFraction left right).toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent (mulFraction left right).toRaw
  exact RFAP.CanonicalFraction.equivalent_trans productDisplay
    (RFAP.CanonicalFraction.equivalent_trans replacedInputs
      (RFAP.CanonicalFraction.equivalent_trans displayedProduct
        resultNormalized.symm))

/-- Multiplication by a displayed positive denominator recovers the displayed
integer numerator, after normalization of the input syntax. -/
theorem ofFraction_mul_den (fraction : Fraction) :
    ofFraction fraction * (fraction.den : Rational) =
      (fraction.num : Rational) := by
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt]
  apply RFAP.CanonicalFraction.eq_of_equivalent
  have productDisplay := RFAP.CanonicalFraction.mul_plain
    (ofFraction fraction) (RFAP.CanonicalFraction.fromInt fraction.den)
  have normalizedInput : RFAP.CanonicalFraction.Equivalent
      (ofFraction fraction).toRaw fraction.toRaw :=
    RFAP.CanonicalFraction.normalize_equivalent fraction.toRaw
  have replacedInput := RFAP.CanonicalFraction.plainMulRaw_respects
    normalizedInput
    (RFAP.CanonicalFraction.equivalent_refl
      (RFAP.CanonicalFraction.fromInt fraction.den).toRaw)
  have denominatorCast : (fraction.den.toNat : Int) = fraction.den :=
    Int.toNat_of_nonneg fraction.den_pos.le
  have plainResult : RFAP.CanonicalFraction.Equivalent
      (RFAP.CanonicalFraction.plainMulRaw fraction.toRaw
        (RFAP.CanonicalFraction.fromInt fraction.den).toRaw)
      (RFAP.CanonicalFraction.fromInt fraction.num).toRaw := by
    dsimp only [RFAP.CanonicalFraction.Equivalent,
      RFAP.CanonicalFraction.plainMulRaw, Fraction.toRaw,
      RFAP.CanonicalFraction.Rational.toRaw,
      RFAP.CanonicalFraction.fromInt]
    simp only [Int.natCast_one, Nat.mul_one, Int.mul_one, denominatorCast]
  exact RFAP.CanonicalFraction.equivalent_trans productDisplay
    (RFAP.CanonicalFraction.equivalent_trans replacedInput plainResult)

/-- A normalized compatibility display is its displayed numerator divided by
its positive displayed denominator. -/
theorem ofFraction_eq_div (fraction : Fraction) :
    ofFraction fraction =
      (fraction.num : Rational) / (fraction.den : Rational) := by
  have denominatorPositive : (0 : Rational) < fraction.den :=
    by
      rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
        RFAP.CanonicalFraction.zero_lt_iff_num_pos]
      exact fraction.den_pos
  apply mul_right_cancel_of_ne denominatorPositive.ne'
  calc
    ofFraction fraction * (fraction.den : Rational) =
        (fraction.num : Rational) := ofFraction_mul_den fraction
    _ = ((fraction.num : Rational) / (fraction.den : Rational)) *
          (fraction.den : Rational) :=
      (div_mul_cancel_of_ne _ _ denominatorPositive.ne').symm

/-- Multiplication by the stored canonical denominator recovers the stored
integer numerator. -/
theorem representative_mul_den (value : Rational) :
    value * ((representative value).den : Rational) =
      ((representative value).num : Rational) := by
  change value * (value.den : Rational) = (value.num : Rational)
  rw [RFAP.CanonicalFraction.natCast_eq_fromInt,
    RFAP.CanonicalFraction.intCast_eq_fromInt]
  apply RFAP.CanonicalFraction.eq_of_equivalent
  have productDisplay := RFAP.CanonicalFraction.mul_plain value
    (RFAP.CanonicalFraction.fromInt (value.den : Int))
  have plainResult : RFAP.CanonicalFraction.Equivalent
      (RFAP.CanonicalFraction.plainMulRaw value.toRaw
        (RFAP.CanonicalFraction.fromInt (value.den : Int)).toRaw)
      (RFAP.CanonicalFraction.fromInt value.num).toRaw := by
    dsimp only [RFAP.CanonicalFraction.Equivalent,
      RFAP.CanonicalFraction.plainMulRaw,
      RFAP.CanonicalFraction.Rational.toRaw,
      RFAP.CanonicalFraction.fromInt]
    simp only [Int.natCast_one, Nat.mul_one, Int.mul_one]
  exact RFAP.CanonicalFraction.equivalent_trans productDisplay plainResult

/-! ## A finite nonsquare certificate -/

private theorem two_dvd_of_two_dvd_square {value : Nat}
    (divides : 2 ∣ value * value) : 2 ∣ value := by
  rw [Nat.dvd_iff_mod_eq_zero] at divides ⊢
  have remainderLt : value % 2 < 2 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 2 = (value % 2) * (value % 2) % 2 := by
    rw [Nat.mul_mod]
  rw [squareRemainder] at divides
  cases remainderEq : value % 2 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rw [remainderEq] at divides
          exact ((by decide : (1 * 1 % 2 : Nat) ≠ 0) divides).elim
      | succ remainder =>
          rw [remainderEq] at remainderLt
          have twoLe : 2 ≤ Nat.succ (Nat.succ remainder) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le remainder))
          exact (Nat.not_lt_of_ge twoLe remainderLt).elim

/-- A reusable denominator-clearance argument: a displayed natural whose
divisibility is detected by its square cannot be a rational square class
unless it is one. -/
private theorem square_ne_nat_of_dvd_square (prime : Nat)
    (primePositive : 0 < prime) (primeNeOne : prime ≠ 1)
    (dvdSquare : ∀ {value : Nat}, prime ∣ value * value → prime ∣ value)
    (value : Rational) : value ^ 2 ≠ (prime : Rational) := by
  intro square
  let reduced := representative value
  have cleared := representative_mul_den value
  change value * (reduced.den : Rational) = (reduced.num : Rational) at cleared
  have rationalSquare :
      (reduced.num : Rational) ^ 2 =
        (prime : Rational) * (reduced.den : Rational) ^ 2 := by
    calc
      (reduced.num : Rational) ^ 2 =
          (value * (reduced.den : Rational)) ^ 2 := by rw [cleared]
      _ = value ^ 2 * (reduced.den : Rational) ^ 2 := by ring1
      _ = (prime : Rational) * (reduced.den : Rational) ^ 2 := by rw [square]
  have integerSquare :
      reduced.num * reduced.num =
        (prime : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    apply intCast_injective_direct
    rw [intCast_mul_direct, intCast_mul_direct, intCast_mul_direct]
    simpa only [Int.cast_natCast, pow_two] using rationalSquare
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        prime * (reduced.den * reduced.den) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absoluteSquare
  have primeDvdNumerator : prime ∣ reduced.num.natAbs :=
    dvdSquare ⟨reduced.den * reduced.den, naturalSquare⟩
  have numeratorDivides : prime ∣ reduced.num.natAbs := primeDvdNumerator
  rcases primeDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have denominatorSquare :
      reduced.den * reduced.den =
        prime * (numeratorFactor * numeratorFactor) := by
    have scaled :
        prime * (prime * (numeratorFactor * numeratorFactor)) =
          prime * (reduced.den * reduced.den) := by
      calc
        prime * (prime * (numeratorFactor * numeratorFactor)) =
            (prime * numeratorFactor) * (prime * numeratorFactor) := by ring1
        _ = prime * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
    exact (Nat.eq_of_mul_eq_mul_left primePositive scaled).symm
  have primeDvdDenominator : prime ∣ reduced.den :=
    dvdSquare ⟨numeratorFactor * numeratorFactor, denominatorSquare⟩
  rcases reduced.reduced with ⟨certificate⟩
  have absurd : prime = 1 :=
    certificate.eq_one_of_dvd numeratorDivides primeDvdDenominator
  exact primeNeOne absurd

/-- No canonical rational has square two.  The proof inspects the two
possible residues and the stored reduced numerator/denominator only. -/
theorem square_ne_two (value : Rational) : value ^ 2 ≠ 2 := by
  exact square_ne_nat_of_dvd_square 2 (by decide) (by decide)
    two_dvd_of_two_dvd_square value

private theorem three_dvd_of_three_dvd_square {value : Nat}
    (divides : 3 ∣ value * value) : 3 ∣ value := by
  rw [Nat.dvd_iff_mod_eq_zero] at divides ⊢
  have remainderLt : value % 3 < 3 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 3 = (value % 3) * (value % 3) % 3 := by
    rw [Nat.mul_mod]
  rw [squareRemainder] at divides
  cases remainderEq : value % 3 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rw [remainderEq] at divides
          have impossible : (1 * 1 % 3 : Nat) ≠ 0 := by decide
          exact (impossible divides).elim
      | succ remainder =>
          cases remainder with
          | zero =>
              rw [remainderEq] at divides
              have impossible : (2 * 2 % 3 : Nat) ≠ 0 := by decide
              exact (impossible divides).elim
          | succ remainder =>
              rw [remainderEq] at remainderLt
              have threeLe : 3 ≤ Nat.succ (Nat.succ (Nat.succ remainder)) :=
                Nat.succ_le_succ (Nat.succ_le_succ
                  (Nat.succ_le_succ (Nat.zero_le remainder)))
              exact (Nat.not_lt_of_ge threeLe remainderLt).elim

/-- No canonical rational has square three.  Clearing its stored positive
denominator produces a finite integer-square equation; reduction then
supplies the explicit Bézout contradiction. -/
theorem square_ne_three (value : Rational) : value ^ 2 ≠ 3 := by
  intro square
  let reduced := representative value
  have cleared := representative_mul_den value
  change value * (reduced.den : Rational) = (reduced.num : Rational) at cleared
  have rationalSquare :
      (reduced.num : Rational) ^ 2 =
        3 * (reduced.den : Rational) ^ 2 := by
    calc
      (reduced.num : Rational) ^ 2 =
          (value * (reduced.den : Rational)) ^ 2 := by rw [cleared]
      _ = value ^ 2 * (reduced.den : Rational) ^ 2 := by ring1
      _ = 3 * (reduced.den : Rational) ^ 2 := by rw [square]
  have integerSquare :
      reduced.num * reduced.num =
        (3 : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    apply intCast_injective_direct
    rw [intCast_mul_direct, intCast_mul_direct, intCast_mul_direct]
    simpa only [Int.cast_natCast, Int.cast_ofNat, pow_two] using
      rationalSquare
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        3 * (reduced.den * reduced.den) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast,
      show Int.natAbs 3 = 3 from rfl] using absoluteSquare
  have threeDvdNumerator : 3 ∣ reduced.num.natAbs :=
    three_dvd_of_three_dvd_square
      ⟨reduced.den * reduced.den, naturalSquare⟩
  have numeratorDivides : 3 ∣ reduced.num.natAbs := threeDvdNumerator
  rcases threeDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have denominatorSquare :
      reduced.den * reduced.den = 3 * (numeratorFactor * numeratorFactor) := by
    have scaled :
        3 * (3 * (numeratorFactor * numeratorFactor)) =
          3 * (reduced.den * reduced.den) := by
      calc
        3 * (3 * (numeratorFactor * numeratorFactor)) =
            (3 * numeratorFactor) * (3 * numeratorFactor) := by ring1
        _ = 3 * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
    exact (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) scaled).symm
  have threeDvdDenominator : 3 ∣ reduced.den :=
    three_dvd_of_three_dvd_square
      ⟨numeratorFactor * numeratorFactor, denominatorSquare⟩
  rcases reduced.reduced with ⟨certificate⟩
  have absurd : 3 = 1 :=
    certificate.eq_one_of_dvd numeratorDivides threeDvdDenominator
  exact (by decide : (3 : Nat) ≠ 1) absurd

/-- Divisibility of a displayed natural square by five forces divisibility
of its base.  The five literal remainder cases are the entire argument. -/
private theorem five_dvd_of_five_dvd_square {value : Nat}
    (divides : 5 ∣ value * value) : 5 ∣ value := by
  rw [Nat.dvd_iff_mod_eq_zero] at divides ⊢
  have remainderLt : value % 5 < 5 := Nat.mod_lt value (by decide)
  have squareRemainder :
      value * value % 5 = (value % 5) * (value % 5) % 5 := by
    rw [Nat.mul_mod]
  rw [squareRemainder] at divides
  cases remainderEq : value % 5 with
  | zero => rfl
  | succ remainder =>
      cases remainder with
      | zero =>
          rw [remainderEq] at divides
          exact ((by decide : (1 * 1 % 5 : Nat) ≠ 0) divides).elim
      | succ remainder =>
          cases remainder with
          | zero =>
              rw [remainderEq] at divides
              exact ((by decide : (2 * 2 % 5 : Nat) ≠ 0) divides).elim
          | succ remainder =>
              cases remainder with
              | zero =>
                  rw [remainderEq] at divides
                  exact ((by decide : (3 * 3 % 5 : Nat) ≠ 0) divides).elim
              | succ remainder =>
                  cases remainder with
                  | zero =>
                      rw [remainderEq] at divides
                      exact ((by decide : (4 * 4 % 5 : Nat) ≠ 0) divides).elim
                  | succ remainder =>
                      rw [remainderEq] at remainderLt
                      have fiveLe :
                          5 ≤ Nat.succ (Nat.succ (Nat.succ
                            (Nat.succ (Nat.succ remainder)))) :=
                        Nat.succ_le_succ (Nat.succ_le_succ
                          (Nat.succ_le_succ (Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.zero_le remainder)))))
                      exact (Nat.not_lt_of_ge fiveLe remainderLt).elim

/-- No canonical rational has square five. -/
theorem square_ne_five (value : Rational) : value ^ 2 ≠ 5 := by
  exact square_ne_nat_of_dvd_square 5 (by decide) (by decide)
    five_dvd_of_five_dvd_square value

/-- No canonical rational has square `455`.  Clearing its stored positive
denominator gives `num² = 455 den²`; the literal remainder-five calculation
makes both stored components divisible by five, contradicting the explicit
Bézout reducedness certificate. -/
theorem square_ne_455 (value : Rational) : value ^ 2 ≠ 455 := by
  intro square
  let reduced := representative value
  have cleared := representative_mul_den value
  change value * (reduced.den : Rational) = (reduced.num : Rational) at cleared
  have rationalSquare :
      (reduced.num : Rational) ^ 2 =
        455 * (reduced.den : Rational) ^ 2 := by
    calc
      (reduced.num : Rational) ^ 2 =
          (value * (reduced.den : Rational)) ^ 2 := by rw [cleared]
      _ = value ^ 2 * (reduced.den : Rational) ^ 2 := by ring1
      _ = 455 * (reduced.den : Rational) ^ 2 := by rw [square]
  have integerSquare :
      reduced.num * reduced.num =
        (455 : Int) * ((reduced.den : Int) * (reduced.den : Int)) := by
    apply intCast_injective_direct
    rw [intCast_mul_direct, intCast_mul_direct, intCast_mul_direct]
    simpa only [Int.cast_natCast, Int.cast_ofNat, pow_two] using
      rationalSquare
  have absoluteSquare := congrArg Int.natAbs integerSquare
  have naturalSquare :
      reduced.num.natAbs * reduced.num.natAbs =
        455 * (reduced.den * reduced.den) := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast,
      show Int.natAbs 455 = 455 from rfl] using absoluteSquare
  have fiveDvdNumeratorSquare :
      5 ∣ reduced.num.natAbs * reduced.num.natAbs := by
    refine ⟨91 * (reduced.den * reduced.den), ?_⟩
    calc
      reduced.num.natAbs * reduced.num.natAbs =
          455 * (reduced.den * reduced.den) := naturalSquare
      _ = 5 * (91 * (reduced.den * reduced.den)) := by ring1
  have fiveDvdNumerator : 5 ∣ reduced.num.natAbs :=
    five_dvd_of_five_dvd_square fiveDvdNumeratorSquare
  have numeratorDivides : 5 ∣ reduced.num.natAbs := fiveDvdNumerator
  rcases fiveDvdNumerator with ⟨numeratorFactor, numeratorEquation⟩
  have reducedEquation :
      5 * (numeratorFactor * numeratorFactor) =
        91 * (reduced.den * reduced.den) := by
    have scaled :
        5 * (5 * (numeratorFactor * numeratorFactor)) =
          5 * (91 * (reduced.den * reduced.den)) := by
      calc
        5 * (5 * (numeratorFactor * numeratorFactor)) =
            (5 * numeratorFactor) * (5 * numeratorFactor) := by ring1
        _ = 455 * (reduced.den * reduced.den) := by
          rw [← numeratorEquation]
          exact naturalSquare
        _ = 5 * (91 * (reduced.den * reduced.den)) := by ring1
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) scaled
  have denominatorSquareMod :
      (reduced.den * reduced.den) % 5 = 0 := by
    have productDivisible : 5 ∣ 91 * (reduced.den * reduced.den) :=
      ⟨numeratorFactor * numeratorFactor, reducedEquation.symm⟩
    calc
      (reduced.den * reduced.den) % 5 =
          ((91 % 5) * ((reduced.den * reduced.den) % 5)) % 5 := by
            simp only [Nat.reduceMod, Nat.one_mul, Nat.mod_mod]
      _ = (91 * (reduced.den * reduced.den)) % 5 :=
        (Nat.mul_mod 91 (reduced.den * reduced.den) 5).symm
      _ = 0 := (Nat.dvd_iff_mod_eq_zero).1 productDivisible
  have fiveDvdDenominatorSquare : 5 ∣ reduced.den * reduced.den :=
    (Nat.dvd_iff_mod_eq_zero).2 denominatorSquareMod
  have fiveDvdDenominator : 5 ∣ reduced.den :=
    five_dvd_of_five_dvd_square fiveDvdDenominatorSquare
  rcases reduced.reduced with ⟨certificate⟩
  have absurd : 5 = 1 :=
    certificate.eq_one_of_dvd numeratorDivides fiveDvdDenominator
  exact (by decide : (5 : Nat) ≠ 1) absurd

end RFAP.ConstructiveFraction
