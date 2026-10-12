module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Int.Order
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.Multiplication

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data
open Purelib.Algebra

/-- Adding a common rational shift preserves a strict bound.

The retained shifted difference is the original difference. The canonical
strict-order equivalence transports its positive sign in each direction. -/
theorem add_lt_add_right_direct {left right : Fraction.Rational}
    (less : left < right) (shift : Fraction.Rational) :
    left + shift < right + shift := by
  have positive := (Order.Basic.lt_iff_zero_lt_sub left right).mp less
  have differenceIdentity :
      right + shift - (left + shift) = right - left := by
    rw [Arithmetic.sub_eq_add_neg_direct, Arithmetic.sub_eq_add_neg_direct]
    ring1
  apply (Order.Basic.lt_iff_zero_lt_sub (left + shift) (right + shift)).mpr
  rw [differenceIdentity]
  exact positive

/-- Weak right translation, obtained by the finite equality/strict split. -/
theorem add_le_add_right_direct {left right : Fraction.Rational}
    (lessEqual : left ≤ right) (shift : Fraction.Rational) :
    left + shift ≤ right + shift := by
  by_cases equal : left = right
  · rw [equal]
  · exact (add_lt_add_right_direct
      ⟨lessEqual, fun reverse => equal
        (Order.Basic.le_antisymm left right lessEqual reverse)⟩
      shift).le

/-- Weak addition in both arguments. -/
theorem add_le_add_direct {first second third fourth :
  Fraction.Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth) :
    first + third ≤ second + fourth := by
  calc
    first + third ≤ second + third :=
      add_le_add_right_direct firstSecond third
    _ = third + second := by ring1
    _ ≤ fourth + second := add_le_add_right_direct thirdFourth second
    _ = second + fourth := by ring1

/-- Adding a common rational on the left preserves weak order. -/
private theorem add_le_add_left_canonical
    (left right : Fraction.Rational) (lessEqual : left ≤ right) (shift : Fraction.Rational) :
    shift + left ≤ shift + right := by
  rw [_root_.add_comm shift left, _root_.add_comm shift right]
  exact add_le_add_right_direct lessEqual shift

/-- Cancel a common left summand from a weak canonical rational comparison. -/
private theorem le_of_add_le_add_left_canonical
    (shift left right : Fraction.Rational)
    (lessEqual : shift + left ≤ shift + right) : left ≤ right := by
  have translated := add_le_add_right_direct lessEqual (-shift)
  calc
    left = (shift + left) + -shift := by ring1
    _ ≤ (shift + right) + -shift := translated
    _ = right := by ring1

/-- Retain direct rational translation monotonicity as the ordered additive-monoid witness. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid Fraction.Rational
  where
  add_le_add_left := fun _ _ lessEqual shift =>
    add_le_add_right_direct lessEqual shift

/-- Retain direct rational translation monotonicity and cancellation as ordered additive witnesses. -/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid
  Fraction.Rational where
  add_le_add_left := fun _ _ lessEqual shift =>
    add_le_add_right_direct lessEqual shift
  le_of_add_le_add_left := fun shift left right lessEqual =>
    le_of_add_le_add_left_canonical shift left right lessEqual

/-! The generic commutative derivation of `AddRightMono` passes through
function swapping and currently reaches `Quot.sound`.  Supply the stored
right-translation proof directly so ordinary ordered-addition lemmas retain
the quotient-free closure. -/
/-- Provide direct weak right-translation monotonicity for canonical rationals.

The stored proof is the direct canonical translation theorem, preserving the constructive proof route without the
generic function-swapping derivation. -/
instance instAddRightMono : AddRightMono Fraction.Rational where
  elim shift _ _ lessEqual := add_le_add_right_direct lessEqual shift

/-- Retain the exact canonical comparison that zero is at most one. -/
instance instZeroLEOneClass : ZeroLEOneClass Fraction.Rational where
  zero_le_one := by decide

/-- Recover weak comparison from failure of the reverse strict comparison. -/
theorem le_of_not_gt_direct {left right : Fraction.Rational}
    (notGreater : ¬ right < left) : left ≤ right := by
  rcases Fraction.Order.Basic.le_total left right with direct | reverse
  · exact direct
  · by_cases direct : left ≤ right
    · exact direct
    · exact (notGreater ⟨reverse, direct⟩).elim

/-- Recover strict comparison from failure of the reverse weak comparison. -/
theorem lt_of_not_ge_direct {left right : Fraction.Rational}
    (notGreaterEqual : ¬ right ≤ left) : left < right := by
  have lessEqual : left ≤ right := by
    rcases Fraction.Order.Basic.le_total left right with direct | reverse
    · exact direct
    · exact (notGreaterEqual reverse).elim
  exact ⟨lessEqual, notGreaterEqual⟩

/-- A strict canonical rational comparison implies its weak comparison. -/
theorem le_of_lt_direct {left right : Fraction.Rational} (less : left
  < right) :
    left ≤ right := less.1

/-- Subtracting the same rational from both sides preserves weak comparison. -/
theorem sub_le_sub_right_direct {left right : Fraction.Rational}
    (lessEqual : left ≤ right) (shift : Fraction.Rational) :
    left - shift ≤ right - shift := by
  simpa only [Fraction.Arithmetic.sub_eq_add_neg_direct] using
    add_le_add_right_direct lessEqual (-shift)

/-- Cancel a common right summand from a weak rational comparison. -/
theorem le_of_add_le_add_right_direct {a b c : Fraction.Rational}
    (lessEqual : a + c ≤ b + c) : a ≤ b := by
  have translated := add_le_add_right_direct lessEqual (-c)
  simpa only [_root_.add_assoc, _root_.add_neg_cancel, _root_.add_zero] using translated

/-- A weak rational comparison makes the right-minus-left difference nonnegative. -/
theorem sub_nonneg_direct {left right : Fraction.Rational}
    (lessEqual : left ≤ right) : 0 ≤ right - left := by
  have translated := add_le_add_right_direct lessEqual (-left)
  calc
    0 = left + -left := by ring1
    _ ≤ right + -left := translated
    _ = right - left := (Fraction.Arithmetic.sub_eq_add_neg_direct right left).symm

/-- A nonnegative right-minus-left rational difference gives the corresponding weak comparison. -/
theorem le_of_sub_nonneg_direct {left right : Fraction.Rational}
    (nonnegative : 0 ≤ right - left) : left ≤ right := by
  have translated := add_le_add_right_direct nonnegative left
  calc
    left = 0 + left := by ring1
    _ ≤ (right - left) + left := translated
    _ = right := by
      rw [Fraction.Arithmetic.sub_eq_add_neg_direct]
      ring1

/-- A strict rational comparison makes the right-minus-left difference positive. -/
theorem sub_pos_direct {left right : Fraction.Rational} (less : left <
  right) :
    0 < right - left :=
  (Fraction.Order.Basic.lt_iff_zero_lt_sub left right).mp less

/-- A positive right-minus-left rational difference gives the corresponding strict comparison. -/
theorem lt_of_sub_pos_direct {left right : Fraction.Rational}
    (positive : 0 < right - left) : left < right :=
  (Fraction.Order.Basic.lt_iff_zero_lt_sub left right).mpr positive

/-- A strict rational bound gives a negative subtraction in the reverse order.

Translating both endpoints by the upper endpoint's negation gives the displayed
subtraction below zero, with the original scalar addition operations. -/
theorem sub_neg_direct {left right : Fraction.Rational} (less : left <
  right) :
    left - right < 0 := by
  have translated := add_lt_add_right_direct less (-right)
  rw [add_comm right (-right), neg_add_cancel] at translated
  rw [Arithmetic.sub_eq_add_neg_direct]
  exact translated

/-- A negative rational subtraction gives a strict bound between its endpoints.

Adding the subtracted endpoint back transports the negative bound and cancels
the retained additive inverse. -/
theorem lt_of_sub_neg_direct {left right : Fraction.Rational}
    (negative : left - right < 0) : left < right := by
  have translated := add_lt_add_right_direct negative right
  rw [Arithmetic.sub_eq_add_neg_direct, add_assoc, neg_add_cancel,
    _root_.add_zero, zero_add] at translated
  exact translated

/-- Adding the same rational on the left preserves strict comparison. -/
theorem add_lt_add_left_direct {left right : Fraction.Rational}
    (less : left < right) (shift : Fraction.Rational) :
    shift + left < shift + right := by
  simpa only [_root_.add_comm shift] using add_lt_add_right_direct less shift

/-- Subtracting the same rational on the right preserves strict comparison. -/
theorem sub_lt_sub_right_direct {left right : Fraction.Rational}
    (less : left < right) (shift : Fraction.Rational) :
    left - shift < right - shift := by
  simpa only [Fraction.Arithmetic.sub_eq_add_neg_direct] using
    add_lt_add_right_direct less (-shift)

/-- Negation reverses strict canonical rational comparison. -/
theorem neg_lt_neg_direct {left right : Fraction.Rational} (less :
  left < right) :
    -right < -left := by
  apply lt_of_sub_pos_direct
  have positive := sub_pos_direct less
  have identity : -left - -right = right - left := by
    rw [Fraction.Arithmetic.sub_eq_add_neg_direct, Fraction.Arithmetic.sub_eq_add_neg_direct]
    ring1
  rwa [identity]

/-- Subtracting strictly ordered rationals from a common value reverses their comparison. -/
theorem sub_lt_sub_left_direct {a b : Fraction.Rational}
    (less : a < b) (c : Fraction.Rational) :
    c - b < c - a := by
  simpa only [Fraction.Arithmetic.sub_eq_add_neg_direct] using
    add_lt_add_left_direct (neg_lt_neg_direct less) c

/-- Negation reverses weak canonical rational comparison. -/
theorem neg_le_neg_direct {left right : Fraction.Rational}
    (lessEqual : left ≤ right) : -right ≤ -left := by
  by_cases equal : left = right
  · rw [equal]
  · exact (neg_lt_neg_direct
      ⟨lessEqual, fun reverse => equal
        (Order.Basic.le_antisymm left right lessEqual reverse)⟩).le

/-- Weak subtraction in both arguments, assembled from the canonical addition and negation order laws rather than the
generic ordered-group inheritance path. -/
theorem sub_le_sub_direct {first second third fourth :
  Fraction.Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth) :
    first - fourth ≤ second - third := by
  rw [Fraction.Arithmetic.sub_eq_add_neg_direct, Fraction.Arithmetic.sub_eq_add_neg_direct]
  exact add_le_add_direct firstSecond (neg_le_neg_direct
    thirdFourth)

/-- Subtracting weakly ordered rationals from a common value reverses their comparison. -/
theorem sub_le_sub_left_direct {left right : Fraction.Rational}
    (lessEqual : left ≤ right) (shift : Fraction.Rational) :
    shift - right ≤ shift - left :=
  sub_le_sub_direct le_rfl lessEqual

/-- The absolute value of a canonical rational is nonnegative.

The retained maximum selects the source or its negation. Its comparison and
the source's explicit sign give a nonnegative bound in either case. -/
theorem abs_nonneg_direct (source : Fraction.Rational) : 0 ≤
  Fraction.abs source := by
  change 0 ≤ if source ≤ -source then -source else source
  by_cases nonnegative : 0 ≤ source
  · split
    · next comparison => exact Order.Basic.le_trans _ _ _ nonnegative comparison
    · exact nonnegative
  · have nonpositive : source ≤ 0 :=
      le_of_not_gt_direct fun positive => nonnegative positive.1
    have negativeNonnegative := neg_le_neg_direct nonpositive
    rw [neg_zero] at negativeNonnegative
    split
    · exact negativeNonnegative
    · next notComparison =>
        have reverse := (Order.Basic.le_total source (-source)).resolve_left notComparison
        exact Order.Basic.le_trans _ _ _ negativeNonnegative reverse

/-- Weak comparison of two negated rationals is exactly the reverse original comparison. -/
theorem neg_le_neg_iff_direct (left right : Fraction.Rational) :
    -left ≤ -right ↔ right ≤ left := by
  constructor
  · intro lessEqual
    have reversed := neg_le_neg_direct lessEqual
    simpa only [neg_neg] using reversed
  · exact neg_le_neg_direct

/-- Adding two strict rational comparisons gives a strict comparison of their sums. -/
theorem add_lt_add_direct {first second third fourth :
  Fraction.Rational}
    (firstSecond : first < second) (thirdFourth : third < fourth) :
    first + third < second + fourth :=
  (add_lt_add_right_direct firstSecond third).trans
    (add_lt_add_left_direct thirdFourth second)

/-- Cancel a common right summand from a strict rational comparison. -/
theorem lt_of_add_lt_add_right_direct {a b c : Fraction.Rational}
    (less : a + c < b + c) : a < b := by
  have translated := add_lt_add_right_direct less (-c)
  simpa only [_root_.add_assoc, _root_.add_neg_cancel, _root_.add_zero] using translated

/-- Multiplying two positive canonical rationals gives a positive rational.

Their retained integer numerators have a positive product. The existing
positive-denominator multiplication display transports that sign to the
normalized product numerator. -/
theorem mul_pos_direct {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < left * right := by
  apply (Order.Basic.zero_lt_iff_num_pos (left * right)).mpr
  exact (Order.Basic.numerator_pos_iff_of_equivalent (mul_equivalent left right)).mpr
    (Int.Order.mul_pos ((Order.Basic.zero_lt_iff_num_pos left).mp leftPositive)
      ((Order.Basic.zero_lt_iff_num_pos right).mp rightPositive))

/-- Multiplying a strict rational comparison on the left by a positive factor preserves it. -/
theorem mul_lt_mul_of_pos_left_direct {a b c : Fraction.Rational}
    (ha : 0 < a) (less : b < c) :
    a * b < a * c := by
  apply lt_of_sub_pos_direct
  have differencePositive := mul_pos_direct ha (sub_pos_direct less)
  have identity : a * c - a * b = a * (c - b) := by
    rw [Fraction.Arithmetic.sub_eq_add_neg_direct, Fraction.Arithmetic.sub_eq_add_neg_direct]
    rw [_root_.mul_add, _root_.mul_neg]
  rw [identity]
  exact differencePositive

/-- Multiplying a strict rational comparison on the right by a positive factor preserves it. -/
theorem mul_lt_mul_of_pos_right_direct {a b c : Fraction.Rational}
    (less : a < b) (hc : 0 < c) :
    a * c < b * c := by
  simpa only [_root_.mul_comm c] using
    mul_lt_mul_of_pos_left_direct hc less

/-- Multiplying two negative canonical rationals gives a positive rational.

Negating each retained strict bound gives two positive factors. Their product
has the same scalar value as the original product. -/
theorem mul_pos_of_neg_of_neg_direct {left right : Fraction.Rational}
    (leftNegative : left < 0) (rightNegative : right < 0) :
    0 < left * right := by
  have leftPositive := neg_lt_neg_direct leftNegative
  have rightPositive := neg_lt_neg_direct rightNegative
  rw [neg_zero] at leftPositive rightPositive
  have positive := mul_pos_direct leftPositive rightPositive
  rw [Ring.Multiplication.neg_mul_neg] at positive
  exact positive

/-- A negative canonical rational times a positive one has negative product.

The negated left factor is positive. Negating its positive product gives the
strict negative bound for the original product. -/
theorem mul_neg_of_neg_of_pos_direct {left right : Fraction.Rational}
    (leftNegative : left < 0) (rightPositive : 0 < right) :
    left * right < 0 := by
  have leftPositive := neg_lt_neg_direct leftNegative
  rw [neg_zero] at leftPositive
  have positive := mul_pos_direct leftPositive rightPositive
  rw [Ring.Multiplication.neg_mul] at positive
  have negative := neg_lt_neg_direct positive
  rw [neg_zero, neg_neg] at negative
  exact negative

/-- A positive rational times a negative rational is negative. -/
theorem mul_neg_of_pos_of_neg_direct {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightNegative : right < 0) :
    left * right < 0 := by
  rw [_root_.mul_comm]
  exact mul_neg_of_neg_of_pos_direct rightNegative leftPositive

/-- A positive product with nonnegative left factor has positive right factor. -/
theorem pos_of_mul_pos_right_direct {left right : Fraction.Rational}
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

/-- Retain direct strict monotonicity of multiplication on the left by a positive rational. -/
instance instPosMulStrictMono : PosMulStrictMono Fraction.Rational
  where
  mul_lt_mul_of_pos_left := fun {factor} factorPositive {left right} less =>
    mul_lt_mul_of_pos_left_direct
      (a := factor) (b := left) (c := right) factorPositive less

/-- Retain direct strict monotonicity of multiplication on the right by a positive rational. -/
instance instMulPosStrictMono : MulPosStrictMono Fraction.Rational
  where
  mul_lt_mul_of_pos_right := fun {factor} factorPositive {left right} less =>
    mul_lt_mul_of_pos_right_direct
      (a := left) (b := right) (c := factor) less factorPositive

/-- The distinct canonical zero and one values witness a nontrivial rational carrier. -/
instance instNontrivial : Nontrivial Fraction.Rational :=
  ⟨⟨0, 1, zero_ne_one⟩⟩

/-- Combine the retained rational ring and direct strict order witnesses. -/
instance instIsStrictOrderedRing : IsStrictOrderedRing
  Fraction.Rational where

/-- The product of two nonnegative canonical rationals is nonnegative. -/
theorem mul_nonneg_direct {left right : Fraction.Rational}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    0 ≤ left * right := by
  by_cases leftZero : left = 0
  · rw [leftZero, zero_mul]
  · by_cases rightZero : right = 0
    · rw [rightZero, mul_zero]
    · have leftPositive : 0 < left :=
        ⟨leftNonnegative, fun reverse => leftZero
          (Order.Basic.le_antisymm left 0 reverse leftNonnegative)⟩
      have rightPositive : 0 < right :=
        ⟨rightNonnegative, fun reverse => rightZero
          (Order.Basic.le_antisymm right 0 reverse rightNonnegative)⟩
      exact (mul_pos_direct leftPositive rightPositive).le

/-- Multiplying a weak rational comparison on the right by a nonnegative factor preserves it. -/
theorem mul_le_mul_of_nonneg_right_direct {a b c : Fraction.Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  by_cases factorZero : c = 0
  · rw [factorZero, mul_zero, mul_zero]
  · have factorPositive : 0 < c :=
      ⟨hc, fun reverse => factorZero
        (Order.Basic.le_antisymm c 0 reverse hc)⟩
    by_cases equal : a = b
    · rw [equal]
    · exact (mul_lt_mul_of_pos_right_direct
        ⟨hab, fun reverse => equal
          (Order.Basic.le_antisymm a b hab reverse)⟩
        factorPositive).le

/-- Multiplying a weak rational comparison on the left by a nonnegative factor preserves it. -/
theorem mul_le_mul_of_nonneg_left_direct {a b c : Fraction.Rational}
    (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  simpa only [_root_.mul_comm c] using
    mul_le_mul_of_nonneg_right_direct hab hc

/-- The square of every canonical rational is nonnegative. -/
theorem sq_nonneg_direct (source : Fraction.Rational) : 0 ≤ source ^ 2
  := by
  by_cases sourceNonnegative : 0 ≤ source
  · simpa only [pow_two] using
      mul_nonneg_direct sourceNonnegative sourceNonnegative
  · have sourceNegative : source < 0 :=
      lt_of_not_ge_direct sourceNonnegative
    exact (by
      simpa only [pow_two] using
        (mul_pos_of_neg_of_neg_direct sourceNegative sourceNegative).le)

/-- A canonical rational square is zero exactly when its base is zero. -/
theorem sq_eq_zero_direct (source : Fraction.Rational) : source ^ 2 =
  0 ↔ source = 0 := by
  constructor
  · intro squareZero
    by_cases sourceZero : source = 0
    · exact sourceZero
    · have productNonzero :=
        Fraction.mul_ne_zero sourceZero sourceZero
      exact (productNonzero (by simpa only [pow_two] using squareZero)).elim
  · intro sourceZero
    rw [sourceZero]
    rfl

/-- Every natural power of a nonnegative canonical rational is nonnegative. -/
theorem pow_nonneg_direct {source : Fraction.Rational} (nonnegative :
  0 ≤ source) :
    ∀ exponent : Nat, 0 ≤ source ^ exponent
  | 0 => by
      change (0 : Fraction.Rational) ≤ 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_nonneg_direct (pow_nonneg_direct
        nonnegative exponent)
        nonnegative

/-- Every natural power of a strictly positive canonical rational is positive. -/
theorem pow_pos_direct {source : Fraction.Rational} (positive : 0 <
  source) :
    ∀ exponent : Nat, 0 < source ^ exponent
  | 0 => by
      change (0 : Fraction.Rational) < 1
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact mul_pos_direct (pow_pos_direct positive
        exponent) positive

/-- Multiply two weak rational comparisons when the left lower and right upper scaling factors are nonnegative. -/
theorem mul_le_mul_direct {first second third fourth :
  Fraction.Rational}
    (firstSecond : first ≤ second) (thirdFourth : third ≤ fourth)
    (thirdNonnegative : 0 ≤ third) (secondNonnegative : 0 ≤ second) :
    first * third ≤ second * fourth :=
  (mul_le_mul_of_nonneg_right_direct firstSecond thirdNonnegative).trans
    (mul_le_mul_of_nonneg_left_direct thirdFourth secondNonnegative)

/-- Natural powers preserve a weak rational comparison with nonnegative lower endpoint. -/
theorem pow_le_pow_direct {left right : Fraction.Rational}
    (leftNonnegative : 0 ≤ left) (lessEqual : left ≤ right) :
    ∀ exponent : Nat, left ^ exponent ≤ right ^ exponent
  | 0 => le_rfl
  | exponent + 1 => by
      rw [pow_succ, pow_succ]
      exact mul_le_mul_direct
        (pow_le_pow_direct leftNonnegative lessEqual exponent) lessEqual
        leftNonnegative
        (pow_nonneg_direct (leftNonnegative.trans lessEqual) exponent)

/-- Cancel a strictly positive common right factor from a weak rational comparison. -/
theorem le_of_mul_le_mul_right_direct {a b c : Fraction.Rational}
    (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  by_cases lessEqual : a ≤ b
  · exact lessEqual
  · have reverse : b ≤ a :=
      (Fraction.Order.Basic.le_total b a).resolve_right lessEqual
    have strictScaled : b * c < a * c :=
      mul_lt_mul_of_pos_right_direct ⟨reverse, lessEqual⟩ hc
    exact ((not_lt_of_ge h) strictScaled).elim

/-- Cancel a strictly positive common right factor from a strict rational comparison. -/
theorem lt_of_mul_lt_mul_right_direct {a b c : Fraction.Rational}
    (h : a * c < b * c) (hc : 0 < c) :
    a < b := by
  by_cases less : a < b
  · exact less
  · have reverse : b ≤ a := le_of_not_gt_direct less
    have reverseScaled :=
      mul_le_mul_of_nonneg_right_direct reverse hc.le
    exact ((not_lt_of_ge reverseScaled) h).elim

/-- A rational whose square is bounded by a nonnegative bound's square is at most that bound. -/
theorem le_of_sq_le_sq_direct {source bound : Fraction.Rational}
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

/-- A rational square bound gives the lower signed endpoint bound.

Negating the source preserves its square, so its upper bound transports under
negation to the original source's lower bound. The supplied radius is nonnegative. -/
theorem neg_le_of_sq_le_sq_direct {source bound : Fraction.Rational}
    (boundNonnegative : 0 ≤ bound)
    (squares : source ^ 2 ≤ bound ^ 2) : -bound ≤ source := by
  have negativeSquares : (-source) ^ 2 ≤ bound ^ 2 := by
    have identity : (-source) ^ 2 = source ^ 2 := by
      rw [pow_two, pow_two, Ring.Multiplication.neg_mul_neg]
    rw [identity]
    exact squares
  have upper : -source ≤ bound :=
    le_of_sq_le_sq_direct boundNonnegative negativeSquares
  have reversed := neg_le_neg_direct upper
  simpa only [neg_neg] using reversed
end Purelib.Data.Rat.Fraction.Order.Arithmetic

end

end

section
@[expose] public section

/-!
# Finite box-sign certificates for CCL branch curves

A four-coefficient Hermitian form has an explicit squared variation bound on
every rational subbox of a fixed rational bounding box.  Comparing that bound
with the squared value at one displayed sample gives a finite certificate that
the form has one strict sign throughout the subbox.

The bound is deliberately coarse.  Its important feature for the persistent
CCL controller is that it is a rational coefficient times the subbox's
squared diagonal, so it contracts along the existing finite shrinking track.
-/

namespace Purelib.CCL.Boundary.BoxSign
namespace Certificate

end Certificate
end Purelib.CCL.Boundary.BoxSign

end

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Data.Rat.Fraction.Order.Boundary

open Purelib.Data.Rat

/-- A nonnegative rational subtraction is the weak bound on its endpoints. -/
theorem sub_nonnegative_iff {value threshold : Fraction.Rational} :
    0 ≤ value - threshold ↔ threshold ≤ value := by
  constructor
  · exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  · exact Fraction.Order.Arithmetic.sub_nonneg_direct

/-- A nonpositive rational subtraction is the reverse weak bound on its endpoints.

Adding the threshold or its negation transports each bound, using the retained
scalar inverse to identify the zero endpoint. -/
theorem sub_nonpositive_iff {value threshold : Fraction.Rational} :
    value - threshold ≤ 0 ↔ value ≤ threshold := by
  constructor
  · intro nonpositive
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
      nonpositive threshold
    rw [Fraction.Arithmetic.sub_eq_add_neg_direct, Fraction.add_assoc,
      Fraction.neg_add_cancel, _root_.add_zero, Fraction.zero_add] at translated
    exact translated
  · intro bound
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct bound (-threshold)
    rw [Fraction.add_comm threshold (-threshold), Fraction.neg_add_cancel] at translated
    rw [Fraction.Arithmetic.sub_eq_add_neg_direct]
    exact translated

/-- A rational difference is negative exactly when its minuend is strictly smaller than its subtrahend. -/
theorem sub_negative_iff {value threshold : Fraction.Rational} :
    value - threshold < 0 ↔ value < threshold := by
  constructor
  · exact Fraction.Order.Arithmetic.lt_of_sub_neg_direct
  · exact Fraction.Order.Arithmetic.sub_neg_direct

/-- A rational difference is positive exactly when its minuend is strictly larger than its subtrahend. -/
theorem sub_positive_iff {value threshold : Fraction.Rational} :
    0 < value - threshold ↔ threshold < value := by
  constructor
  · exact Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  · exact Fraction.Order.Arithmetic.sub_pos_direct
end Purelib.Data.Rat.Fraction.Order.Boundary

end

section
@[expose] public section

/-!
# Constructive finite CCF contraction certificate

This file isolates the finite integer and half-open-square estimates used by
the three-step coordinate-floor CCF contraction theorem.  The exceptional
digit set is an eight-constructor type; no unbounded search or ambient
quantifier-elimination principle is involved.
-/

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- The product of two nonpositive canonical rationals is nonnegative. -/
public theorem product_nonnegative_of_both_nonpositive
    {x y : Fraction.Rational} (xNonpositive : x ≤ 0) (yNonpositive : y ≤ 0) :
    0 ≤ x * y := by
  have negXNonnegative := neg_le_neg_direct
    xNonpositive
  have negYNonnegative := neg_le_neg_direct
    yNonpositive
  have product := mul_nonneg_direct
    (by simpa only [neg_zero] using negXNonnegative)
    (by simpa only [neg_zero] using negYNonnegative)
  calc
    0 ≤ (-x) * (-y) := product
    _ = x * y := by ring1

/-- The product of two strictly negative canonical rationals is positive. -/
public theorem product_positive_of_both_negative
    {x y : Fraction.Rational} (xNegative : x < 0) (yNegative : y < 0) :
    0 < x * y := by
  have negXPositive := neg_lt_neg_direct xNegative
  have negYPositive := neg_lt_neg_direct yNegative
  have product := mul_pos_direct
    (by simpa only [neg_zero] using negXPositive)
    (by simpa only [neg_zero] using negYPositive)
  calc
    0 < (-x) * (-y) := product
    _ = x * y := by ring1

end Purelib.Data.Rat.Fraction.Order.Arithmetic

end

section
@[expose] public section

/-!
# Constructive coordinate-floor complex continued fractions

The coordinate-floor return map and its digit cone, stated entirely in the
explicit finite rational and Gaussian representations used by CCL-1.
-/

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- For a rational between zero and one, the product with one minus itself is nonnegative. -/
public theorem coordinate_product_nonnegative {x : Fraction.Rational}
    (nonnegative : 0 ≤ x) (small : x < 1) : 0 ≤ x * (1 - x) :=
  mul_nonneg_direct nonnegative
    (sub_pos_direct small).le

/-- For a rational strictly between zero and one, the product with one minus itself is positive. -/
public theorem coordinate_product_positive {x : Fraction.Rational}
    (positive : 0 < x) (small : x < 1) : 0 < x * (1 - x) :=
  mul_pos_direct positive
    (sub_pos_direct small)

/-- A nonnegative canonical rational is at least its own negation. -/
public theorem neg_le_self_of_nonnegative {x : Fraction.Rational}
    (nonnegative : 0 ≤ x) : -x ≤ x := by
  have negNonpositive := neg_le_neg_direct nonnegative
  simpa only [neg_zero] using negNonpositive.trans nonnegative

end Purelib.Data.Rat.Fraction.Order.Arithmetic

end

section
@[expose] public section

/-!
# Constructive conversion between CCL cylinders and rational boxes

The canonical CCL object remains a finite bit word with a finite projective
realization.  This module belongs to the optional quantitative sidecar.  It
converts a completed-block chordal estimate into an affine rational box and
gives a total, square-root-free rational box transport for a displayed
homography whose denominator has a positive rational margin.

The generic transport box is intentionally coarse: it first computes a
rational squared-norm bound and then encloses that ball in a symmetric box.
This is enough for the existence and productivity arguments.  Coordinatewise
interval arithmetic may replace it without changing the interface.
-/

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- A rational with square bounded by a nonnegative radius's square is at most that radius. -/
public theorem nonnegative_le_of_sq_le_sq
    {value radius : Fraction.Rational} (radiusNonnegative : 0 ≤ radius)
    (squareBound : value ^ 2 ≤ radius ^ 2) : value ≤ radius := by
  by_cases bounded : value ≤ radius
  · exact bounded
  · have radiusLtValue : radius < value := lt_of_not_ge bounded
    have valuePositive : 0 < value := radiusNonnegative.trans_lt radiusLtValue
    have first : radius * radius ≤ radius * value :=
      mul_le_mul_of_nonneg_left_direct
        radiusLtValue.le radiusNonnegative
    have second : radius * value < value * value :=
      mul_lt_mul_of_pos_right_direct
        radiusLtValue valuePositive
    have strictSquare : radius ^ 2 < value ^ 2 := by
      rw [pow_two, pow_two]
      exact first.trans_lt second
    exact ((not_lt_of_ge squareBound) strictSquare).elim

end Purelib.Data.Rat.Fraction.Order.Arithmetic

end

section
@[expose] public section

/-!
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace Purelib.CCL.Persistent.ConditionProfiles

end Purelib.CCL.Persistent.ConditionProfiles

end

section
@[expose] public section

/-!
# Worked finite hyperelliptic period examples

This module records explicit squarefree cyclic curves for the worked examples
of the finite period theorem.  Every polynomial is the concrete finite dense
power polynomial `Z^d - 1`.  Its nonzeroness, degree, and displayed Bézout
identity are proved by the finite power-monodromy algebra, so the examples
introduce no separate squarefreeness assumption.

The five nontrivial examples are

* `y² = x³ - 1` and `y² = x⁴ - 1` in genus one;
* `y² = x⁵ - 1` and `y² = x⁶ - 1` in genus two;
* `y² = x⁷ - 1` in genus three.

Two genus-zero controls, `y² = x - 1` and `y² = x² - 1`, exercise the
complete unconditional theorem and its genuinely empty period matrix.

The topology statements below compute the classical Euler characteristics
`0`, `-2`, and `-4` and expose the expected symplectic intersection basis.
The analytic period conclusions use the unconditional public theorem on
these same curves. The separate exact matrix examples below are algebraic
models, not period-program evaluations.
-/

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- A nonzero canonical rational has a strictly positive square. -/
theorem exact_rational_sq_pos {value : Fraction.Rational}
    (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have nonnegative := sq_nonneg_direct value
  exact ⟨nonnegative, fun reverse => nonzero
    ((sq_eq_zero_direct value).1
      (Data.Rat.Fraction.Order.Basic.le_antisymm _ _ reverse nonnegative))⟩
end Purelib.Data.Rat.Fraction.Order.Arithmetic

end

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- Adding a nonnegative rational to a positive rational gives a positive sum.

The original nonnegative right summand retains a weak translation of the
positive left value. Its strict lower bound therefore remains strictly above zero. -/
public theorem add_pos_of_pos_of_nonneg_direct {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightNonnegative : 0 ≤ right) :
    0 < left + right := by
  have translated := add_le_add_right_direct rightNonnegative left
  have leftBound : left ≤ left + right :=
    calc
      left = 0 + left := (Fraction.zero_add left).symm
      _ ≤ right + left := translated
      _ = left + right := Fraction.add_comm right left
  exact leftPositive.trans_le leftBound

/-- Adding a positive rational to a nonnegative rational gives a positive sum.

The retained commutative sum places the original positive right summand first,
where its strict positivity remains after adding the original nonnegative value. -/
public theorem add_pos_of_nonneg_of_pos_direct {left right : Fraction.Rational}
    (leftNonnegative : 0 ≤ left) (rightPositive : 0 < right) :
    0 < left + right := by
  have positive := add_pos_of_pos_of_nonneg_direct rightPositive leftNonnegative
  exact (Fraction.add_comm right left) ▸ positive

end Purelib.Data.Rat.Fraction.Order.Arithmetic

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data.Rat

/-- Moving a subtracted canonical rational to the right preserves weak comparison.

Adding the same retained rational to both sides restores the displayed left
operand; adding its negation reverses that translation. Both directions retain
the original three scalar inputs. -/
public theorem sub_le_iff_le_add_direct {left right bound : Fraction.Rational} :
    left - right ≤ bound ↔ left ≤ bound + right := by
  constructor
  · intro ordered
    have translated := add_le_add_right_direct ordered right
    have restore : (left - right) + right = left := by ring1
    rw [restore] at translated
    exact translated
  · intro ordered
    have translated := add_le_add_right_direct ordered (-right)
    have restoreLeft : left + -right = left - right := by ring1
    have restoreRight : (bound + right) + -right = bound := by ring1
    rw [restoreLeft, restoreRight] at translated
    exact translated

end Purelib.Data.Rat.Fraction.Order.Arithmetic

public section

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data
open Purelib.Data.Rat

/-- Twice a rational value strictly below one half is at most one.

The retained strict endpoint bound is weakened and scaled by the nonnegative factor two. The exact half simplifies to
the displayed unit endpoint. -/
public theorem twice_le_one_of_lt_half {value : Fraction.Rational}
    (upper : value < 1 / 2) : 2 * value ≤ 1 := by
  have scaled := mul_le_mul_of_nonneg_left_direct
    upper.le (show (0 : Fraction.Rational) ≤ 2 by decide)
  calc
    2 * value ≤ 2 * (1 / 2 : Fraction.Rational) := scaled
    _ = 1 := by decide

/-- Twice a rational value at least minus one half is at least minus one.

Multiplication by the nonnegative factor two transports the retained lower bound. The negative half becomes the
displayed negative unit. -/
public theorem neg_one_le_twice_of_neg_half_le {value : Fraction.Rational}
    (lower : -(1 / 2 : Fraction.Rational) ≤ value) : -1 ≤ 2 * value := by
  have scaled := mul_le_mul_of_nonneg_left_direct
    lower (show (0 : Fraction.Rational) ≤ 2 by decide)
  calc
    (-1 : Fraction.Rational) = 2 * (-(1 / 2 : Fraction.Rational)) := by decide
    _ ≤ 2 * value := scaled

/-- One minus twice a rational value below one half is nonnegative.

The same strict half-bound gives the doubled weak unit bound, which is transported to the displayed rational
subtraction. -/
public theorem one_sub_twice_nonneg_of_lt_half {value : Fraction.Rational}
    (upper : value < 1 / 2) : 0 ≤ 1 - 2 * value :=
  sub_nonneg_direct
    (twice_le_one_of_lt_half upper)

/-- One plus twice a rational value at least minus one half is nonnegative.

The doubled lower bound is translated by one. Scalar rearrangement identifies the retained input with the displayed
nonnegative sum. -/
public theorem one_add_twice_nonneg_of_neg_half_le {value : Fraction.Rational}
    (lower : -(1 / 2 : Fraction.Rational) ≤ value) : 0 ≤ 1 + 2 * value := by
  have translated := add_le_add_right_direct
    (neg_one_le_twice_of_neg_half_le lower) 1
  calc
    0 = (-1 : Fraction.Rational) + 1 := by ring1
    _ ≤ 2 * value + 1 := translated
    _ = 1 + 2 * value := by ring1

end Purelib.Data.Rat.Fraction.Order.Arithmetic

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data.Rat

/-- A positive rational product with negative right factor has negative left factor. -/
public theorem negative_of_mul_pos_right_neg
    {left right : Fraction.Rational} (product : 0 < left * right)
    (rightNegative : right < 0) : left < 0 := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · exact leftNegative
  · rw [leftZero, Fraction.Field.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · have negative :=
      mul_neg_of_pos_of_neg_direct
        leftPositive rightNegative
    exact (lt_asymm product negative).elim

/-- A positive rational product with positive right factor has positive left factor. -/
public theorem positive_of_mul_pos_right_pos
    {left right : Fraction.Rational} (product : 0 < left * right)
    (rightPositive : 0 < right) : 0 < left := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · have negative :=
      mul_neg_of_neg_of_pos_direct
        leftNegative rightPositive
    exact (lt_asymm product negative).elim
  · rw [leftZero, Fraction.Field.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · exact leftPositive

end Purelib.Data.Rat.Fraction.Order.Arithmetic

section

namespace Purelib.Data.Rat.Fraction.Order.Arithmetic
/-- Multiplication on the left by a nonpositive rational reverses weak comparison.

Negating the supplied nonpositive factor gives a nonnegative rational.
The direct product comparison and its negation reverse the original order. -/
public theorem mul_le_mul_of_nonpositive_left {left right factor : Purelib.Data.Rat.Fraction.Rational}
    (ordered : left ≤ right) (nonpositive : factor ≤ 0) : factor * right ≤ factor * left := by
  have nonnegative : 0 ≤ -factor := by
    simpa only [neg_zero] using neg_le_neg_direct nonpositive
  have reversed := neg_le_neg_direct
    (mul_le_mul_of_nonneg_left_direct ordered nonnegative)
  simpa only [neg_mul, neg_neg] using reversed

/-- Multiplication on the right by a nonpositive rational reverses weak comparison.

Commuting the two original products reduces the claim to multiplication
on the left by the same retained nonpositive factor. -/
public theorem mul_le_mul_of_nonpositive_right {left right factor : Purelib.Data.Rat.Fraction.Rational}
    (ordered : left ≤ right) (nonpositive : factor ≤ 0) : right * factor ≤ left * factor := by
  simpa only [Purelib.Data.Rat.Fraction.mul_comm] using
    mul_le_mul_of_nonpositive_left ordered nonpositive
end Purelib.Data.Rat.Fraction.Order.Arithmetic
end
