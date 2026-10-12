module

public import Purelib.Data.Rat.Sign.Jump
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.Basic
import Mathlib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Group.Even
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.NatCast

/-!
# Doubled variation of finite rational lists

Adjacent natural sign distances determine doubled variation. Finite structural
recursion retains list order, alternating factors and the terminal coordinate;
direct integer identities certify the corresponding endpoint parity.
-/

namespace Purelib.Data.Rat.Sign.Variation

open Purelib.Data.Rat

/-- Sum the doubled sign changes across all adjacent entries of a finite rational list.

Each adjacent jump is the natural absolute difference of two integer signs. Equal signs contribute zero, zero-to-nonzero
transitions contribute one, and opposite nonzero signs contribute two. -/
@[expose] public def variation2 : List Fraction.Rational → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: values => Sign.Jump.signJump x y + Purelib.Data.Rat.Sign.Variation.variation2 (y :: values)

/-- The empty rational list has zero doubled sign variation. -/
@[simp] public theorem variation2_nil : Sign.Variation.variation2 [] = 0 := rfl

/-- A singleton rational list has zero doubled sign variation. -/
@[simp] public theorem variation2_singleton (x : Fraction.Rational) : Sign.Variation.variation2 [x] = 0 := rfl

/-- Pointwise equality of integer signs across related lists preserves their doubled sign variation. -/
public theorem variation2_congr_of_forall₂_sign :
    ∀ {xs ys : List Fraction.Rational},
      List.Forall₂ (fun x y => Sign.Basic.sign x = Sign.Basic.sign y) xs ys →
        Sign.Variation.variation2 xs = Sign.Variation.variation2 ys
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | x :: x' :: xs, y :: y' :: ys,
      List.Forall₂.cons hxy (List.Forall₂.cons hxy' tail) => by
      rw [Sign.Variation.variation2, Sign.Variation.variation2, Sign.Jump.signJump_congr hxy hxy',
        Purelib.Data.Rat.Sign.Variation.variation2_congr_of_forall₂_sign (List.Forall₂.cons hxy' tail)]

/-- Replacing one interior coordinate preserves total variation when both adjacent jumps have the same total and the
surrounding signs agree.

The retained prefixes and suffixes have entrywise equal signs. The supplied
local equality identifies the two affected jumps, leaving every other edge
unchanged. -/
public theorem variation2_eq_of_middle_change
    {prefixA prefixB suffixA suffixB : List Fraction.Rational}
    {leftA leftB middleA middleB rightA rightB : Fraction.Rational}
    (prefixSigns :
      List.Forall₂ (fun x y => Sign.Basic.sign x = Sign.Basic.sign y) prefixA prefixB)
    (suffixSigns :
      List.Forall₂ (fun x y => Sign.Basic.sign x = Sign.Basic.sign y) suffixA suffixB)
    (leftSign : Sign.Basic.sign leftA = Sign.Basic.sign leftB)
    (rightSign : Sign.Basic.sign rightA = Sign.Basic.sign rightB)
    (localEquality :
      Sign.Jump.signJump leftA middleA + Sign.Jump.signJump middleA rightA =
        Sign.Jump.signJump leftB middleB + Sign.Jump.signJump middleB rightB) :
    Sign.Variation.variation2 (prefixA ++ leftA :: middleA :: rightA :: suffixA) =
      Sign.Variation.variation2 (prefixB ++ leftB :: middleB :: rightB :: suffixB) := by
  induction prefixSigns with
  | nil =>
      have tailSigns := Sign.Variation.variation2_congr_of_forall₂_sign
        (List.Forall₂.cons rightSign suffixSigns)
      simp only [List.nil_append, Sign.Variation.variation2]
      have combined := congrArg₂ (· + ·) localEquality tailSigns
      simpa only [Nat.add_assoc] using combined
  | @cons headA headB prefixA prefixB headSign prefixSigns inductionHypothesis =>
      cases prefixSigns with
      | nil =>
          have recursive' :
              Sign.Variation.variation2 (leftA :: middleA :: rightA :: suffixA) =
                Sign.Variation.variation2 (leftB :: middleB :: rightB :: suffixB) := by
            simpa only [List.nil_append] using inductionHypothesis
          change Sign.Jump.signJump headA leftA +
              Sign.Variation.variation2 (leftA :: middleA :: rightA :: suffixA) =
            Sign.Jump.signJump headB leftB +
              Sign.Variation.variation2 (leftB :: middleB :: rightB :: suffixB)
          rw [Sign.Jump.signJump_congr headSign leftSign, recursive']
      | @cons nextA nextB tailA tailB nextSign tailSigns =>
          change Sign.Jump.signJump headA nextA +
              Sign.Variation.variation2
                (nextA :: tailA ++ leftA :: middleA :: rightA :: suffixA) =
            Sign.Jump.signJump headB nextB +
              Sign.Variation.variation2
                (nextB :: tailB ++ leftB :: middleB :: rightB :: suffixB)
          rw [Sign.Jump.signJump_congr headSign nextSign, inductionHypothesis]

/-- Negating every entry preserves doubled sign variation.

Simultaneous negation preserves each adjacent sign distance and retains the
original list order, so the structural variation recursion agrees. -/
public theorem variation2_map_neg : ∀ values : List Fraction.Rational,
    Sign.Variation.variation2 (values.map (-·)) = Sign.Variation.variation2 values
  | [] => rfl
  | [_] => rfl
  | x :: y :: values => by
      simp only [List.map_cons, Sign.Variation.variation2, Sign.Jump.signJump_neg_neg]
      exact congrArg (Sign.Jump.signJump x y + ·) (Purelib.Data.Rat.Sign.Variation.variation2_map_neg (y :: values))

/-- Multiply successive list entries alternately by the two supplied rational factors.

The recursion multiplies the head by the first factor and swaps the factors before processing the tail. It retains the
input list order and length. -/
@[expose] public def alternatingMul (a b : Fraction.Rational) : List Fraction.Rational → List Fraction.Rational
  | [] => []
  | x :: values => a * x :: Purelib.Data.Rat.Sign.Variation.alternatingMul b a values

/-- Require every pair of adjacent rational list entries to contain a nonzero value.

The empty and singleton lists satisfy the condition. At each longer list, retain explicit evidence that one of the first
two entries is nonzero and recursively check the remaining adjacent pairs. -/
@[expose] public def NoAdjacentZero : List Fraction.Rational → Prop
  | [] => True
  | [_] => True
  | x :: y :: values => (x ≠ 0 ∨ y ≠ 0) ∧ Purelib.Data.Rat.Sign.Variation.NoAdjacentZero (y :: values)

/-- For opposite-sign multipliers and no adjacent zeros, original and alternately multiplied variations sum to twice the
number of list edges.

Each original list edge contributes together with its alternately scaled edge exactly two. The no-adjacent-zero
condition excludes the single edge case where both original signs vanish. -/
public theorem variation2_add_alternatingMul {a b : Fraction.Rational} (hab : a * b < 0) :
    ∀ values : List Fraction.Rational, Sign.Variation.NoAdjacentZero values →
      Sign.Variation.variation2 values + Sign.Variation.variation2 (Sign.Variation.alternatingMul a b values) =
        2 * (values.length - 1)
  | [], _ => rfl
  | [_], _ => by
      change (0 : Nat) + 0 = 2 * (1 - 1)
      decide
  | x :: y :: values, valid => by
      have hlocal := Sign.Jump.signJump_add_signJump_mul_of_mul_neg hab valid.1
      have tail := Purelib.Data.Rat.Sign.Variation.variation2_add_alternatingMul (a := b) (b := a)
        (by simpa [mul_comm] using hab) (y :: values) valid.2
      simp only [Sign.Variation.alternatingMul, Sign.Variation.variation2, List.length_cons] at tail ⊢
      omega

/-- Return the last entry of the nonempty list given by a head and tail. -/
@[expose] public def terminalValue (x : Fraction.Rational) : List Fraction.Rational → Fraction.Rational
  | [] => x
  | y :: values => Purelib.Data.Rat.Sign.Variation.terminalValue y values

/-- The doubled variation of a nonempty list differs from its endpoint sign difference by an even integer.

The explicit even witness is built from the original adjacent-jump witnesses
and the retained terminal coordinate by structural induction on the tail. -/
public theorem variation2_sub_signDifference_even :
    ∀ (x : Fraction.Rational) (values : List Fraction.Rational),
      Even (((Sign.Variation.variation2 (x :: values) : Nat) : Int) -
        (Sign.Basic.sign x - Sign.Basic.sign (Sign.Variation.terminalValue x values)))
  | x, [] => by
      refine ⟨0, ?_⟩
      change (0 : Int) - (Sign.Basic.sign x - Sign.Basic.sign x) = 0 + 0
      ring1
  | x, y :: values => by
      rcases Sign.Jump.signJump_sub_signDifference_even x y with ⟨a, ha⟩
      rcases Purelib.Data.Rat.Sign.Variation.variation2_sub_signDifference_even y values with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rewrite [Sign.Variation.variation2, Sign.Variation.terminalValue, Purelib.Algebra.NatCast.add]
      calc
        ((Sign.Jump.signJump x y : Nat) : Int) +
              ((Sign.Variation.variation2 (y :: values) : Nat) : Int) -
            (Sign.Basic.sign x - Sign.Basic.sign (Sign.Variation.terminalValue y values)) =
            (((Sign.Jump.signJump x y : Nat) : Int) - (Sign.Basic.sign x - Sign.Basic.sign y)) +
              (((Sign.Variation.variation2 (y :: values) : Nat) : Int) -
                (Sign.Basic.sign y - Sign.Basic.sign (Sign.Variation.terminalValue y values))) := by ring1
        _ = (a + a) + (b + b) := by rw [ha, hb]
        _ = (a + b) + (a + b) := by ring1

/-- For a nonzero terminal coordinate, the endpoint sign difference minus the initial zero flag is even.

A nonzero terminal value has sign minus one or one. The initial zero case
uses the corresponding explicit even witness; the nonzero case retains the
existing endpoint sign-difference witness. -/
public theorem sign_sub_terminal_sub_zeroFlag_even
    {x y : Fraction.Rational} (hy : y ≠ 0) :
    Even ((Sign.Basic.sign x - Sign.Basic.sign y) - (if x = 0 then 1 else 0)) := by
  by_cases hx : x = 0
  · subst x
    rcases lt_or_gt_of_ne hy with hy | hy
    · refine ⟨0, ?_⟩
      rewrite [Sign.Basic.sign_zero, Sign.Basic.sign_of_neg hy, if_pos (Eq.refl _)]
      decide
    · refine ⟨-1, ?_⟩
      rewrite [Sign.Basic.sign_zero, Sign.Basic.sign_of_pos hy, if_pos (Eq.refl _)]
      decide
  · rewrite [if_neg hx]
    have difference :
        (Sign.Basic.sign x - Sign.Basic.sign y) - (0 : Int) =
          Sign.Basic.sign x - Sign.Basic.sign y := by ring1
    rewrite [difference]
    exact Sign.Basic.sign_sub_even_of_ne_zero hx hy

end Purelib.Data.Rat.Sign.Variation
