module

import Purelib.Data.Int.Arithmetic

import Purelib.Tactic.Ring

import Lean.Elab.Tactic.Omega
meta import Lean.Elab.Tactic.Omega.Frontend
meta import Lean.Elab.Tactic.Omega.OmegaM

section

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

public section

namespace Purelib.Tactic.Omega.Coefficients

open Lean.Omega
open Purelib.Data.Int

/-- Read a finite coefficient coordinate, returning zero beyond the retained list.

Structural recursion reads the original list spine and natural index. An empty
list contributes zero, and a successor index consumes exactly one retained tail. -/
@[expose] def get : Coeffs → Nat → Int
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, index + 1 => get tail index

/-- Reduce a finite coordinate evaluation by its explicit list and integer equations.

This local tactic unfolds only the displayed coefficient constructors, dot product and scalar zero/one identities. -/
local macro "coordinate_rfl" : tactic =>
  `(tactic|
    simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith, Int.one_mul, Arithmetic.zero_mul, Int.add_zero,
      Arithmetic.zero_add])

/-- Right-zero law for Omega's padded pointwise list addition, proved by
structural recursion rather than function extensionality. -/
theorem intList_add_nil : ∀ values : IntList, values + [] = values
  | [] => rfl
  | head :: tail => by
      change List.map (fun value : Int => value + 0) (head :: tail) =
        head :: tail
      have tailEquality := intList_add_nil tail
      rw [IntList.add_def, List.zipWithAll_nil] at tailEquality
      change List.map (fun value : Int => value + 0) tail = tail at tailEquality
      rw [List.map, Int.add_zero, tailEquality]

/-- Left-zero law for Omega's padded pointwise list addition. -/
theorem intList_nil_add : ∀ values : IntList, [] + values = values
  | [] => rfl
  | head :: tail => by
      change (0 + head) :: ([] + tail) = head :: tail
      rw [Arithmetic.zero_add, intList_nil_add tail]

/-- Subtracting an empty padded coefficient list preserves every entry. -/
theorem intList_sub_nil : ∀ values : IntList, values - [] = values
  | [] => rfl
  | head :: tail => by
      change List.map (fun value : Int => value - 0) (head :: tail) =
        head :: tail
      have tailEquality := intList_sub_nil tail
      rw [IntList.sub_def, List.zipWithAll_nil] at tailEquality
      change List.map (fun value : Int => value - 0) tail = tail at tailEquality
      rw [List.map, Arithmetic.sub_zero, tailEquality]

section
open Purelib.Tactic
/-- Pointwise subtraction is addition of pointwise negation, proved directly
on the finite coefficient lists.

Padded subtraction retains the original ordered finite entries. At each coordinate
it equals adding the first entry to the negation of the second. -/
theorem intList_sub_eq_add_neg : ∀ left right : IntList,
    left - right = left + -right
  | [], [] => rfl
  | [], head :: tail => by
      change (0 - head) :: ([] - tail) =
        (0 + -head) :: ([] + -tail)
      rw [Arithmetic.zero_sub, Arithmetic.zero_add, intList_sub_eq_add_neg [] tail]
  | head :: tail, [] => by
      rw [intList_sub_nil, show -([] : IntList) = [] from rfl,
        intList_add_nil]
  | left :: leftTail, right :: rightTail => by
      change (left - right) :: (leftTail - rightTail) =
        (left + -right) :: (leftTail + -rightTail)
      rw [Int.sub_eq_add_neg,
        intList_sub_eq_add_neg leftTail rightTail]

/-- Dot product distributes over Omega's padded coefficient addition.

The original valuation list is retained in both dot products. Padded coefficient
addition distributes pointwise over the finite integer product sum. -/
theorem intList_dot_distrib_left : ∀ left right values : IntList,
    IntList.dot (left + right) values =
      IntList.dot left values + IntList.dot right values
  | [], right, values => by
      rw [intList_nil_add]
      change IntList.dot right values = 0 + IntList.dot right values
      rw [Arithmetic.zero_add]
  | left, [], values => by
      rw [intList_add_nil]
      change IntList.dot left values = IntList.dot left values + 0
      rw [Int.add_zero]
  | left :: leftTail, right :: rightTail, [] => by
      change 0 = 0 + 0
      rw [Arithmetic.zero_add]
  | left :: leftTail, right :: rightTail, value :: valueTail => by
      change (left + right) * value +
          IntList.dot (leftTail + rightTail) valueTail =
        (left * value + IntList.dot leftTail valueTail) +
          (right * value + IntList.dot rightTail valueTail)
      rw [intList_dot_distrib_left leftTail rightTail valueTail]
      ring1

end

/-- Negating a finite coefficient list negates its dot product.

The proof follows the two actual list spines and transports the current
integer product before recurring on their unchanged tails. -/
theorem intList_dot_neg_left :
    ∀ source values : IntList, IntList.dot (-source) values = -(IntList.dot source values)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | head :: tail, value :: values => by
      change -head * value + IntList.dot (-tail) values =
        -(head * value + IntList.dot tail values)
      rw [Arithmetic.neg_mul, intList_dot_neg_left tail values,
        Arithmetic.neg_add]

/-- Scaling a finite coefficient list scales its dot product.

The retained scalar multiplies each displayed coefficient once. Structural
recursion compares the same coefficient and valuation tails. -/
theorem intList_dot_smul_left (factor : Int) :
    ∀ source values : IntList,
      IntList.dot (factor * source) values = factor * IntList.dot source values
  | [], _ => (Int.mul_zero factor).symm
  | _ :: _, [] => (Int.mul_zero factor).symm
  | head :: tail, value :: values => by
      change (factor * head) * value + IntList.dot (factor * tail) values =
        factor * (head * value + IntList.dot tail values)
      rw [Arithmetic.mul_assoc, intList_dot_smul_left factor tail values,
        Arithmetic.mul_add]

/-- A finite coefficient vector whose every entry is zero has zero dot product.

The original membership certificate supplies the current head equality and
restricts to the same retained tail. Structural recursion removes one scalar
zero product at each displayed entry. -/
theorem intList_dot_of_left_zero
    (source values : IntList) (zeroEntries : Coeffs.isZero source) :
    IntList.dot source values = 0 := by
  induction source generalizing values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases values with
      | nil => rfl
      | cons value values =>
          have headZero : head = 0 := zeroEntries head (List.Mem.head tail)
          have tailZero : Coeffs.isZero tail :=
            fun entry member => zeroEntries entry (List.Mem.tail head member)
          change head * value + IntList.dot tail values = 0
          rw [headZero, Arithmetic.zero_mul, Arithmetic.zero_add]
          exact inductionHypothesis values tailZero

/-- Updating one displayed coefficient changes its dot product by exactly
the corresponding coordinate correction.

Replacing one coefficient changes the finite product sum by its original valuation
entry times the coefficient difference. All other retained coordinates contribute
the same terms. -/
theorem intList_dot_set_left : ∀ (source values : IntList)
    (index : Nat) (replacement : Int),
    IntList.dot (IntList.set source index replacement) values =
      IntList.dot source values +
        (replacement - get source index) *
          get values index
  | [], [], 0, replacement => by
      change 0 = 0 + (replacement - 0) * 0
      ring1
  | [], value :: values, 0, replacement => by
      change replacement * value + 0 =
        0 + (replacement - 0) * value
      ring1
  | [], [], index + 1, replacement => by
      change 0 = 0 + (replacement - 0) * 0
      ring1
  | [], value :: values, index + 1, replacement => by
      change 0 * value +
          IntList.dot (IntList.set [] index replacement) values =
        0 + (replacement - 0) * get values index
      rw [Arithmetic.zero_mul, Arithmetic.zero_add,
        intList_dot_set_left [] values index replacement]
      rfl
  | sourceHead :: sourceTail, [], 0, replacement => by
      change 0 = 0 + (replacement - sourceHead) * 0
      ring1
  | sourceHead :: sourceTail, value :: values, 0, replacement => by
      change replacement * value + IntList.dot sourceTail values =
        (sourceHead * value + IntList.dot sourceTail values) +
          (replacement - sourceHead) * value
      ring1
  | sourceHead :: sourceTail, [], index + 1, replacement => by
      change 0 = 0 +
        (replacement - get sourceTail index) * 0
      ring1
  | sourceHead :: sourceTail, value :: values, index + 1, replacement => by
      change sourceHead * value +
          IntList.dot (IntList.set sourceTail index replacement) values =
        (sourceHead * value + IntList.dot sourceTail values) +
          (replacement - get sourceTail index) *
            get values index
      rw [intList_dot_set_left sourceTail values index replacement]
      ring1

open Purelib.Tactic in
/-- `Coeffs` is the same finite integer-list representation, so the direct
update calculation applies without the upstream extensional list lemma. -/
theorem coeffs_dot_set_left (source values : Coeffs) (index : Nat)
    (replacement : Int) :
    Coeffs.dot (Coeffs.set source index replacement) values =
      Coeffs.dot source values +
        (replacement - get source index) * get values index :=
  intList_dot_set_left source values index replacement

/-- The map used by the empty-right branch of `IntList.combo` reduces
pointwise to scalar multiplication. -/
theorem intList_combo_map_nil_right (leftScale rightScale : Int) :
    ∀ left : List Int,
      List.map (fun value => leftScale * value + rightScale * 0) left =
        List.map (fun value => leftScale * value) left
  | [] => rfl
  | left :: leftTail => by
      change (leftScale * left + rightScale * 0) ::
          List.map (fun value => leftScale * value + rightScale * 0) leftTail =
        leftScale * left :: List.map (fun value => leftScale * value) leftTail
      rw [intList_combo_map_nil_right leftScale rightScale leftTail,
        Int.mul_zero, Int.add_zero]

section
open Purelib.Tactic
/-- Combining a coefficient list with an empty right-hand list is just scalar
multiplication.  This branch of `List.zipWithAll` is a map over the whole
left-hand list, so we expose that finite recursion explicitly. -/
theorem intList_combo_nil_right (leftScale rightScale : Int)
    (left : IntList) :
    IntList.combo leftScale left rightScale [] = leftScale * left := by
  rw [IntList.combo, List.zipWithAll_nil, IntList.smul_def]
  exact intList_combo_map_nil_right leftScale rightScale left

/-- Omega's coefficient combination is the displayed sum of two scalar
multiples, by recursion on the two finite lists.

The two displayed integer factors multiply their original coefficient lists.
Padded addition of those products gives the same finite combined coefficient
vector. -/
theorem intList_combo_eq_smul_add_smul (leftScale : Int) :
    ∀ left : IntList, ∀ rightScale : Int, ∀ right : IntList,
      IntList.combo leftScale left rightScale right =
        leftScale * left + rightScale * right
  | [], rightScale, [] => rfl
  | [], rightScale, right :: rightTail => by
      change (leftScale * 0 + rightScale * right) ::
          IntList.combo leftScale [] rightScale rightTail =
        [] + rightScale * (right :: rightTail)
      rw [Int.mul_zero, Arithmetic.zero_add, intList_nil_add]
      change rightScale * right ::
          IntList.combo leftScale [] rightScale rightTail =
        rightScale * right :: rightScale * rightTail
      rw [intList_combo_eq_smul_add_smul leftScale [] rightScale rightTail,
        show leftScale * ([] : IntList) = [] from rfl,
        intList_nil_add]
  | left :: leftTail, rightScale, [] => by
      rw [intList_combo_nil_right,
        show rightScale * ([] : IntList) = [] from rfl,
        intList_add_nil]
  | left :: leftTail, rightScale, right :: rightTail => by
      change (leftScale * left + rightScale * right) ::
          IntList.combo leftScale leftTail rightScale rightTail =
        (leftScale * left + rightScale * right) ::
          (leftScale * leftTail + rightScale * rightTail)
      rw [intList_combo_eq_smul_add_smul leftScale leftTail rightScale rightTail]

end

/-- A zero coefficient vector has zero dot product with every valuation,
proved by recursion on the displayed finite vectors.

Every retained coefficient is zero. The finite product sum therefore vanishes for
each supplied valuation list, including different list lengths. -/
theorem intList_dot_eq_zero_of_isZero : ∀ source values : Coeffs,
    source.isZero → IntList.dot source values = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | head :: tail, value :: values, allZero => by
      have headZero : head = 0 := by
        apply allZero head
        exact List.mem_cons_self
      have tailZero : Coeffs.isZero tail := by
        intro entry member
        apply allZero entry
        exact List.mem_cons_of_mem head member
      rw [headZero]
      change 0 * value + IntList.dot tail values = 0
      rw [Arithmetic.zero_mul, Arithmetic.zero_add,
        intList_dot_eq_zero_of_isZero tail values tailZero]
end Purelib.Tactic.Omega.Coefficients

end

end
