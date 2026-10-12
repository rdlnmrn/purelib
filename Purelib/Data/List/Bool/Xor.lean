module
public import Purelib.Data.Bool.Xor

public section

/-!
# Coordinatewise XOR of retained Boolean lists

Each paired head contributes its Boolean XOR in the same list order. The
operation stops at the shorter list; equal-width laws preserve the retained
spines and the all-false identity without constructing a function space.
-/

namespace Purelib.Data.List.Bool.Xor

open Purelib.Data.Bool

/-- Compute coordinatewise XOR up to the end of the shorter Boolean list.

Each paired head uses the retained bitXor operation. Once either input is exhausted
the result stops, making the operation total on unequal lengths as well. -/
@[expose] def bitsXor : List Bool → List Bool → List Bool
  | left :: leftTail, right :: rightTail =>
      Xor.bitXor left right :: Purelib.Data.List.Bool.Xor.bitsXor leftTail rightTail
  | [], _ => []
  | _ :: _, [] => []

/-- Coordinatewise XOR of equal-length Boolean lists has their common length.

The proof follows the retained list spines and Boolean head identities. The stated length condition keeps every
coordinate paired with its corresponding input. -/
theorem bitsXor_length_of_eq {left right : List Bool}
    (lengthEq : left.length = right.length) :
    (bitsXor left right).length = left.length := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => nomatch lengthEq
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => nomatch lengthEq
      | cons rightHead rightTail =>
          simp only [List.length_cons] at lengthEq ⊢
          unfold bitsXor
          simp only [List.length_cons]
          rw [inductionHypothesis (Nat.succ.inj lengthEq)]

/-- Coordinatewise XOR commutes on equal-length Boolean lists.

The proof follows the retained list spines and Boolean head identities. The stated length condition keeps every
coordinate paired with its corresponding input. -/
theorem bitsXor_comm_of_length_eq {left right : List Bool}
    (lengthEq : left.length = right.length) :
    bitsXor left right = bitsXor right left := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => nomatch lengthEq
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => nomatch lengthEq
      | cons rightHead rightTail =>
          simp only [List.length_cons] at lengthEq
          exact (congrArg (fun head => head :: bitsXor leftTail rightTail)
            (Xor.bitXor_comm_direct leftHead rightHead)).trans
            (congrArg (List.cons (Xor.bitXor rightHead leftHead))
              (inductionHypothesis (Nat.succ.inj lengthEq)))

/-- Coordinatewise XOR associates on three Boolean lists of the same length.

The proof follows the retained list spines and Boolean head identities. The stated length condition keeps every
coordinate paired with its corresponding input. -/
theorem bitsXor_assoc_of_lengths
    {first second third : List Bool}
    (firstSecond : first.length = second.length)
    (secondThird : second.length = third.length) :
    bitsXor (bitsXor first second) third =
      bitsXor first (bitsXor second third) := by
  induction first generalizing second third with
  | nil =>
      cases second with
      | nil =>
          cases third with
          | nil => rfl
          | cons _ _ => nomatch secondThird
      | cons _ _ => nomatch firstSecond
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | nil => nomatch firstSecond
      | cons secondHead secondTail =>
          cases third with
          | nil => nomatch secondThird
          | cons thirdHead thirdTail =>
              simp only [List.length_cons] at firstSecond secondThird
              exact (congrArg (fun head => head :: bitsXor (bitsXor firstTail secondTail) thirdTail)
                (Xor.bitXor_assoc_direct firstHead secondHead thirdHead)).trans
                (congrArg (List.cons (Xor.bitXor firstHead (Xor.bitXor secondHead thirdHead)))
                  (inductionHypothesis (Nat.succ.inj firstSecond)
                    (Nat.succ.inj secondThird)))

/-- A Boolean list XORed with itself is the equal-length all-false list.

Each paired head has Boolean XOR equal to false. The retained tail recurses in
its original order, producing exactly one false entry per original coordinate. -/
theorem bitsXor_self_eq_false : ∀ values : List Bool,
    bitsXor values values = List.replicate values.length false
  | [] => rfl
  | head :: tail => by
      exact (congrArg (fun value => value :: bitsXor tail tail)
        (Xor.bitXor_self_direct head)).trans
        (congrArg (List.cons false) (Purelib.Data.List.Bool.Xor.bitsXor_self_eq_false tail))

/-- An equal-length all-false left input is an identity for coordinatewise XOR.

The proof follows the retained list spines and Boolean head identities. The stated length condition keeps every
coordinate paired with its corresponding input. -/
theorem false_bitsXor : ∀ values : List Bool,
    bitsXor (List.replicate values.length false) values = values
  | [] => rfl
  | head :: tail => by
      simp only [List.length_cons, List.replicate_succ, bitsXor, Xor.bitXor]
      rw [Purelib.Data.List.Bool.Xor.false_bitsXor tail]

/-- An equal-length all-false right input is an identity for coordinatewise XOR.

The proof follows the retained list spines and Boolean head identities. The stated length condition keeps every
coordinate paired with its corresponding input. -/
theorem bitsXor_false : ∀ values : List Bool,
    bitsXor values (List.replicate values.length false) = values
  | [] => rfl
  | head :: tail => by
      simp only [List.length_cons, List.replicate_succ, bitsXor]
      rw [Xor.bitXor_comm_direct head false, Xor.bitXor, Purelib.Data.List.Bool.Xor.bitsXor_false tail]

end Purelib.Data.List.Bool.Xor
