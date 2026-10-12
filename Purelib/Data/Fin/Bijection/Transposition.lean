module

public import Purelib.Data.Fin.Bijection.Basic

/-!
# Transpositions on retained finite indices

Two equality tests exchange the selected coordinates and fix every other
coordinate. The same map in both directions supplies an explicit bijection;
pointwise laws certify involution, disjoint commutation and the braid relation.
-/

namespace Purelib.Data.Fin.Bijection.Transposition

open Purelib.Data.Fin.Bijection
open Purelib.Data.Fin.Bijection.Basic

public section

/-- Swap two displayed finite indices and fix every other index.

Equality tests select the two exceptional cases. The operation is total even when the
two selected indices coincide, and applying it twice is identity. -/
@[expose] def swapIndices {count : Nat} (left right index : Fin count) : Fin count :=
  if index = left then right else if index = right then left else index

/-- The finite swap sends its left selected index to its right selected index. -/
@[simp] theorem swapIndices_left {count : Nat} (left right : Fin count) :
    Transposition.swapIndices left right left = right := by
  unfold Transposition.swapIndices
  rw [if_pos rfl]

/-- The finite swap sends its right selected index to its left selected index. -/
theorem swapIndices_right {count : Nat} (left right : Fin count) :
    Transposition.swapIndices left right right = left := by
  unfold Transposition.swapIndices
  by_cases same : right = left
  · rw [if_pos same]
    exact same
  · rw [if_neg same, if_pos rfl]

/-- A finite swap fixes an index different from both selected indices. -/
theorem swapIndices_of_ne {count : Nat} {left right index : Fin count}
    (notLeft : index ≠ left) (notRight : index ≠ right) :
    Transposition.swapIndices left right index = index := by
  unfold Transposition.swapIndices
  rw [if_neg notLeft, if_neg notRight]

/-- Applying the same finite swap twice recovers every original index. -/
@[simp] theorem swapIndices_involutive {count : Nat}
    (left right index : Fin count) :
    Transposition.swapIndices left right (Transposition.swapIndices left right index) = index := by
  by_cases atLeft : index = left
  · subst index
    rw [Transposition.swapIndices_left, Transposition.swapIndices_right]
  · by_cases atRight : index = right
    · subst index
      rw [Transposition.swapIndices_right, Transposition.swapIndices_left]
    · rw [Transposition.swapIndices_of_ne atLeft atRight,
        Transposition.swapIndices_of_ne atLeft atRight]

/-- Package a finite swap as an explicit bijection with the same map in both directions.

The swap's pointwise involution law supplies both retained inverse laws, including
the case of two coincident selected indices. -/
@[expose] def transposition {count : Nat} (left right : Fin count) :
    Bijection count count where
  forward := Transposition.swapIndices left right
  backward := Transposition.swapIndices left right
  backward_forward := Transposition.swapIndices_involutive left right
  forward_backward := Transposition.swapIndices_involutive left right

/-- The retained forward map of a transposition is its explicit finite swap. -/
@[simp] theorem transposition_forward {count : Nat}
    (left right index : Fin count) :
    (Transposition.transposition left right).forward index = Transposition.swapIndices left right index :=
  rfl

/-- Reversing a transposition preserves its forward map pointwise. -/
theorem transposition_reverse {count : Nat} (left right : Fin count) :
    Bijection.Same
      (Transposition.transposition left right).reverse
      (Transposition.transposition left right) :=
  fun _ => rfl

/-- Finite swaps on disjoint selected pairs commute at every index.

The four supplied inequalities separate the two pairs. Each index is one of their
selected entries or is fixed by both swaps. -/
theorem swapIndices_commute_of_disjoint {count : Nat}
    {firstLeft firstRight secondLeft secondRight : Fin count}
    (leftLeft : firstLeft ≠ secondLeft)
    (leftRight : firstLeft ≠ secondRight)
    (rightLeft : firstRight ≠ secondLeft)
    (rightRight : firstRight ≠ secondRight)
    (index : Fin count) :
    Transposition.swapIndices secondLeft secondRight
        (Transposition.swapIndices firstLeft firstRight index) =
      Transposition.swapIndices firstLeft firstRight
        (Transposition.swapIndices secondLeft secondRight index) := by
  by_cases atFirstLeft : index = firstLeft
  · subst index
    calc
      Transposition.swapIndices secondLeft secondRight
          (Transposition.swapIndices firstLeft firstRight firstLeft) =
        Transposition.swapIndices secondLeft secondRight firstRight := by
          rw [Transposition.swapIndices_left]
      _ = firstRight := Transposition.swapIndices_of_ne rightLeft rightRight
      _ = Transposition.swapIndices firstLeft firstRight firstLeft :=
        (Transposition.swapIndices_left firstLeft firstRight).symm
      _ = Transposition.swapIndices firstLeft firstRight
          (Transposition.swapIndices secondLeft secondRight firstLeft) := by
        rw [Transposition.swapIndices_of_ne leftLeft leftRight]
  · by_cases atFirstRight : index = firstRight
    · subst index
      calc
        Transposition.swapIndices secondLeft secondRight
            (Transposition.swapIndices firstLeft firstRight firstRight) =
          Transposition.swapIndices secondLeft secondRight firstLeft := by
            rw [Transposition.swapIndices_right]
        _ = firstLeft := Transposition.swapIndices_of_ne leftLeft leftRight
        _ = Transposition.swapIndices firstLeft firstRight firstRight :=
          (Transposition.swapIndices_right firstLeft firstRight).symm
        _ = Transposition.swapIndices firstLeft firstRight
            (Transposition.swapIndices secondLeft secondRight firstRight) := by
          rw [Transposition.swapIndices_of_ne rightLeft rightRight]
    · by_cases atSecondLeft : index = secondLeft
      · subst index
        calc
          Transposition.swapIndices secondLeft secondRight
              (Transposition.swapIndices firstLeft firstRight secondLeft) =
            Transposition.swapIndices secondLeft secondRight secondLeft := by
              rw [Transposition.swapIndices_of_ne leftLeft.symm rightLeft.symm]
          _ = secondRight := Transposition.swapIndices_left secondLeft secondRight
          _ = Transposition.swapIndices firstLeft firstRight secondRight :=
            (Transposition.swapIndices_of_ne leftRight.symm rightRight.symm).symm
          _ = Transposition.swapIndices firstLeft firstRight
              (Transposition.swapIndices secondLeft secondRight secondLeft) := by
            rw [Transposition.swapIndices_left]
      · by_cases atSecondRight : index = secondRight
        · subst index
          calc
            Transposition.swapIndices secondLeft secondRight
                (Transposition.swapIndices firstLeft firstRight secondRight) =
              Transposition.swapIndices secondLeft secondRight secondRight := by
                rw [Transposition.swapIndices_of_ne leftRight.symm rightRight.symm]
            _ = secondLeft := Transposition.swapIndices_right secondLeft secondRight
            _ = Transposition.swapIndices firstLeft firstRight secondLeft :=
              (Transposition.swapIndices_of_ne leftLeft.symm rightLeft.symm).symm
            _ = Transposition.swapIndices firstLeft firstRight
                (Transposition.swapIndices secondLeft secondRight secondRight) := by
              rw [Transposition.swapIndices_right]
        · calc
          Transposition.swapIndices secondLeft secondRight
              (Transposition.swapIndices firstLeft firstRight index) =
            Transposition.swapIndices secondLeft secondRight index := by
              rw [Transposition.swapIndices_of_ne atFirstLeft atFirstRight]
          _ = index := Transposition.swapIndices_of_ne atSecondLeft atSecondRight
          _ = Transposition.swapIndices firstLeft firstRight index :=
            (Transposition.swapIndices_of_ne atFirstLeft atFirstRight).symm
          _ = Transposition.swapIndices firstLeft firstRight
              (Transposition.swapIndices secondLeft secondRight index) := by
            rw [Transposition.swapIndices_of_ne atSecondLeft atSecondRight]

/-- Swaps on two overlapping pairs satisfy the three-step braid relation.

The three displayed indices must be pairwise distinct. Both composites agree on these
three indices and fix every other index. -/
theorem swapIndices_braid {count : Nat} {left middle right : Fin count}
    (leftMiddle : left ≠ middle) (leftRight : left ≠ right)
    (middleRight : middle ≠ right) (index : Fin count) :
    Transposition.swapIndices left middle
        (Transposition.swapIndices middle right (Transposition.swapIndices left middle index)) =
      Transposition.swapIndices middle right
        (Transposition.swapIndices left middle (Transposition.swapIndices middle right index)) := by
  by_cases atLeft : index = left
  · subst index
    have leftEvaluation :
        Transposition.swapIndices left middle
            (Transposition.swapIndices middle right (Transposition.swapIndices left middle left)) =
          right := by
      calc
        _ = Transposition.swapIndices left middle
            (Transposition.swapIndices middle right middle) := by rw [Transposition.swapIndices_left]
        _ = Transposition.swapIndices left middle right := by rw [Transposition.swapIndices_left]
        _ = right := Transposition.swapIndices_of_ne leftRight.symm middleRight.symm
    have rightEvaluation :
        Transposition.swapIndices middle right
            (Transposition.swapIndices left middle (Transposition.swapIndices middle right left)) =
          right := by
      calc
        _ = Transposition.swapIndices middle right (Transposition.swapIndices left middle left) := by
          rw [Transposition.swapIndices_of_ne leftMiddle leftRight]
        _ = Transposition.swapIndices middle right middle := by rw [Transposition.swapIndices_left]
        _ = right := Transposition.swapIndices_left middle right
    exact leftEvaluation.trans rightEvaluation.symm
  · by_cases atMiddle : index = middle
    · subst index
      have leftEvaluation :
          Transposition.swapIndices left middle
              (Transposition.swapIndices middle right
                (Transposition.swapIndices left middle middle)) = middle := by
        calc
          _ = Transposition.swapIndices left middle
              (Transposition.swapIndices middle right left) := by rw [Transposition.swapIndices_right]
          _ = Transposition.swapIndices left middle left := by
            rw [Transposition.swapIndices_of_ne leftMiddle leftRight]
          _ = middle := Transposition.swapIndices_left left middle
      have rightEvaluation :
          Transposition.swapIndices middle right
              (Transposition.swapIndices left middle
                (Transposition.swapIndices middle right middle)) = middle := by
        calc
          _ = Transposition.swapIndices middle right
              (Transposition.swapIndices left middle right) := by rw [Transposition.swapIndices_left]
          _ = Transposition.swapIndices middle right right := by
            rw [Transposition.swapIndices_of_ne leftRight.symm middleRight.symm]
          _ = middle := Transposition.swapIndices_right middle right
      exact leftEvaluation.trans rightEvaluation.symm
    · by_cases atRight : index = right
      · subst index
        have leftEvaluation :
            Transposition.swapIndices left middle
                (Transposition.swapIndices middle right
                  (Transposition.swapIndices left middle right)) = left := by
          calc
            _ = Transposition.swapIndices left middle
                (Transposition.swapIndices middle right right) := by
              rw [Transposition.swapIndices_of_ne leftRight.symm middleRight.symm]
            _ = Transposition.swapIndices left middle middle := by rw [Transposition.swapIndices_right]
            _ = left := Transposition.swapIndices_right left middle
        have rightEvaluation :
            Transposition.swapIndices middle right
                (Transposition.swapIndices left middle
                  (Transposition.swapIndices middle right right)) = left := by
          calc
            _ = Transposition.swapIndices middle right
                (Transposition.swapIndices left middle middle) := by rw [Transposition.swapIndices_right]
            _ = Transposition.swapIndices middle right left := by rw [Transposition.swapIndices_right]
            _ = left := Transposition.swapIndices_of_ne leftMiddle leftRight
        exact leftEvaluation.trans rightEvaluation.symm
      · have firstFixed : Transposition.swapIndices left middle index = index :=
          Transposition.swapIndices_of_ne atLeft atMiddle
        have secondFixed : Transposition.swapIndices middle right index = index :=
          Transposition.swapIndices_of_ne atMiddle atRight
        have leftFixed :
            Transposition.swapIndices left middle
              (Transposition.swapIndices middle right
                (Transposition.swapIndices left middle index)) = index :=
          (congrArg (fun value => Transposition.swapIndices left middle
              (Transposition.swapIndices middle right value)) firstFixed).trans
            ((congrArg (Transposition.swapIndices left middle) secondFixed).trans firstFixed)
        have rightFixed :
            Transposition.swapIndices middle right
              (Transposition.swapIndices left middle
                (Transposition.swapIndices middle right index)) = index :=
          (congrArg (fun value => Transposition.swapIndices middle right
              (Transposition.swapIndices left middle value)) secondFixed).trans
            ((congrArg (Transposition.swapIndices middle right) firstFixed).trans secondFixed)
        exact leftFixed.trans rightFixed.symm

end

end Purelib.Data.Fin.Bijection.Transposition
