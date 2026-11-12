module

public import Purelib.Data.Fin
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.Ring

/-!
# Finite leading-coordinate transpositions

The displayed pivot exchanges with the first finite coordinate. Its original
involution and finite-sum identities retain every bounded coordinate.
-/

public section

namespace Purelib.Data.Fin

open Purelib.Algebra

/-- Swap index zero with one displayed pivot index. -/
@[expose] def swapZero {size : Nat} (pivot index : Fin (size + 1)) : Fin (size + 1) :=
  if index = 0 then pivot else if index = pivot then 0 else index

/-- The transposition sends the leading coordinate to its retained pivot.

The first scalar equality test succeeds at that same coordinate, so the
original conditional construction returns its supplied pivot. -/
@[simp] theorem swapZero_zero {size : Nat} (pivot : Fin (size + 1)) :
    swapZero pivot 0 = pivot := by
  unfold swapZero
  rewrite [if_pos (Eq.refl (0 : Fin (size + 1)))]
  exact Eq.refl _

/-- The transposition sends its retained pivot to the leading coordinate.

A pivot already at the leading coordinate is retained. Otherwise the first
comparison fails and the second comparison selects the original zero index. -/
theorem swapZero_pivot {size : Nat} (pivot : Fin (size + 1)) :
    swapZero pivot pivot = 0 := by
  unfold swapZero
  by_cases pivotZero : pivot = 0
  · rewrite [if_pos pivotZero]
    exact pivotZero
  · rewrite [if_neg pivotZero, if_pos (Eq.refl pivot)]
    exact Eq.refl _

/-- The transposition fixes coordinates distinct from zero and its pivot.

The two supplied inequalities reject the original conditional branches.
The remaining branch retains the original bounded coordinate. -/
theorem swapZero_of_ne {size : Nat} {pivot index : Fin (size + 1)}
    (indexZero : index ≠ 0) (indexPivot : index ≠ pivot) :
    swapZero pivot index = index := by
  unfold swapZero
  rewrite [if_neg indexZero, if_neg indexPivot]
  exact Eq.refl _

/-- Applying the transposition twice restores the original coordinate.

The leading and pivot cases exchange those two retained positions. Every
other finite coordinate is fixed by both applications. -/
@[simp] theorem swapZero_involutive {size : Nat}
    (pivot index : Fin (size + 1)) :
    swapZero pivot (swapZero pivot
      index) = index := by
  by_cases indexZero : index = 0
  · cases indexZero
    rewrite [swapZero_zero,
      swapZero_pivot]
    exact Eq.refl _
  · by_cases indexPivot : index = pivot
    · cases indexPivot
      rewrite [swapZero_pivot,
        swapZero_zero]
      exact Eq.refl _
    · rewrite [swapZero_of_ne indexZero indexPivot,
        swapZero_of_ne indexZero indexPivot]
      exact Eq.refl _

/-- The displayed transposition is injective on the retained finite index type. -/
theorem swapZero_injective {size : Nat} (pivot : Fin (size + 1))
    {left right : Fin (size + 1)}
    (equal : swapZero pivot left =
      swapZero pivot right) : left = right := by
  have reapplied := congrArg (swapZero pivot) equal
  simpa only [swapZero_involutive] using reapplied

/-- A finite commutative sum is invariant under the displayed transposition.

The two retained correction functions isolate the leading and pivot entries.
Their original finite sums cancel, leaving all other summands unchanged. -/
theorem sumFin_swapZero {K : Type*} [CommRing K] {size : Nat}
    (pivot : Fin (size + 1)) (values : Fin (size + 1) → K) :
    FiniteSum.Fin.sumFin
        (fun index => values (swapZero pivot index)) =
      FiniteSum.Fin.sumFin values := by
  by_cases pivotZero : pivot = 0
  · subst pivot
    apply FiniteSum.Fin.sumFin_congr
    intro index
    by_cases indexZero : index = 0
    · cases indexZero
      rewrite [swapZero_zero]
      exact Eq.refl _
    · rewrite [swapZero_of_ne indexZero indexZero]
      exact Eq.refl _
  · let correctionZero : Fin (size + 1) → K := fun index =>
      if index = 0 then values pivot - values 0 else 0
    let correctionPivot : Fin (size + 1) → K := fun index =>
      if index = pivot then values 0 - values pivot else 0
    have pointwise : forall index,
        values (swapZero pivot index) =
          values index + correctionZero index + correctionPivot index := by
      intro index
      by_cases indexZero : index = 0
      · subst index
        rewrite [swapZero_zero]
        dsimp only [correctionZero, correctionPivot]
        rewrite [if_pos (Eq.refl (0 : Fin (size + 1))), if_neg (Ne.symm pivotZero)]
        ring1
      · by_cases indexPivot : index = pivot
        · subst index
          rewrite [swapZero_pivot]
          dsimp only [correctionZero, correctionPivot]
          rewrite [if_neg pivotZero, if_pos (Eq.refl pivot)]
          ring1
        · rw [swapZero_of_ne indexZero indexPivot]
          dsimp only [correctionZero, correctionPivot]
          rewrite [if_neg indexZero, if_neg indexPivot]
          ring1
    rw [FiniteSum.Fin.sumFin_congr pointwise]
    rw [FiniteSum.Fin.sumFin_add,
      FiniteSum.Fin.sumFin_add]
    have zeroCorrection :
        FiniteSum.Fin.sumFin correctionZero =
          values pivot - values 0 := by
      unfold correctionZero
      exact FiniteSum.Fin.sumFin_ite_eq 0
        (fun _ => values pivot - values 0)
    have pivotCorrection :
        FiniteSum.Fin.sumFin correctionPivot =
          values 0 - values pivot := by
      unfold correctionPivot
      exact FiniteSum.Fin.sumFin_ite_eq pivot
        (fun _ => values 0 - values pivot)
    rw [zeroCorrection, pivotCorrection]
    ring1

end Purelib.Data.Fin
