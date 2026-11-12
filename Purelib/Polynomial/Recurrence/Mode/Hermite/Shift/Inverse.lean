module

public import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift
public import Purelib.Polynomial.Recurrence.Mode.Inverse
import Purelib.Tactic.QuotientFreeOmega

/-!
# Partial inverse powers on the original occurrence coordinates

Only selected original root tags are inverted. The same original word and
retained predecessor table determine every finite coefficient; unselected
blocks contribute zero. This includes zero roots outside the selected part
without asserting a global inverse for the original transition.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite.Shift

open Purelib.Data.List (Occurrences)
open Purelib.Data renaming Vector → Vec
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] {Tag : Type*}

/-- Materialize the diagonal projector onto selected tags of the same original finite word. -/
@[expose] def projection (selected : Tag → Bool) (word : List Tag) : SquareMatrix K word.length :=
  matrixOfFn fun row column =>
    if selected (word[column.val]'column.isLt) = true then if row = column then 1 else 0 else 0

/-- The same original selected tag fixes every projector entry. -/
theorem projection_at (selected : Tag → Bool) (word : List Tag) (row column : Fin word.length) :
    projection (K := K) selected word row column =
      if selected (word[column.val]'column.isLt) = true then if row = column then 1 else 0 else 0 :=
  matrixOfFn_apply _ row column

/-- Applying the same original projector retains precisely its selected finite coordinates. -/
theorem projection_apply (selected : Tag → Bool) (word : List Tag) (values : Vec K word.length)
    (index : Fin word.length) : Rectangular.apply (projection selected word) values index =
      if selected (word[index.val]'index.isLt) = true then values index else 0 := by
  rewrite [Rectangular.apply_at]
  calc
    _ = sumFin (fun column => if column = index then
        (if selected (word[column.val]'column.isLt) = true then values column else 0) else 0) := by
      apply sumFin_congr
      intro column
      rewrite [projection_at]
      by_cases same : column = index
      · cases same
        rewrite [if_pos rfl]
        by_cases chosen : selected (word[index.val]'index.isLt) = true
        · rewrite [if_pos chosen, if_pos chosen, if_pos rfl, one_mul]
          rfl
        · rewrite [if_neg chosen, if_neg chosen, zero_mul, if_pos rfl]
          rfl
      · rewrite [if_neg same]
        by_cases chosen : selected (word[column.val]'column.isLt) = true
        · rewrite [if_pos chosen, if_neg (Ne.symm same), zero_mul]
          rfl
        · rewrite [if_neg chosen, zero_mul]
          rfl
    _ = _ := sumFin_ite_eq index _

variable [DecidableEq Tag]

/-- Materialize selected inverse coefficients on the same retained original occurrence coordinates.

Only equal original tags with increasing occurrence order contribute.
Unselected tags contribute zero, so their original roots need no inverse.
The retained inverse lookup is consumed by the original reciprocal-mode
coefficient producer without reconstructing a word or predecessor table.
-/
@[expose] def inversePower (inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word) (steps : Nat) : SquareMatrix K word.length :=
  matrixOfFn fun row column =>
    if selected (word[column.val]'column.isLt) = true then
      if word[row.val]'row.isLt = word[column.val]'column.isLt then
        if occurrences.orders row ≤ occurrences.orders column then
          inverseEntry (inverses (word[column.val]'column.isLt))
            (occurrences.orders column - occurrences.orders row) steps
        else 0
      else 0
    else 0

/-- Every partial inverse entry reads its same selected tag, cached orders and retained reciprocal. -/
theorem inversePower_at (inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word) (steps : Nat) (row column : Fin word.length) :
    inversePower inverses selected word occurrences steps row column =
      if selected (word[column.val]'column.isLt) = true then
        if word[row.val]'row.isLt = word[column.val]'column.isLt then
          if occurrences.orders row ≤ occurrences.orders column then
            inverseEntry (inverses (word[column.val]'column.isLt))
              (occurrences.orders column - occurrences.orders row) steps
          else 0
        else 0
      else 0 := matrixOfFn_apply _ row column

/-- The zero partial inverse power is exactly the same original selected-coordinate projector. -/
theorem inversePower_zero (inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word) :
    inversePower inverses selected word occurrences 0 = projection selected word := by
  apply matrix_ext
  intro row column
  rewrite [inversePower_at, projection_at]
  by_cases chosen : selected (word[column.val]'column.isLt) = true
  · rewrite [if_pos chosen, if_pos chosen]
    by_cases same : row = column
    · cases same
      rewrite [if_pos rfl, if_pos (Nat.le_refl _), Nat.sub_self, inverseEntry, if_pos rfl, if_pos rfl]
      rfl
    · rewrite [if_neg same]
      by_cases tags : word[row.val]'row.isLt = word[column.val]'column.isLt
      · rewrite [if_pos tags]
        by_cases ordered : occurrences.orders row ≤ occurrences.orders column
        · rewrite [if_pos ordered, inverseEntry]
          have different : occurrences.orders column - occurrences.orders row ≠ 0 := by
            intro zero
            have equal : occurrences.orders row = occurrences.orders column := by omega0
            exact same (occurrences.eq_of_tag_order_eq row column tags equal)
          rewrite [if_neg different]
          rfl
        · rewrite [if_neg ordered]
          rfl
      · rewrite [if_neg tags]
        rfl
  · rewrite [if_neg chosen, if_neg chosen]
    rfl

/-- Multiplication by the same original transition removes one selected inverse step.

Root-unit equations are required only at selected original occurrences.
The retained predecessor supplies exactly the lower inverse coefficient;
all other tags and every unselected column remain identically zero.
-/
theorem inversePower_step (roots inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word)
    (units : ∀ column : Fin word.length, selected (word[column.val]'column.isLt) = true →
      inverses (word[column.val]'column.isLt) * roots (word[column.val]'column.isLt) = 1)
    (steps : Nat) :
    Rectangular.mul (inversePower inverses selected word occurrences (steps + 1))
        (transition roots word occurrences) = inversePower inverses selected word occurrences steps := by
  apply matrix_ext
  intro row column
  rewrite [mul_transition, inversePower_at, inversePower_at]
  by_cases chosen : selected (word[column.val]'column.isLt) = true
  · rewrite [if_pos chosen, if_pos chosen]
    by_cases tags : word[row.val]'row.isLt = word[column.val]'column.isLt
    · rewrite [if_pos tags, if_pos tags]
      cases previous : occurrences.predecessors column with
      | none =>
          have zero := occurrences.none_zero column previous
          change (if occurrences.orders row ≤ occurrences.orders column then _ else 0) * _ + 0 = _
          rewrite [zero]
          by_cases first : occurrences.orders row = 0
          · rewrite [first, if_pos (Nat.le_refl 0), Nat.sub_self, add_zero]
            exact inverseEntry_step_zero _ _ (units column chosen) steps
          · have later : ¬occurrences.orders row ≤ 0 := by omega0
            rewrite [if_neg later, zero_mul, add_zero, if_neg later]
            rfl
      | some prior =>
          have facts := occurrences.some_spec column prior previous
          have chosenPrior : selected (word[prior.val]'prior.isLt) = true :=
            (congrArg selected facts.2.1).trans chosen
          have tagsPrior : word[row.val]'row.isLt = word[prior.val]'prior.isLt := tags.trans facts.2.1.symm
          change (if occurrences.orders row ≤ occurrences.orders column then _ else 0) * _ +
            inversePower inverses selected word occurrences (steps + 1) row prior = _
          rewrite [inversePower_at, if_pos chosenPrior, if_pos tagsPrior, facts.2.1]
          by_cases equal : occurrences.orders row = occurrences.orders column
          · have atColumn : occurrences.orders row ≤ occurrences.orders column := equal.le
            have afterPrior : ¬occurrences.orders row ≤ occurrences.orders prior := by
              have next := facts.2.2
              omega0
            rewrite [if_pos atColumn, if_pos atColumn, if_neg afterPrior, equal, Nat.sub_self, add_zero]
            exact inverseEntry_step_zero _ _ (units column chosen) steps
          · by_cases before : occurrences.orders row < occurrences.orders column
            · have atColumn := Nat.le_of_lt before
              have atPrior : occurrences.orders row ≤ occurrences.orders prior := by
                have next := facts.2.2
                omega0
              have distance : occurrences.orders column - occurrences.orders row =
                  (occurrences.orders prior - occurrences.orders row) + 1 := by
                have next := facts.2.2
                omega0
              rewrite [if_pos atColumn, if_pos atColumn, if_pos atPrior, distance]
              exact inverseEntry_step _ _ (units column chosen) _ steps
            · have afterColumn : ¬occurrences.orders row ≤ occurrences.orders column := by omega0
              have afterPrior : ¬occurrences.orders row ≤ occurrences.orders prior := by
                have next := facts.2.2
                omega0
              rewrite [if_neg afterColumn, if_neg afterColumn, if_neg afterPrior, zero_mul, zero_add]
              rfl
    · rewrite [if_neg tags, if_neg tags, zero_mul]
      cases previous : occurrences.predecessors column with
      | none => exact add_zero 0
      | some prior =>
          have facts := occurrences.some_spec column prior previous
          have chosenPrior : selected (word[prior.val]'prior.isLt) = true :=
            (congrArg selected facts.2.1).trans chosen
          have other : word[row.val]'row.isLt ≠ word[prior.val]'prior.isLt := by
            intro same
            exact tags (same.trans facts.2.1)
          change 0 + inversePower inverses selected word occurrences (steps + 1) row prior = 0
          rewrite [inversePower_at, if_pos chosenPrior, if_neg other, zero_add]
          rfl
  · rewrite [if_neg chosen, if_neg chosen, zero_mul]
    cases previous : occurrences.predecessors column with
    | none => exact add_zero 0
    | some prior =>
        have facts := occurrences.some_spec column prior previous
        have other : selected (word[prior.val]'prior.isLt) ≠ true := by
          intro same
          exact chosen ((congrArg selected facts.2.1).symm.trans same)
        change 0 + inversePower inverses selected word occurrences (steps + 1) row prior = 0
        rewrite [inversePower_at, if_neg other, zero_add]
        rfl

/-- The selected finite inverse power cancels the same original transition power to its actual projector. -/
theorem inversePower_identity (roots inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word)
    (units : ∀ column : Fin word.length, selected (word[column.val]'column.isLt) = true →
      inverses (word[column.val]'column.isLt) * roots (word[column.val]'column.isLt) = 1)
    (steps : Nat) :
    Rectangular.mul (inversePower inverses selected word occurrences steps)
      (Arithmetic.power (transition roots word occurrences) steps) = projection selected word := by
  induction steps with
  | zero => rewrite [Arithmetic.power_zero, Rectangular.mul_unit, inversePower_zero]; rfl
  | succ steps previous =>
      have power : Arithmetic.power (transition roots word occurrences) (steps + 1) =
          Rectangular.mul (transition roots word occurrences)
            (Arithmetic.power (transition roots word occurrences) steps) :=
        (Arithmetic.power_succ _ _).trans (Arithmetic.commute_power _ _ rfl steps).symm
      rewrite [power, ← Rectangular.mul_assoc, inversePower_step roots inverses selected word occurrences units]
      exact previous

/-- The same partial inverse recovers exactly the selected original coefficient coordinates from the shifted vector. -/
theorem inversePower_apply (roots inverses : Tag → K) (selected : Tag → Bool) (word : List Tag)
    (occurrences : Occurrences word)
    (units : ∀ column : Fin word.length, selected (word[column.val]'column.isLt) = true →
      inverses (word[column.val]'column.isLt) * roots (word[column.val]'column.isLt) = 1)
    (steps : Nat) (values : Vec K word.length) :
    Rectangular.apply (inversePower inverses selected word occurrences steps)
      (Rectangular.apply (Arithmetic.power (transition roots word occurrences) steps) values) =
        Rectangular.apply (projection selected word) values := by
  rewrite [← Rectangular.apply_mul, inversePower_identity roots inverses selected word occurrences units]
  rfl

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

omit [CommRing K] in
/-- One original common inverse request bounds every selected partial-inverse entry after its retained threshold.

The actual Gaussian reciprocals belong only to the selected original tags.
The same source-fixed outside floor bounds their root readings, and each
cached predecessor distance is below the original finite word length.
-/
theorem inversePower_bound {floor epsilon : Rational} (word : List Tag)
    (request : InverseRequest floor word.length epsilon)
    (roots inverses : Tag → Canonical) (selected : Tag → Bool)
    (occurrences : Occurrences word)
    (reciprocals : ∀ tag, selected tag = true → inverses tag = Field.inv (roots tag))
    (pointBound : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (roots tag))
    (steps : Nat) (later : request.index ≤ steps) (row column : Fin word.length) :
    Norm.Basic.normSq (inversePower inverses selected word occurrences steps row column) ≤ epsilon := by
  rewrite [inversePower_at]
  by_cases chosen : selected (word[column.val]'column.isLt) = true
  · rewrite [if_pos chosen]
    by_cases tags : word[row.val]'row.isLt = word[column.val]'column.isLt
    · rewrite [if_pos tags]
      by_cases ordered : occurrences.orders row ≤ occurrences.orders column
      · rewrite [if_pos ordered, reciprocals _ chosen]
        have distance : occurrences.orders column - occurrences.orders row < word.length :=
          (Nat.sub_le _ _).trans_lt ((occurrences.order_le column).trans_lt column.isLt)
        exact request.bound (roots (word[column.val]'column.isLt)) (pointBound _ chosen)
          ⟨_, distance⟩ steps later
      · rewrite [if_neg ordered, Norm.Basic.normSq_zero]
        exact request.epsilonPositive.le
    · rewrite [if_neg tags, Norm.Basic.normSq_zero]
      exact request.epsilonPositive.le
  · rewrite [if_neg chosen, Norm.Basic.normSq_zero]
    exact request.epsilonPositive.le

end Purelib.Polynomial.Recurrence.Mode.Hermite.Shift

end
