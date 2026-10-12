module

import Purelib.Data.Bool.Decide
import Purelib.Data.List.Append
import Purelib.Data.List.Filter
import Purelib.Data.List.Range.Basic
public import Purelib.Data.Nat.Decide
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Data.Nat

open Purelib.Data.List

section
section
public section

/-!
# Natural sums over explicit finite prefixes

Natural recursion sums a displayed prefix or a `Fin`-indexed family.
Pointwise transport, rectangular interchange, indicator counting and prefix
splitting retain the original requested counts and indices.
-/

namespace Purelib.Data.Nat.FiniteSum

/-- Sum a displayed prefix of a natural-valued function.

The count bounds the indices from zero through count - 1. Each successor step adds
the final requested term to the preceding prefix sum. -/
@[expose] def natSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count + 1, term => Data.Nat.FiniteSum.natSum count term + term count

/-- The natural sum over an empty prefix is zero. -/
@[simp] theorem natSum_zero (term : Nat → Nat) :
    FiniteSum.natSum 0 term = 0 := rfl

/-- A successor prefix sum adds the final term to the preceding prefix sum. -/
@[simp] theorem natSum_succ_last (count : Nat) (term : Nat → Nat) :
    FiniteSum.natSum (count + 1) term = FiniteSum.natSum count term + term count := rfl

/-- Pointwise equality on the requested prefix preserves a natural sum.

Only indices strictly below count require an equality witness; no equality of the
whole functions is assumed. -/
theorem natSum_congr
    (count : Nat) (first second : Nat → Nat)
    (equal : ∀ index, index < count → first index = second index) :
    FiniteSum.natSum count first = FiniteSum.natSum count second := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, FiniteSum.natSum_succ_last,
        inductionHypothesis (fun index indexBelow =>
          equal index (by omega0)), equal count (by omega0)]

/-- A bounded natural sum distributes over pointwise addition. -/
theorem natSum_add
    (count : Nat) (first second : Nat → Nat) :
    FiniteSum.natSum count (fun index => first index + second index) =
      FiniteSum.natSum count first + FiniteSum.natSum count second := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, FiniteSum.natSum_succ_last,
        FiniteSum.natSum_succ_last, inductionHypothesis]
      omega0

/-- Interchange two explicitly bounded natural sums.

For a natural-valued function of two indices and two supplied counts, summing over
either index first gives the same rectangular total. -/
theorem natSum_swap
    (firstCount secondCount : Nat) (term : Nat → Nat → Nat) :
    FiniteSum.natSum firstCount (fun first =>
        FiniteSum.natSum secondCount (fun second => term first second)) =
      FiniteSum.natSum secondCount (fun second =>
        FiniteSum.natSum firstCount (fun first => term first second)) := by
  induction firstCount with
  | zero =>
      rw [FiniteSum.natSum_zero]
      have zeros : FiniteSum.natSum secondCount (fun _ : Nat => 0) = 0 := by
        induction secondCount with
        | zero => rfl
        | succ secondCount inductionHypothesis =>
            rw [FiniteSum.natSum_succ_last, inductionHypothesis]
      exact zeros.symm
  | succ firstCount inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, inductionHypothesis]
      have expanded :
          FiniteSum.natSum secondCount (fun second =>
              FiniteSum.natSum (firstCount + 1) (fun first =>
                term first second)) =
            FiniteSum.natSum secondCount (fun second =>
              FiniteSum.natSum firstCount (fun first => term first second) +
                term firstCount second) := by
        apply FiniteSum.natSum_congr
        intro second secondBelow
        rw [FiniteSum.natSum_succ_last]
      rw [expanded, FiniteSum.natSum_add]

/-- The natural sum of a constant one over a prefix equals its length. -/
theorem natSum_one (count : Nat) :
    FiniteSum.natSum count (fun _ : Nat => 1) = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, inductionHypothesis]

/-- Sum an equality indicator over a bounded natural prefix.

The sum is one exactly when the target lies below the supplied count, and zero
otherwise; the statement uses the executable natural equality and order tests. -/
theorem natSum_natEquals (count target : Nat) :
    FiniteSum.natSum count (fun index =>
        if Decide.natEquals index target then 1 else 0) =
      if Decide.natLess target count then 1 else 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, inductionHypothesis]
      by_cases targetBelow : target < count
      · have countNotTarget : count ≠ target := fun equal =>
          Nat.lt_irrefl target (equal ▸ targetBelow)
        rw [show Decide.natLess target count = true by
            exact (Decide.natLess_eq_true target count).2 targetBelow,
          show Decide.natLess target (count + 1) = true by
            exact (Decide.natLess_eq_true target (count + 1)).2 (by omega0),
          show Decide.natEquals count target = false by
            exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equality =>
              countNotTarget ((Decide.natEquals_eq_true count target).1 equality))]
        rfl
      · by_cases targetEquals : target = count
        · subst target
          rw [show Decide.natLess count count = false by
              exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                (Nat.lt_irrefl count)
                  ((Decide.natLess_eq_true count count).1 below)),
            show Decide.natLess count (count + 1) = true by
              exact (Decide.natLess_eq_true count (count + 1)).2 (by omega0),
            show Decide.natEquals count count = true by
              exact (Decide.natEquals_eq_true count count).2 rfl]
          rfl
        · have targetAbove : count < target := by omega0
          rw [show Decide.natLess target count = false by
              exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                targetBelow ((Decide.natLess_eq_true target count).1 below)),
            show Decide.natLess target (count + 1) = false by
              exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                (by
                  have := (Decide.natLess_eq_true target (count + 1)).1 below
                  omega0)),
            show Decide.natEquals count target = false by
              exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equality =>
                targetEquals
                  ((Decide.natEquals_eq_true count target).1 equality).symm)]
          rfl

/-- An indicator sum equals the length of the corresponding filtered natural range.

For a Boolean predicate, each accepted index contributes one and each rejected index
contributes zero, matching the finite filter of List.range count. -/
theorem natSum_indicator_eq_filter_length
    (count : Nat) (predicate : Nat → Bool) :
    FiniteSum.natSum count (fun index => if predicate index then 1 else 0) =
      ((List.range count).filter predicate).length := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rewrite [FiniteSum.natSum_succ_last, Range.Basic.range_succ,
        Filter.filter_append, Append.length_append, inductionHypothesis]
      have lastLength : ([count].filter predicate).length =
          if predicate count then 1 else 0 := by
        change (match predicate count with
          | true => [count]
          | false => []).length = if predicate count then 1 else 0
        cases predicate count <;> exact Eq.refl _
      exact congrArg (fun length => ((List.range count).filter predicate).length + length)
        lastLength.symm
end Purelib.Data.Nat.FiniteSum

end

end

section
@[expose] public section

/-!
## Natural sums over finite index types

The finite-index recursion retains the original successor prefix and final
index. Its certificates compare that sum with a natural prefix, transport
pointwise equalities and split an original prefix into two displayed parts.
-/

namespace Purelib.Data.Nat.FiniteSum

/-- Sum a natural-valued family over its exact finite index type.

At a successor size, recurse on the prefix through castSucc and add the value at the
last index. The empty family has sum zero. -/
def sumFinNat : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, term =>
      Data.Nat.FiniteSum.sumFinNat count (fun index => term index.castSucc) + term (Fin.last count)

/-- Pointwise equality of two finite indexed families preserves their natural sum.

Equality is supplied separately at each retained Fin index, avoiding an equality
premise between the family functions. -/
theorem sumFinNat_congr : ∀ (count : Nat) (left right : Fin count → Nat),
    (∀ index, left index = right index) →
      FiniteSum.sumFinNat count left = FiniteSum.sumFinNat count right
  | 0, left, right, pointwise => rfl
  | count + 1, left, right, pointwise => by
      rw [FiniteSum.sumFinNat, FiniteSum.sumFinNat,
        Data.Nat.FiniteSum.sumFinNat_congr count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc)
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]

/-- Finite-index summation agrees with bounded natural summation on index values.

When a Fin-indexed term reads only the natural value of its index, both recursions
visit the same displayed prefix in the same order. -/
theorem sumFinNat_eq_natSum (count : Nat) (term : Nat → Nat) :
    FiniteSum.sumFinNat count (fun index => term index.val) =
      FiniteSum.natSum count term := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.sumFinNat, FiniteSum.natSum_succ_last]
      change FiniteSum.sumFinNat count (fun index => term index.val) + term count = _
      rw [inductionHypothesis]

/-- Sum a weighted equality indicator over a bounded natural prefix.

The result is the supplied weight exactly when the target occurs below count, and
zero otherwise. -/
theorem natSum_singletonWeight (count target weight : Nat) :
    FiniteSum.natSum count (fun index =>
        if Decide.natEquals index target then weight else 0) =
      if Decide.natLess target count then weight else 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, inductionHypothesis]
      by_cases targetBelow : target < count
      · have countDifferent : count ≠ target := fun equal =>
          Nat.lt_irrefl target (equal ▸ targetBelow)
        rewrite [show Decide.natLess target count = true by
              exact (Decide.natLess_eq_true target count).2 targetBelow,
          show Decide.natLess target (count + 1) = true by
              exact (Decide.natLess_eq_true target (count + 1)).2 (by omega0),
          show Decide.natEquals count target = false by
              exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
                countDifferent
                  ((Decide.natEquals_eq_true count target).1 equal))]
        change weight + 0 = weight
        exact Nat.add_zero weight
      · by_cases targetEqual : target = count
        · subst target
          rewrite [show Decide.natLess count count = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                  (Nat.lt_irrefl count)
                    ((Decide.natLess_eq_true count count).1 below)),
            show Decide.natLess count (count + 1) = true by
                exact (Decide.natLess_eq_true count (count + 1)).2 (by omega0),
            show Decide.natEquals count count = true by
                exact (Decide.natEquals_eq_true count count).2 rfl]
          change 0 + weight = weight
          exact Nat.zero_add weight
        · have targetAbove : count < target := by omega0
          rewrite [show Decide.natLess target count = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                  targetBelow
                    ((Decide.natLess_eq_true target count).1 below)),
            show Decide.natLess target (count + 1) = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun below =>
                  (by
                    have := (Decide.natLess_eq_true
                      target (count + 1)).1 below
                    omega0)),
            show Decide.natEquals count target = false by
                exact Bool.Decide.bool_eq_false_of_not_eq_true _ (fun equal =>
                  targetEqual
                    ((Decide.natEquals_eq_true count target).1 equal).symm)]
          change 0 + 0 = 0
          exact Eq.refl (0 : Nat)

/-- Split a natural prefix sum into a Fin-indexed part and another prefix sum.

At every retained Fin count index, the supplied equality splits the whole term into
the finite part and the extra natural term. Summing those equalities gives the two
corresponding totals. -/
theorem natSum_eq_sumFinNat_add (count : Nat)
    (whole extra : Nat → Nat) (part : Fin count → Nat)
    (split : ∀ index : Fin count,
      whole index.val = part index + extra index.val) :
    FiniteSum.natSum count whole =
      FiniteSum.sumFinNat count part + FiniteSum.natSum count extra := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.natSum_succ_last, FiniteSum.natSum_succ_last,
        FiniteSum.sumFinNat]
      rw [inductionHypothesis (fun index => part index.castSucc)
        (fun index => split index.castSucc)]
      have finalSplit := split (Fin.last count)
      change whole count = part (Fin.last count) + extra count at finalSplit
      rewrite [finalSplit,
        Nat.add_assoc
          (FiniteSum.sumFinNat count (fun index => part index.castSucc))
          (FiniteSum.natSum count extra) (part (Fin.last count) + extra count),
        Nat.add_left_comm (FiniteSum.natSum count extra)
          (part (Fin.last count)) (extra count)]
      exact (Nat.add_assoc
        (FiniteSum.sumFinNat count (fun index => part index.castSucc))
        (part (Fin.last count)) (FiniteSum.natSum count extra + extra count)).symm
end Purelib.Data.Nat.FiniteSum

end
