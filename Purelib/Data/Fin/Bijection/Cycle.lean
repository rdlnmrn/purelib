module
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Fin.Bijection.Search
import Mathlib.Tactic.Linter.Lint
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin.Bijection

section
public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.Data.Fin.Bijection

open Purelib.Data
section Bijection

/-- Without an early return, the first count iterates reach every finite target.

For any displayed start, two equal iterates would produce a positive return before
count steps. Their distinctness makes the finite orbit enumeration injective and
hence surjective. -/
theorem iterateForward_surjective_of_noEarlyReturn
    {count : Nat} (bijection : Bijection count count)
    (noEarlyReturn : ∀ (index : Fin count) (steps : Nat),
      0 < steps → steps < count →
        Bijection.iterateForward bijection steps index ≠ index)
    (start target : Fin count) :
    ∃ steps : Fin count,
      Bijection.iterateForward bijection steps.val start = target := by
  let orbit : Fin count → Fin count := fun steps =>
    Bijection.iterateForward bijection steps.val start
  have orbitInjective : Function.Injective orbit := by
    intro left right equal
    change Bijection.iterateForward bijection left.val start =
      Bijection.iterateForward bijection right.val start at equal
    by_cases valuesEqual : left.val = right.val
    · exact Fin.ext valuesEqual
    · by_cases leftBefore : left.val < right.val
      · let difference := right.val - left.val
        have differencePositive : 0 < difference :=
          Nat.Subtraction.sub_pos_of_lt leftBefore
        have differenceSmall : difference < count :=
          (Nat.sub_le right.val left.val).trans_lt right.isLt
        have split : left.val + difference = right.val :=
          Nat.Subtraction.add_sub_of_le leftBefore.le
        have returned :
            Bijection.iterateForward bijection difference
                (Bijection.iterateForward bijection left.val start) =
              Bijection.iterateForward bijection left.val start := by
          calc
            Bijection.iterateForward bijection difference
                (Bijection.iterateForward bijection left.val start) =
              Bijection.iterateForward bijection (left.val + difference) start :=
                (Bijection.iterateForward_add bijection left.val difference start).symm
            _ = Bijection.iterateForward bijection right.val start := by rw [split]
            _ = Bijection.iterateForward bijection left.val start := equal.symm
        exact (noEarlyReturn (orbit left) difference differencePositive
          differenceSmall (by simpa only [-eq_self, -iff_self, orbit] using returned)).elim
      · have rightBefore : right.val < left.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt leftBefore)
            (Ne.symm valuesEqual)
        let difference := left.val - right.val
        have differencePositive : 0 < difference :=
          Nat.Subtraction.sub_pos_of_lt rightBefore
        have differenceSmall : difference < count :=
          (Nat.sub_le left.val right.val).trans_lt left.isLt
        have split : right.val + difference = left.val :=
          Nat.Subtraction.add_sub_of_le rightBefore.le
        have returned :
            Bijection.iterateForward bijection difference
                (Bijection.iterateForward bijection right.val start) =
              Bijection.iterateForward bijection right.val start := by
          calc
            Bijection.iterateForward bijection difference
                (Bijection.iterateForward bijection right.val start) =
              Bijection.iterateForward bijection (right.val + difference) start :=
                (Bijection.iterateForward_add bijection right.val difference start).symm
            _ = Bijection.iterateForward bijection left.val start := by rw [split]
            _ = Bijection.iterateForward bijection right.val start := equal
        exact (noEarlyReturn (orbit right) difference differencePositive
          differenceSmall (by simpa only [-eq_self, -iff_self, orbit] using returned)).elim
  simpa only [-eq_self, -iff_self, orbit] using
    Bijection.fin_surjective_of_injective orbit orbitInjective target

/-- Certify exact count-step periods at every index of a finite bijection.

Every index returns after count forward steps, and no index returns after a strictly
positive smaller number of steps. The condition remains meaningful for the empty
finite type. -/
structure IsSingleCycle {count : Nat}
    (bijection : Bijection count count) : Prop where
  /-- Every index returns after exactly count forward steps. -/ return_at_count : ∀ index : Fin count,
    Bijection.iterateForward bijection count index = index
  /-- No index returns after a strictly positive number of steps below count. -/ no_early_return : ∀ (index : Fin count)
    (steps : Nat),
    0 < steps → steps < count →
      Bijection.iterateForward bijection steps index ≠ index

/-- Excluding every shorter positive return forces a finite bijection to be a single
cycle.

The first count iterates reach the starting index's predecessor. Its next step
returns, and the exclusion of earlier returns identifies this return time with count. -/
theorem isSingleCycle_of_noEarlyReturn
    {count : Nat} (bijection : Bijection count count)
    (noEarlyReturn : ∀ (index : Fin count) (steps : Nat),
      0 < steps → steps < count →
        Bijection.iterateForward bijection steps index ≠ index) :
    IsSingleCycle bijection where
  no_early_return := noEarlyReturn
  return_at_count := by
    intro index
    let predecessor := bijection.backward index
    obtain ⟨steps, reaches⟩ :=
      Bijection.iterateForward_surjective_of_noEarlyReturn bijection noEarlyReturn
        index predecessor
    have returns : Bijection.iterateForward bijection (steps.val + 1) index = index := by
      rw [Bijection.iterateForward_succ, reaches, bijection.forward_backward]
    have notLess : ¬steps.val + 1 < count := by
      intro small
      exact noEarlyReturn index (steps.val + 1) (Nat.zero_lt_succ _)
        small returns
    have equalCount : steps.val + 1 = count :=
      Nat.le_antisymm (Nat.succ_le_of_lt steps.isLt)
        (Nat.le_of_not_gt notLess)
    simpa only [-eq_self, -iff_self, equalCount] using returns

namespace IsSingleCycle

/-- A certified single cycle reaches any target within the first count iterates from any
start. -/
theorem reaches
    {count : Nat} {bijection : Bijection count count}
    (cycle : IsSingleCycle bijection) (start target : Fin count) :
    ∃ steps : Fin count,
      Bijection.iterateForward bijection steps.val start = target :=
  Bijection.iterateForward_surjective_of_noEarlyReturn bijection
    cycle.no_early_return start target

end IsSingleCycle
end Bijection

end Purelib.Data.Fin.Bijection

end

section
public section

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`Bijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace Purelib.Data.Fin.Bijection.Cycle

open Purelib.Data

section Bijection

namespace IsSingleCycle

/-- The inverse of a certified finite single cycle is again a single cycle.

Equal forward and backward iterate lengths cancel. This transports both the
full-period return and the exclusion of shorter positive returns. -/
theorem reverse {count : Nat}
    {bijection : Bijection count count}
    (cycle : IsSingleCycle bijection) :
    IsSingleCycle bijection.reverse := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro index
    apply (Bijection.iterateForward_injective
      bijection count)
    rw [Iteration.iterate_reverse_cancel, cycle.return_at_count]
  · intro index steps positive small returned
    apply cycle.no_early_return index steps positive small
    have applied := congrArg
      (Bijection.iterateForward
        bijection steps) returned
    rw [Iteration.iterate_reverse_cancel] at applied
    exact applied.symm

end IsSingleCycle
/-- The first count iterates from a fixed base are pairwise distinct in a single cycle.

Equality at different bounded iteration counts would give a strictly positive return
shorter than count, contradicting the retained no-early-return certificate. -/
theorem orbit_injective {count : Nat}
    {bijection : Bijection count count}
    (cycle : IsSingleCycle bijection)
    (base : Fin count) : Function.Injective
      (fun steps : Fin count =>
        Bijection.iterateForward
          bijection steps.val base) := by
  intro left right equal
  by_cases valuesEqual : left.val = right.val
  · exact Fin.ext valuesEqual
  · by_cases leftBefore : left.val < right.val
    · let difference := right.val - left.val
      have differencePositive : 0 < difference := Nat.Subtraction.sub_pos_of_lt leftBefore
      have differenceSmall : difference < count :=
        (Nat.sub_le right.val left.val).trans_lt right.isLt
      have split : left.val + difference = right.val :=
        Nat.Subtraction.add_sub_of_le leftBefore.le
      have returned :
          Bijection.iterateForward
              bijection difference
              (Bijection.iterateForward
                bijection left.val base) =
            Bijection.iterateForward
              bijection left.val base := by
        calc
          _ = Bijection.iterateForward
                bijection (left.val + difference) base :=
            (Bijection.iterateForward_add
              bijection left.val difference base).symm
          _ = Bijection.iterateForward
                bijection right.val base := by rw [split]
          _ = Bijection.iterateForward
                bijection left.val base := equal.symm
      exact (cycle.no_early_return _ difference differencePositive
        differenceSmall returned).elim
    · have rightBefore : right.val < left.val :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt leftBefore)
          (Ne.symm valuesEqual)
      let difference := left.val - right.val
      have differencePositive : 0 < difference :=
        Nat.Subtraction.sub_pos_of_lt rightBefore
      have differenceSmall : difference < count :=
        (Nat.sub_le left.val right.val).trans_lt left.isLt
      have split : right.val + difference = left.val :=
        Nat.Subtraction.add_sub_of_le rightBefore.le
      have returned :
          Bijection.iterateForward
              bijection difference
              (Bijection.iterateForward
                bijection right.val base) =
            Bijection.iterateForward
              bijection right.val base := by
        calc
          _ = Bijection.iterateForward
                bijection (right.val + difference) base :=
            (Bijection.iterateForward_add
              bijection right.val difference base).symm
          _ = Bijection.iterateForward
                bijection left.val base := by rw [split]
          _ = Bijection.iterateForward
                bijection right.val base := equal
      exact (cycle.no_early_return _ difference differencePositive
        differenceSmall returned).elim
end Bijection

end Purelib.Data.Fin.Bijection.Cycle

end
