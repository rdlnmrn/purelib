module
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Range.Basic
import Purelib.Data.Nat.GCD.Extended

import Purelib.Data.Bool.Decide
import Purelib.Data.List.Range.Nodup
import Purelib.Data.Nat.Decide
public import Purelib.Data.Nat.FiniteSum
public import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Order
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic

/-!
# Totient counts over finite natural residue prefixes

Scalar Euclidean computation tests the gcd of each retained residue. Filtered
range lengths count the coprime labels and individual gcd fibres; explicit
multiplication witnesses identify quotient-totient counts with those fibres.
-/

public section

namespace Purelib.NumberTheory.Totient.Basic

open Purelib
open Purelib.Data.List
open Purelib.Data.Nat

/-- Executable gcd equality for the bounded filters below. -/
@[expose] def gcdEquals (number divisor residue : Nat) : Bool :=
  decide (GCD.Scalar.gcd number residue = divisor)

/-- The gcd equality test agrees with the retained extended-Euclidean gcd.

Each Boolean certificate retains the scalar Euclidean computation. Its original
projection equation transports the displayed equality in either direction. -/
theorem gcdEquals_eq_true
    (number divisor residue : Nat) :
    gcdEquals number divisor residue = true ↔
      (GCD.Extended.compute number residue).gcd = divisor := by
  constructor
  · intro accepted
    have scalarEquality : GCD.Scalar.gcd number residue = divisor :=
      of_decide_eq_true accepted
    exact (GCD.Scalar.gcd_eq_compute number residue).symm.trans scalarEquality
  · intro retained
    change decide (GCD.Scalar.gcd number residue = divisor) = true
    exact decide_eq_true ((GCD.Scalar.gcd_eq_compute number residue).trans retained)

/-- Euler's totient as the literal finite list of coprime labels
`0, ..., modulus-1`. -/
@[expose] def totient (modulus : Nat) : Nat :=
  ((List.range modulus).filter fun residue =>
    gcdEquals modulus 1 residue).length

/-- The finite coprime-label count at modulus zero is zero. -/
@[simp] theorem totient_zero : totient 0 = 0 := rfl

/-- The finite coprime-label count at modulus one is one. -/
@[simp] theorem totient_one : totient 1 = 1 := rfl

/-- The explicitly filtered gcd fibre. -/
@[expose] def gcdFiberCount (number divisor : Nat) : Nat :=
  ((List.range number).filter fun residue =>
    gcdEquals number divisor residue).length

/-- A displayed divisor transports coprime labels to its gcd fibre.

Multiplication by the retained positive divisor maps coprime labels below the
original quotient bijectively to labels with that computed gcd. Duplicate-free
containment in both directions certifies equality of the finite counts. -/
theorem totient_div_of_dvd {number divisor : Nat}
    (divides : divisor ∣ number) :
    totient (number / divisor) =
      gcdFiberCount number divisor := by
  rcases divisor.eq_zero_or_pos with divisorZero | divisorPositive
  · subst divisor
    have numberZero : number = 0 := Nat.eq_zero_of_zero_dvd divides
    subst number
    rfl
  · rcases divides with ⟨quotient, rfl⟩
    rw [Division.mul_div_cancel_left quotient divisorPositive]
    unfold totient gcdFiberCount
    let source := (List.range quotient).filter fun residue =>
      gcdEquals quotient 1 residue
    let target := (List.range (divisor * quotient)).filter fun residue =>
      gcdEquals (divisor * quotient) divisor residue
    have multiplyInjective : Function.Injective (fun value : Nat =>
        divisor * value) := by
      intro left right equality
      exact Nat.eq_of_mul_eq_mul_left divisorPositive equality
    have sourceRangeNodup : (List.range quotient).Nodup :=
      Range.Nodup.range_nodup quotient
    have targetRangeNodup :
        (List.range (divisor * quotient)).Nodup :=
      Range.Nodup.range_nodup (divisor * quotient)
    have sourceNodup : source.Nodup := Filter.pairwise_filter _ sourceRangeNodup
    have targetNodup : target.Nodup := Filter.pairwise_filter _ targetRangeNodup
    have members (residue : Nat) :
        residue ∈ source.map (fun label => divisor * label) ↔ residue ∈ target := by
      unfold source target
      constructor
      · intro mappedMember
        rcases Map.mem_map.mp mappedMember with
          ⟨label, filteredMember, labelEquality⟩
        rcases Filter.mem_filter.mp filteredMember with
          ⟨labelRangeMember, coprimeTest⟩
        have labelBelow :=
          Range.Basic.mem_range.mp labelRangeMember
        have coprime :=
          (gcdEquals_eq_true quotient 1 label).mp coprimeTest
        subst residue
        apply Filter.mem_filter.mpr
        constructor
        · apply Range.Basic.mem_range.mpr
          exact Nat.mul_lt_mul_of_pos_left labelBelow divisorPositive
        · apply (gcdEquals_eq_true
            (divisor * quotient) divisor (divisor * label)).mpr
          rw [GCD.Extended.compute_gcd_mul_left, coprime, Nat.mul_one]
      · intro filteredMember
        rcases Filter.mem_filter.mp filteredMember with
          ⟨residueRangeMember, gcdTest⟩
        have residueBelow :=
          Range.Basic.mem_range.mp residueRangeMember
        have gcdEquation := (gcdEquals_eq_true
          (divisor * quotient) divisor residue).mp gcdTest
        have divisorDividesResidue : divisor ∣ residue := by
          rw [← gcdEquation]
          exact (GCD.Extended.compute_spec _ _).2.2
        rcases divisorDividesResidue with ⟨label, rfl⟩
        apply Map.mem_map.mpr
        refine ⟨label, ?_, rfl⟩
        apply Filter.mem_filter.mpr
        constructor
        · apply Range.Basic.mem_range.mpr
          exact Order.lt_of_mul_lt_mul_left residueBelow
        · apply (gcdEquals_eq_true quotient 1 label).mpr
          have scaledEquation :
              divisor * (GCD.Extended.compute quotient label).gcd =
                divisor * 1 := by
            calc
              _ = (GCD.Extended.compute
                  (divisor * quotient) (divisor * label)).gcd :=
                (GCD.Extended.compute_gcd_mul_left divisor quotient label).symm
              _ = divisor := gcdEquation
              _ = divisor * 1 := (Nat.mul_one divisor).symm
          exact Nat.eq_of_mul_eq_mul_left divisorPositive scaledEquation
    have mappedNodup : (source.map (fun label => divisor * label)).Nodup :=
      Data.List.Nodup.nodup_map_of_injective multiplyInjective sourceNodup
    have forwardBound := Nodup.nodup_length_le_of_mem mappedNodup targetNodup
      (fun residue member => (members residue).mp member)
    have reverseBound := Nodup.nodup_length_le_of_mem targetNodup mappedNodup
      (fun residue member => (members residue).mpr member)
    have lengths := Nat.le_antisymm forwardBound reverseBound
    rewrite [Map.length_map] at lengths
    exact lengths

/-- Scan all possible divisor labels in quotient coordinates. -/
@[expose] def divisorQuotientTotientSum (number : Nat) : Nat :=
  FiniteSum.natSum (number + 1) fun divisor =>
    if Decide.divisibilityTest divisor number then
      totient (number / divisor) else 0

/-- A nondivisor cannot label a computed gcd fibre.

Every displayed member of the filtered fibre retains its gcd equality. The
original Euclidean specification would then make that same label a divisor,
contradicting the supplied nondivisibility certificate. -/
theorem gcdFiberCount_eq_zero_of_not_dvd
    {number divisor : Nat} (notDivides : ¬ divisor ∣ number) :
    gcdFiberCount number divisor = 0 := by
  unfold gcdFiberCount
  cases filteredEquation : (List.range number).filter
      (fun residue => gcdEquals number divisor residue) with
  | nil => rfl
  | cons residue remaining =>
      have member : residue ∈ (List.range number).filter
          (fun candidate => gcdEquals number divisor candidate) := by
        rw [filteredEquation]
        exact List.mem_cons_self
      have gcdEquation := (gcdEquals_eq_true
        number divisor residue).1 (Filter.mem_filter.mp member).2
      have contradiction : False := by
        apply notDivides
        rw [← gcdEquation]
        exact (GCD.Extended.compute_spec _ _).2.1
      exact contradiction.elim

/-- A gcd-fibre count is its bounded equality-indicator sum. -/
theorem gcdFiberCount_eq_indicator_sum (number divisor : Nat) :
    gcdFiberCount number divisor =
      FiniteSum.natSum number (fun residue =>
        if gcdEquals number divisor residue then 1 else 0) := by
  exact (FiniteSum.natSum_indicator_eq_filter_length number
    (gcdEquals number divisor)).symm

/-- The finite gcd fibres partition the displayed residue prefix.

Each residue retains its computed gcd as exactly one fibre label. Interchanging
the two bounded natural sums therefore makes the quotient-totient counts add
to the original prefix length. -/
theorem divisorQuotientTotientSum_eq (number : Nat) :
    divisorQuotientTotientSum number = number := by
  have divisorTerm (divisor : Nat) (divisorBelow : divisor < number + 1) :
      (if Decide.divisibilityTest divisor number then
          totient (number / divisor) else 0) =
        gcdFiberCount number divisor := by
    cases accepted : Decide.divisibilityTest divisor number with
    | false =>
        have notDivides : ¬ divisor ∣ number := by
          intro divides
          have truth := (Decide.divisibilityTest_eq_true divisor number).mpr divides
          exact Bool.noConfusion (accepted.symm.trans truth)
        change 0 = gcdFiberCount number divisor
        exact (gcdFiberCount_eq_zero_of_not_dvd notDivides).symm
    | true =>
        have divides := (Decide.divisibilityTest_eq_true divisor number).mp accepted
        change totient (number / divisor) =
          gcdFiberCount number divisor
        exact totient_div_of_dvd divides
  have oneFiber (residue : Nat) (residueBelow : residue < number) :
      FiniteSum.natSum (number + 1) (fun divisor =>
          if gcdEquals number divisor residue then 1 else 0) = 1 := by
    let common := (GCD.Extended.compute number residue).gcd
    have commonBelow : common < number + 1 := by
      unfold common
      exact Nat.lt_succ_of_le (Divisibility.le_of_dvd
        (Nat.lt_of_le_of_lt (Nat.zero_le residue) residueBelow)
        (GCD.Extended.compute_spec number residue).2.1)
    calc
      FiniteSum.natSum (number + 1) (fun divisor =>
          if gcdEquals number divisor residue then 1 else 0) =
        FiniteSum.natSum (number + 1) (fun divisor =>
          if Decide.natEquals divisor common then 1 else 0) := by
            apply FiniteSum.natSum_congr
            intro divisor divisorBelow
            by_cases equality :
                (GCD.Extended.compute number residue).gcd = divisor
            · have reverse :
                  divisor = (GCD.Extended.compute number residue).gcd :=
                equality.symm
              rw [show gcdEquals number divisor residue = true by
                    exact (gcdEquals_eq_true
                      number divisor residue).2 equality,
                show Decide.natEquals divisor common = true by
                    exact (Decide.natEquals_eq_true divisor common).2 reverse]
            · have reverse :
                  divisor ≠ (GCD.Extended.compute number residue).gcd := by
                intro reversed
                exact equality reversed.symm
              rw [show gcdEquals number divisor residue = false by
                    exact Data.Bool.Decide.bool_eq_false_of_not_eq_true _ (fun truth =>
                      equality ((gcdEquals_eq_true
                        number divisor residue).1 truth)),
                show Decide.natEquals divisor common = false by
                    exact Data.Bool.Decide.bool_eq_false_of_not_eq_true _ (fun truth =>
                      reverse ((Decide.natEquals_eq_true
                        divisor common).1 truth))]
      _ = if Decide.natLess common (number + 1) then 1 else 0 :=
        FiniteSum.natSum_natEquals (number + 1) common
      _ = 1 := by
        rw [show Decide.natLess common (number + 1) = true by
          exact (Decide.natLess_eq_true common (number + 1)).2 commonBelow,
          if_pos rfl]
  unfold divisorQuotientTotientSum
  calc
    FiniteSum.natSum (number + 1) (fun divisor =>
        if Decide.divisibilityTest divisor number then
          totient (number / divisor) else 0) =
      FiniteSum.natSum (number + 1) (gcdFiberCount number) := by
        apply FiniteSum.natSum_congr
        exact divisorTerm
    _ = FiniteSum.natSum (number + 1) (fun divisor =>
        FiniteSum.natSum number (fun residue =>
          if gcdEquals number divisor residue then 1 else 0)) := by
            apply FiniteSum.natSum_congr
            intro divisor divisorBelow
            exact gcdFiberCount_eq_indicator_sum number divisor
    _ = FiniteSum.natSum number (fun residue =>
        FiniteSum.natSum (number + 1) (fun divisor =>
          if gcdEquals number divisor residue then 1 else 0)) :=
            FiniteSum.natSum_swap (number + 1) number _
    _ = FiniteSum.natSum number (fun _ : Nat => 1) := by
      apply FiniteSum.natSum_congr
      exact oneFiber
    _ = number := FiniteSum.natSum_one number

end Purelib.NumberTheory.Totient.Basic
