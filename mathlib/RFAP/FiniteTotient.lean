import mathlib.Tactic.QuotientFreeOmega
import mathlib.Data.ConstructiveList
import mathlib.RFAP.CanonicalGCD
import Mathlib.Data.List.Perm.Basic

/-!
# A bounded constructive Euler totient

The source's Exercise 8.13 needs only the finite count of residue labels below
one displayed modulus.  This module uses ordinary lists and primitive natural
recursion; it is independent of `Finset`, `ZMod`, finite-carrier cardinality,
primitive roots, and Mathlib's noncomputable cyclotomic development.
-/

namespace RFAP

/-- Executable gcd equality for the bounded filters below. -/
def finiteGcdEquals (number divisor residue : Nat) : Bool :=
  decide ((CanonicalGCD.compute number residue).gcd = divisor)

@[simp] theorem finiteGcdEquals_eq_true
    (number divisor residue : Nat) :
    finiteGcdEquals number divisor residue = true ↔
      (CanonicalGCD.compute number residue).gcd = divisor := by
  simp only [finiteGcdEquals, decide_eq_true_eq]

/-- Executable equality of two natural labels. -/
def finiteNatEquals (left right : Nat) : Bool := decide (left = right)

@[simp] theorem finiteNatEquals_eq_true (left right : Nat) :
    finiteNatEquals left right = true ↔ left = right := by
  simp only [finiteNatEquals, decide_eq_true_eq]

/-- Executable strict comparison of natural labels. -/
def finiteNatLess (left right : Nat) : Bool := decide (left < right)

@[simp] theorem finiteNatLess_eq_true (left right : Nat) :
    finiteNatLess left right = true ↔ left < right := by
  simp only [finiteNatLess, decide_eq_true_eq]

/-- Executable divisibility for bounded divisor scans. -/
def finiteDivides (divisor number : Nat) : Bool :=
  decide (divisor ∣ number)

@[simp] theorem finiteDivides_eq_true (divisor number : Nat) :
    finiteDivides divisor number = true ↔ divisor ∣ number := by
  simp only [finiteDivides, decide_eq_true_eq]

/-- Constructive Boolean complement used when a bounded test is known not to
hold. -/
theorem finiteBool_eq_false_of_not_eq_true
    (value : Bool) (notTrue : value ≠ true) : value = false := by
  cases value with
  | false => rfl
  | true => exact (notTrue rfl).elim

/-- The literal prefix list has no duplicate labels.  This direct induction
avoids the upstream simplifier-generated `List.nodup_range` certificate,
whose proof closure contains classical choice. -/
theorem finiteRange_nodup (count : Nat) : (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count inductionHypothesis =>
      rw [List.range_succ]
      apply QuotientFreeList.nodup_append inductionHypothesis
        (QuotientFreeList.nodup_singleton count)
      intro left leftMember right rightMember equality
      have leftBelow : left < count := QuotientFreeList.mem_range.mp leftMember
      have rightEquals : right = count := List.mem_singleton.mp rightMember
      omega0

/-- Cancel a common natural factor from a strict inequality without using the
choice-bearing upstream biconditional. -/
theorem finite_lt_of_mul_lt_mul_left {factor left right : Nat}
    (strict : factor * left < factor * right) : left < right := by
  by_cases ordered : left < right
  · exact ordered
  · have reverse : right ≤ left := Nat.le_of_not_gt ordered
    have scaledReverse : factor * right ≤ factor * left :=
      Nat.mul_le_mul_left factor reverse
    exact False.elim ((Nat.not_le_of_gt strict) scaledReverse)

/-- Sum the first `count` natural-valued terms, appending the final requested
index at each primitive-recursive step. -/
def finiteNatSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | count + 1, term => finiteNatSum count term + term count

@[simp] theorem finiteNatSum_zero (term : Nat → Nat) :
    finiteNatSum 0 term = 0 := rfl

@[simp] theorem finiteNatSum_succ_last (count : Nat) (term : Nat → Nat) :
    finiteNatSum (count + 1) term = finiteNatSum count term + term count := rfl

/-- Pointwise equality on a displayed prefix preserves its natural sum. -/
theorem finiteNatSum_congr
    (count : Nat) (first second : Nat → Nat)
    (equal : ∀ index, index < count → first index = second index) :
    finiteNatSum count first = finiteNatSum count second := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteNatSum_succ_last, finiteNatSum_succ_last,
        inductionHypothesis (fun index indexBelow =>
          equal index (by omega0)), equal count (by omega0)]

/-- Addition distributes through a bounded natural sum. -/
theorem finiteNatSum_add
    (count : Nat) (first second : Nat → Nat) :
    finiteNatSum count (fun index => first index + second index) =
      finiteNatSum count first + finiteNatSum count second := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteNatSum_succ_last, finiteNatSum_succ_last,
        finiteNatSum_succ_last, inductionHypothesis]
      omega0

/-- Two explicitly bounded natural sums may be interchanged. -/
theorem finiteNatSum_swap
    (firstCount secondCount : Nat) (term : Nat → Nat → Nat) :
    finiteNatSum firstCount (fun first =>
        finiteNatSum secondCount (fun second => term first second)) =
      finiteNatSum secondCount (fun second =>
        finiteNatSum firstCount (fun first => term first second)) := by
  induction firstCount with
  | zero =>
      rw [finiteNatSum_zero]
      have zeros : finiteNatSum secondCount (fun _ : Nat => 0) = 0 := by
        induction secondCount with
        | zero => rfl
        | succ secondCount inductionHypothesis =>
            rw [finiteNatSum_succ_last, inductionHypothesis]
      exact zeros.symm
  | succ firstCount inductionHypothesis =>
      rw [finiteNatSum_succ_last, inductionHypothesis]
      have expanded :
          finiteNatSum secondCount (fun second =>
              finiteNatSum (firstCount + 1) (fun first =>
                term first second)) =
            finiteNatSum secondCount (fun second =>
              finiteNatSum firstCount (fun first => term first second) +
                term firstCount second) := by
        apply finiteNatSum_congr
        intro second secondBelow
        rw [finiteNatSum_succ_last]
      rw [expanded, finiteNatSum_add]

/-- A bounded sum of ones is its displayed natural length. -/
theorem finiteNatSum_one (count : Nat) :
    finiteNatSum count (fun _ : Nat => 1) = count := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteNatSum_succ_last, inductionHypothesis]

/-- A bounded equality indicator has exactly one hit when its target lies in
the requested prefix, and none otherwise. -/
theorem finiteNatSum_natEquals (count target : Nat) :
    finiteNatSum count (fun index =>
        if finiteNatEquals index target then 1 else 0) =
      if finiteNatLess target count then 1 else 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteNatSum_succ_last, inductionHypothesis]
      by_cases targetBelow : target < count
      · have countNotTarget : count ≠ target := by omega0
        rw [show finiteNatLess target count = true by
            exact (finiteNatLess_eq_true target count).2 targetBelow,
          show finiteNatLess target (count + 1) = true by
            exact (finiteNatLess_eq_true target (count + 1)).2 (by omega0),
          show finiteNatEquals count target = false by
            exact finiteBool_eq_false_of_not_eq_true _ (fun equality =>
              countNotTarget ((finiteNatEquals_eq_true count target).1 equality))]
        rfl
      · by_cases targetEquals : target = count
        · subst target
          rw [show finiteNatLess count count = false by
              exact finiteBool_eq_false_of_not_eq_true _ (fun below =>
                (Nat.lt_irrefl count)
                  ((finiteNatLess_eq_true count count).1 below)),
            show finiteNatLess count (count + 1) = true by
              exact (finiteNatLess_eq_true count (count + 1)).2 (by omega0),
            show finiteNatEquals count count = true by
              exact (finiteNatEquals_eq_true count count).2 rfl]
          rfl
        · have targetAbove : count < target := by omega0
          rw [show finiteNatLess target count = false by
              exact finiteBool_eq_false_of_not_eq_true _ (fun below =>
                targetBelow ((finiteNatLess_eq_true target count).1 below)),
            show finiteNatLess target (count + 1) = false by
              exact finiteBool_eq_false_of_not_eq_true _ (fun below =>
                (by
                  have := (finiteNatLess_eq_true target (count + 1)).1 below
                  omega0)),
            show finiteNatEquals count target = false by
              exact finiteBool_eq_false_of_not_eq_true _ (fun equality =>
                targetEquals
                  ((finiteNatEquals_eq_true count target).1 equality).symm)]
          rfl

/-- The indicator sum is the length of the corresponding explicitly filtered
natural range. -/
theorem finiteNatSum_indicator_eq_filter_length
    (count : Nat) (predicate : Nat → Bool) :
    finiteNatSum count (fun index => if predicate index then 1 else 0) =
      ((List.range count).filter predicate).length := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finiteNatSum_succ_last, List.range_succ,
        List.filter_append, List.length_append, inductionHypothesis]
      cases predicateEquation : predicate count <;> simp [predicateEquation]

/-- Euler's totient as the literal finite list of coprime labels
`0, ..., modulus-1`. -/
def finiteTotient (modulus : Nat) : Nat :=
  ((List.range modulus).filter fun residue =>
    finiteGcdEquals modulus 1 residue).length

@[simp] theorem finiteTotient_zero : finiteTotient 0 = 0 := rfl

@[simp] theorem finiteTotient_one : finiteTotient 1 = 1 := rfl

/-- The explicitly filtered gcd fibre. -/
def finiteGcdFiberCount (number divisor : Nat) : Nat :=
  ((List.range number).filter fun residue =>
    finiteGcdEquals number divisor residue).length

/-- For a displayed divisor `d | n`, multiplication by `d` is an explicit
bijection from the coprime labels below `n/d` to the gcd-`d` fibre below `n`. -/
theorem finiteTotient_div_of_dvd {number divisor : Nat}
    (divides : divisor ∣ number) :
    finiteTotient (number / divisor) =
      finiteGcdFiberCount number divisor := by
  rcases divisor.eq_zero_or_pos with divisorZero | divisorPositive
  · subst divisor
    have numberZero : number = 0 := Nat.eq_zero_of_zero_dvd divides
    subst number
    rfl
  · rcases divides with ⟨quotient, rfl⟩
    rw [Nat.mul_div_cancel_left quotient divisorPositive]
    unfold finiteTotient finiteGcdFiberCount
    let source := (List.range quotient).filter fun residue =>
      finiteGcdEquals quotient 1 residue
    let target := (List.range (divisor * quotient)).filter fun residue =>
      finiteGcdEquals (divisor * quotient) divisor residue
    have multiplyInjective : Function.Injective (fun value : Nat =>
        divisor * value) := by
      intro left right equality
      exact Nat.eq_of_mul_eq_mul_left divisorPositive equality
    have sourceRangeNodup : (List.range quotient).Nodup :=
      finiteRange_nodup quotient
    have targetRangeNodup :
        (List.range (divisor * quotient)).Nodup :=
      finiteRange_nodup (divisor * quotient)
    have sourceNodup : source.Nodup := sourceRangeNodup.filter _
    have targetNodup : target.Nodup := targetRangeNodup.filter _
    have permutation : List.Perm
        (source.map (fun residue => divisor * residue)) target := by
      apply (List.perm_ext_iff_of_nodup
        (QuotientFreeList.nodup_map_of_injective multiplyInjective sourceNodup)
        targetNodup).2
      intro residue
      unfold source target
      constructor
      · intro mappedMember
        rcases QuotientFreeList.mem_map.mp mappedMember with
          ⟨label, filteredMember, labelEquality⟩
        rcases List.mem_filter.mp filteredMember with
          ⟨labelRangeMember, coprimeTest⟩
        have labelBelow :=
          QuotientFreeList.mem_range.mp labelRangeMember
        have coprime :=
          (finiteGcdEquals_eq_true quotient 1 label).mp coprimeTest
        subst residue
        apply List.mem_filter.mpr
        constructor
        · apply QuotientFreeList.mem_range.mpr
          exact Nat.mul_lt_mul_of_pos_left labelBelow divisorPositive
        · apply (finiteGcdEquals_eq_true
            (divisor * quotient) divisor (divisor * label)).mpr
          rw [CanonicalGCD.compute_gcd_mul_left, coprime, mul_one]
      · intro filteredMember
        rcases List.mem_filter.mp filteredMember with
          ⟨residueRangeMember, gcdTest⟩
        have residueBelow :=
          QuotientFreeList.mem_range.mp residueRangeMember
        have gcdEquation := (finiteGcdEquals_eq_true
          (divisor * quotient) divisor residue).mp gcdTest
        have divisorDividesResidue : divisor ∣ residue := by
          rw [← gcdEquation]
          exact (CanonicalGCD.compute_spec _ _).2.2
        rcases divisorDividesResidue with ⟨label, rfl⟩
        apply QuotientFreeList.mem_map.mpr
        refine ⟨label, ?_, rfl⟩
        apply List.mem_filter.mpr
        constructor
        · apply QuotientFreeList.mem_range.mpr
          exact finite_lt_of_mul_lt_mul_left residueBelow
        · apply (finiteGcdEquals_eq_true quotient 1 label).mpr
          rw [CanonicalGCD.compute_gcd_mul_left,
            Nat.mul_eq_left divisorPositive.ne'] at gcdEquation
          exact gcdEquation
    have lengths := permutation.length_eq
    rw [List.length_map] at lengths
    exact lengths

/-- Scan all possible divisor labels in quotient coordinates. -/
def finiteDivisorQuotientTotientSum (number : Nat) : Nat :=
  finiteNatSum (number + 1) fun divisor =>
    if finiteDivides divisor number then
      finiteTotient (number / divisor) else 0

/-- A nondivisor cannot label a gcd fibre. -/
theorem finiteGcdFiberCount_eq_zero_of_not_dvd
    {number divisor : Nat} (notDivides : ¬ divisor ∣ number) :
    finiteGcdFiberCount number divisor = 0 := by
  unfold finiteGcdFiberCount
  cases filteredEquation : (List.range number).filter
      (fun residue => finiteGcdEquals number divisor residue) with
  | nil => rfl
  | cons residue remaining =>
      have member : residue ∈ (List.range number).filter
          (fun candidate => finiteGcdEquals number divisor candidate) := by
        rw [filteredEquation]
        exact List.mem_cons_self
      have gcdEquation := (finiteGcdEquals_eq_true
        number divisor residue).1 (List.mem_filter.mp member).2
      have contradiction : False := by
        apply notDivides
        rw [← gcdEquation]
        exact (CanonicalGCD.compute_spec _ _).2.1
      exact contradiction.elim

/-- A gcd-fibre count is its bounded equality-indicator sum. -/
theorem finiteGcdFiberCount_eq_indicator_sum (number divisor : Nat) :
    finiteGcdFiberCount number divisor =
      finiteNatSum number (fun residue =>
        if finiteGcdEquals number divisor residue then 1 else 0) := by
  exact (finiteNatSum_indicator_eq_filter_length number
    (finiteGcdEquals number divisor)).symm

/-- The finite gcd fibres partition the displayed residue prefix, so their
totient counts add to `n`. -/
theorem finiteDivisorQuotientTotientSum_eq (number : Nat) :
    finiteDivisorQuotientTotientSum number = number := by
  have divisorTerm (divisor : Nat) (divisorBelow : divisor < number + 1) :
      (if finiteDivides divisor number then
          finiteTotient (number / divisor) else 0) =
        finiteGcdFiberCount number divisor := by
    by_cases divides : divisor ∣ number
    · rw [show finiteDivides divisor number = true by
          exact (finiteDivides_eq_true divisor number).2 divides,
        if_pos rfl, finiteTotient_div_of_dvd divides]
    · rw [show finiteDivides divisor number = false by
          exact finiteBool_eq_false_of_not_eq_true _ (fun truth =>
            divides ((finiteDivides_eq_true divisor number).1 truth)),
        if_neg (by decide), finiteGcdFiberCount_eq_zero_of_not_dvd divides]
  have oneFiber (residue : Nat) (residueBelow : residue < number) :
      finiteNatSum (number + 1) (fun divisor =>
          if finiteGcdEquals number divisor residue then 1 else 0) = 1 := by
    let common := (CanonicalGCD.compute number residue).gcd
    have commonBelow : common < number + 1 := by
      unfold common
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (by omega0)
        (CanonicalGCD.compute_spec number residue).2.1)
    calc
      finiteNatSum (number + 1) (fun divisor =>
          if finiteGcdEquals number divisor residue then 1 else 0) =
        finiteNatSum (number + 1) (fun divisor =>
          if finiteNatEquals divisor common then 1 else 0) := by
            apply finiteNatSum_congr
            intro divisor divisorBelow
            by_cases equality :
                (CanonicalGCD.compute number residue).gcd = divisor
            · have reverse :
                  divisor = (CanonicalGCD.compute number residue).gcd :=
                equality.symm
              rw [show finiteGcdEquals number divisor residue = true by
                    exact (finiteGcdEquals_eq_true
                      number divisor residue).2 equality,
                show finiteNatEquals divisor common = true by
                    exact (finiteNatEquals_eq_true divisor common).2 reverse]
            · have reverse :
                  divisor ≠ (CanonicalGCD.compute number residue).gcd := by
                intro reversed
                exact equality reversed.symm
              rw [show finiteGcdEquals number divisor residue = false by
                    exact finiteBool_eq_false_of_not_eq_true _ (fun truth =>
                      equality ((finiteGcdEquals_eq_true
                        number divisor residue).1 truth)),
                show finiteNatEquals divisor common = false by
                    exact finiteBool_eq_false_of_not_eq_true _ (fun truth =>
                      reverse ((finiteNatEquals_eq_true
                        divisor common).1 truth))]
      _ = if finiteNatLess common (number + 1) then 1 else 0 :=
        finiteNatSum_natEquals (number + 1) common
      _ = 1 := by
        rw [show finiteNatLess common (number + 1) = true by
          exact (finiteNatLess_eq_true common (number + 1)).2 commonBelow,
          if_pos rfl]
  unfold finiteDivisorQuotientTotientSum
  calc
    finiteNatSum (number + 1) (fun divisor =>
        if finiteDivides divisor number then
          finiteTotient (number / divisor) else 0) =
      finiteNatSum (number + 1) (finiteGcdFiberCount number) := by
        apply finiteNatSum_congr
        exact divisorTerm
    _ = finiteNatSum (number + 1) (fun divisor =>
        finiteNatSum number (fun residue =>
          if finiteGcdEquals number divisor residue then 1 else 0)) := by
            apply finiteNatSum_congr
            intro divisor divisorBelow
            exact finiteGcdFiberCount_eq_indicator_sum number divisor
    _ = finiteNatSum number (fun residue =>
        finiteNatSum (number + 1) (fun divisor =>
          if finiteGcdEquals number divisor residue then 1 else 0)) :=
            finiteNatSum_swap (number + 1) number _
    _ = finiteNatSum number (fun _ : Nat => 1) := by
      apply finiteNatSum_congr
      exact oneFiber
    _ = number := finiteNatSum_one number

end RFAP
