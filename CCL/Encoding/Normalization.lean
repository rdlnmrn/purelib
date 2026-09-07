import mathlib.Tactic.QuotientFreeOmega
import Lean.Elab.Tactic.Omega

/-!
# Choice-free bounded binary normalization

The three normalization exponents are found by transparent recursion with an
explicit natural-number fuel bound.  No finite set, extremum operator, or
unbounded search is used.
-/

namespace CCL.Normalization

/-- The elementary estimate `n + 1 ≤ 2ⁿ` used to bound every scan. -/
theorem succ_le_two_pow (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [Nat.pow_succ]
      have step : n + 2 ≤ 2 * (n + 1) := by omega
      simpa only [Nat.mul_comm] using
        Nat.le_trans step (Nat.mul_le_mul_left 2 inductionHypothesis)

/-- Result of scanning forward for the last consecutive true predicate. -/
structure LastResult (predicate : Nat → Prop) (start : Nat) where
  exponent : Nat
  start_le : start ≤ exponent
  holds : predicate exponent
  next_fails : ¬predicate (exponent + 1)

/-- Starting from one true value, scan forward until the next value is false.
The supplied terminal failure makes exhaustion constructive. -/
def scanLast (predicate : Nat → Prop)
    (decidablePredicate : (index : Nat) → Decidable (predicate index)) :
    (start fuel : Nat) → predicate start →
      ¬predicate (start + fuel + 1) → LastResult predicate start
  | start, 0, startHolds, terminalFailure =>
      ⟨start, Nat.le_refl start, startHolds, by
        simpa only [Nat.add_zero] using terminalFailure⟩
  | start, fuel + 1, startHolds, terminalFailure =>
      if nextHolds : predicate (start + 1) then
        let result := scanLast predicate decidablePredicate (start + 1) fuel
          nextHolds (by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              terminalFailure)
        ⟨result.exponent,
          Nat.le_trans (Nat.le_succ start) result.start_le,
          result.holds,
          result.next_fails⟩
      else
        ⟨start, Nat.le_refl start, startHolds, nextHolds⟩

/-- Result of scanning forward for the first true predicate. -/
structure FirstResult (predicate : Nat → Prop) (start : Nat) where
  exponent : Nat
  start_le : start ≤ exponent
  holds : predicate exponent
  before_fails : ∀ index, start ≤ index → index < exponent →
    ¬predicate index

/-- Scan forward for the first true value.  The supplied terminal witness
makes exhaustion constructive. -/
def scanFirst (predicate : Nat → Prop)
    (decidablePredicate : (index : Nat) → Decidable (predicate index)) :
    (start fuel : Nat) → predicate (start + fuel) →
      FirstResult predicate start
  | start, 0, terminalHolds =>
      ⟨start, Nat.le_refl start, by
        simpa only [Nat.add_zero] using terminalHolds,
        by
          intro index startLe indexLt
          exact (Nat.not_lt_of_ge startLe indexLt).elim⟩
  | start, fuel + 1, terminalHolds =>
      if startHolds : predicate start then
        ⟨start, Nat.le_refl start, startHolds,
          by
            intro index startLe indexLt
            exact (Nat.not_lt_of_ge startLe indexLt).elim⟩
      else
        let result := scanFirst predicate decidablePredicate (start + 1) fuel
          (by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              terminalHolds)
        ⟨result.exponent,
          Nat.le_trans (Nat.le_succ start) result.start_le,
          result.holds,
          by
            intro index startLe indexLt
            by_cases atStart : index = start
            · simpa only [atStart] using startHolds
            · have startLt : start < index :=
                Nat.lt_of_le_of_ne startLe (Ne.symm atStart)
              exact result.before_fails index
                (Nat.succ_le_of_lt startLt) indexLt⟩

/-- A certified result of the high branch of binary normalization. -/
structure HighResult (numeratorNorm denominatorNorm : Nat) where
  exponent : Nat
  positive : 1 ≤ exponent
  lower : 2 ^ exponent * denominatorNorm ≤ numeratorNorm
  upper : numeratorNorm < 2 ^ (exponent + 1) * denominatorNorm

/-- A certified result of the low branch of binary normalization. -/
structure LowResult (numeratorNorm denominatorNorm : Nat) where
  exponent : Nat
  lower : denominatorNorm ≤ 2 ^ exponent * numeratorNorm
  upper : 2 ^ exponent * numeratorNorm < 2 * denominatorNorm

/-- A certified result of the strict loop branch of binary normalization. -/
structure LoopResult (numeratorNorm denominatorNorm : Nat) where
  exponent : Nat
  lower : 2 ^ exponent * denominatorNorm < numeratorNorm
  upper : numeratorNorm ≤ 2 ^ (exponent + 1) * denominatorNorm

private theorem pow_mul_mono_exponent (factor left right : Nat)
    (order : left ≤ right) :
    2 ^ left * factor ≤ 2 ^ right * factor :=
  Nat.mul_le_mul_right factor
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) order)

/-- The two adjacent power bounds determine a high-normalization exponent
uniquely.  Concrete certificates can therefore avoid reducing the search
that originally found the exponent. -/
theorem HighResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : HighResult numeratorNorm denominatorNorm)
    (candidateLower :
      2 ^ candidate * denominatorNorm ≤ numeratorNorm)
    (candidateUpper :
      numeratorNorm < 2 ^ (candidate + 1) * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent denominatorNorm
        (candidate + 1) result.exponent nextLe
      omega
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent denominatorNorm
        (result.exponent + 1) candidate nextLe
      omega

/-- The two adjacent power bounds determine a low-normalization exponent
uniquely. -/
theorem LowResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : LowResult numeratorNorm denominatorNorm)
    (candidateLower :
      denominatorNorm ≤ 2 ^ candidate * numeratorNorm)
    (candidateUpper :
      2 ^ candidate * numeratorNorm < 2 * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent numeratorNorm
        (candidate + 1) result.exponent nextLe
      have twiceDenominatorLe :
          2 * denominatorNorm ≤ 2 ^ (candidate + 1) * numeratorNorm := by
        calc
          2 * denominatorNorm ≤
              2 * (2 ^ candidate * numeratorNorm) :=
            Nat.mul_le_mul_left 2 candidateLower
          _ = 2 ^ (candidate + 1) * numeratorNorm := by
            rw [Nat.pow_succ]
            ring1
      have impossible := Nat.le_trans twiceDenominatorLe powerLe
      omega
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent numeratorNorm
        (result.exponent + 1) candidate nextLe
      have twiceDenominatorLe :
          2 * denominatorNorm ≤
            2 ^ (result.exponent + 1) * numeratorNorm := by
        calc
          2 * denominatorNorm ≤
              2 * (2 ^ result.exponent * numeratorNorm) :=
            Nat.mul_le_mul_left 2 resultLower
          _ = 2 ^ (result.exponent + 1) * numeratorNorm := by
            rw [Nat.pow_succ]
            ring1
      have impossible := Nat.le_trans twiceDenominatorLe powerLe
      omega

/-- The two adjacent power bounds determine a loop-normalization exponent
uniquely. -/
theorem LoopResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : LoopResult numeratorNorm denominatorNorm)
    (candidateLower :
      2 ^ candidate * denominatorNorm < numeratorNorm)
    (candidateUpper :
      numeratorNorm ≤ 2 ^ (candidate + 1) * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent denominatorNorm
        (candidate + 1) result.exponent nextLe
      omega
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := pow_mul_mono_exponent denominatorNorm
        (result.exponent + 1) candidate nextLe
      omega

/-- High normalization by a bounded last-true scan starting at exponent one. -/
def high (numeratorNorm denominatorNorm : Nat)
    (denominatorPositive : 0 < denominatorNorm)
    (highBranch : 2 * denominatorNorm ≤ numeratorNorm) :
    HighResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    2 ^ exponent * denominatorNorm ≤ numeratorNorm
  have starts : predicate 1 := by
    simpa only [predicate, Nat.pow_one] using highBranch
  have terminalFailure :
      ¬predicate (1 + numeratorNorm + 1) := by
    intro terminalHolds
    have powerBound : numeratorNorm + 3 ≤ 2 ^ (numeratorNorm + 2) :=
      succ_le_two_pow (numeratorNorm + 2)
    have denominatorAtLeastOne : 1 ≤ denominatorNorm := denominatorPositive
    have productBound :
        2 ^ (numeratorNorm + 2) ≤
          2 ^ (numeratorNorm + 2) * denominatorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ (numeratorNorm + 2)) denominatorAtLeastOne
    have impossible : numeratorNorm + 3 ≤ numeratorNorm := by
      exact Nat.le_trans powerBound (Nat.le_trans productBound (by
        simpa only [predicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using terminalHolds))
    have successorLeSelf : Nat.succ numeratorNorm ≤ numeratorNorm := by
      simpa only [Nat.succ_eq_add_one] using
        Nat.le_trans
          (Nat.add_le_add_left (by decide : 1 ≤ 3) numeratorNorm) impossible
    exact (Nat.not_succ_le_self numeratorNorm successorLeSelf).elim
  let result := scanLast predicate (fun _ => inferInstance) 1 numeratorNorm
    starts terminalFailure
  refine ⟨result.exponent, result.start_le, result.holds, ?_⟩
  exact Nat.lt_of_not_ge result.next_fails

/-- Low normalization by a bounded first-true scan starting at exponent zero. -/
def low (numeratorNorm denominatorNorm : Nat)
    (numeratorPositive : 0 < numeratorNorm)
    (_denominatorPositive : 0 < denominatorNorm)
    (lowBranch : numeratorNorm < 2 * denominatorNorm) :
    LowResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    denominatorNorm ≤ 2 ^ exponent * numeratorNorm
  have powerBound : denominatorNorm + 1 ≤ 2 ^ denominatorNorm :=
    succ_le_two_pow denominatorNorm
  have numeratorAtLeastOne : 1 ≤ numeratorNorm := numeratorPositive
  have terminalHolds : predicate (0 + denominatorNorm) := by
    have denominatorLePower : denominatorNorm ≤ 2 ^ denominatorNorm :=
      Nat.le_trans (Nat.le_add_right denominatorNorm 1) powerBound
    have powerLeProduct :
        2 ^ denominatorNorm ≤ 2 ^ denominatorNorm * numeratorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ denominatorNorm) numeratorAtLeastOne
    simpa only [predicate, Nat.zero_add] using
      Nat.le_trans denominatorLePower powerLeProduct
  let result := scanFirst predicate (fun _ => inferInstance) 0 denominatorNorm
    terminalHolds
  refine ⟨result.exponent, result.holds, ?_⟩
  cases exponentIdentity : result.exponent with
  | zero =>
      simpa only [exponentIdentity, Nat.pow_zero, Nat.one_mul] using lowBranch
  | succ previous =>
      have previousFails :
          ¬denominatorNorm ≤ 2 ^ previous * numeratorNorm := by
        have previousLtExponent : previous < result.exponent := by
          rw [exponentIdentity]
          exact Nat.lt_succ_self previous
        exact result.before_fails previous (Nat.zero_le previous)
          previousLtExponent
      have previousLt :
          2 ^ previous * numeratorNorm < denominatorNorm :=
        Nat.lt_of_not_ge previousFails
      calc
        2 ^ (previous + 1) * numeratorNorm =
            2 * (2 ^ previous * numeratorNorm) := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_comm, Nat.mul_left_comm]
        _ < 2 * denominatorNorm :=
          by
            simpa only [two_mul] using
              Nat.add_lt_add previousLt previousLt

/-- Loop normalization by a bounded last-true scan starting at exponent zero. -/
def loop (numeratorNorm denominatorNorm : Nat)
    (denominatorPositive : 0 < denominatorNorm)
    (strictBranch : denominatorNorm < numeratorNorm) :
    LoopResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    2 ^ exponent * denominatorNorm < numeratorNorm
  have starts : predicate 0 := by
    simpa only [predicate, Nat.pow_zero, Nat.one_mul] using strictBranch
  have terminalFailure : ¬predicate (0 + numeratorNorm + 1) := by
    intro terminalHolds
    have powerBound : numeratorNorm + 2 ≤ 2 ^ (numeratorNorm + 1) :=
      succ_le_two_pow (numeratorNorm + 1)
    have denominatorAtLeastOne : 1 ≤ denominatorNorm := denominatorPositive
    have productBound :
        2 ^ (numeratorNorm + 1) ≤
          2 ^ (numeratorNorm + 1) * denominatorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ (numeratorNorm + 1)) denominatorAtLeastOne
    have impossible : numeratorNorm + 2 < numeratorNorm := by
      exact Nat.lt_of_le_of_lt powerBound (Nat.lt_of_le_of_lt productBound (by
        simpa only [predicate, Nat.zero_add] using terminalHolds))
    exact (Nat.not_lt_of_ge (Nat.le_add_right numeratorNorm 2) impossible).elim
  let result := scanLast predicate (fun _ => inferInstance) 0 numeratorNorm
    starts terminalFailure
  refine ⟨result.exponent, result.holds, ?_⟩
  exact Nat.le_of_not_gt result.next_fails

end CCL.Normalization
