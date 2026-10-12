module

public import Purelib.Data.List.Range.Basic
public import Purelib.NumberTheory.FourSquares.Descent
import Purelib.NumberTheory.FourSquares.Basic
import Purelib.NumberTheory.Prime.Basic
import Purelib.Data.List.Search
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Divisibility
import Purelib.Algebra.Semiring.Nat

/-!
# Retained bounded factor recursion for natural four-square representations

The original natural input controls the bounded factor scan and both
recursive factors. Its exact cached representations are multiplied only
after both runs return, preserving the original factor order and roots.
-/

open Purelib.NumberTheory
open Purelib.Data
open Purelib.Data.Nat
open Purelib.Algebra

namespace Purelib.NumberTheory.FourSquares.Natural

attribute [local instance high] Semiring.Nat.commSemiring
attribute [local instance high] CommSemiring.toSemiring Semiring.toMonoid
attribute [local instance high] Monoid.toSemigroup

/-- Compute four retained natural roots representing the supplied natural.

The original bounded proper-factor scan selects its first accepted factor.
An empty scan supplies the same prime branch; a selected factor retains
both recursive representations before multiplying their exact cached roots. -/
@[expose] public def naturalRepresentation : (value : Nat) → Basic.Representation value :=
  Nat.strongRec (motive := fun value => Basic.Representation value) fun value recurse => by
    by_cases valueZero : value = 0
    · subst value
      exact ⟨0, 0, 0, 0, rfl⟩
    · by_cases valueOne : value = 1
      · subst value
        exact ⟨1, 0, 0, 0, rfl⟩
      · have valueAtLeastTwo : 2 ≤ value := by
          cases value with
          | zero => exact (valueZero rfl).elim
          | succ value =>
              cases value with
              | zero => exact (valueOne rfl).elim
              | succ value =>
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le value))
        let acceptedFactor : Nat → Bool := fun factor =>
          decide (2 ≤ factor) && decide (value % factor = 0)
        cases factorFound : (List.range value).find? acceptedFactor with
        | none =>
            have rejected :=
              List.Search.find?_eq_none.mp factorFound
            have valuePrime : NumberTheory.Prime value := by
              apply Prime.of_divisors valueAtLeastTwo
              intro divisor divisorDivides
              by_cases divisorOne : divisor = 1
              · exact Or.inl divisorOne
              · by_cases divisorValue : divisor = value
                · exact Or.inr divisorValue
                · have divisorPositive : 0 < divisor := by
                    cases divisor with
                    | zero =>
                        obtain ⟨factor, factorEquation⟩ := divisorDivides
                        exact (valueZero (factorEquation.trans (Nat.zero_mul factor))).elim
                    | succ divisor => exact Nat.zero_lt_succ divisor
                  have divisorAtLeastTwo : 2 ≤ divisor := by
                    cases divisor with
                    | zero => exact (Nat.not_lt_zero _ divisorPositive).elim
                    | succ divisor =>
                        cases divisor with
                        | zero => exact (divisorOne rfl).elim
                        | succ divisor =>
                            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le divisor))
                  have divisorAtMostValue : divisor ≤ value :=
                    Divisibility.le_of_dvd (Nat.pos_of_ne_zero valueZero) divisorDivides
                  have divisorBelow : divisor < value :=
                    Nat.lt_of_le_of_ne divisorAtMostValue divisorValue
                  have divisorMember : divisor ∈ List.range value :=
                    List.Range.Basic.mem_range.mpr divisorBelow
                  have divisorRejected := rejected divisor divisorMember
                  have divisorModulo : value % divisor = 0 :=
                    Divisibility.mod_eq_zero_of_dvd divisorDivides
                  have divisorAccepted : acceptedFactor divisor = true := by
                    change (decide (2 ≤ divisor) && decide (value % divisor = 0)) = true
                    rewrite [decide_eq_true divisorAtLeastTwo, decide_eq_true divisorModulo]
                    rfl
                  rw [divisorAccepted] at divisorRejected
                  exact False.elim (Bool.noConfusion divisorRejected)
            exact Descent.primeRepresentation value valuePrime
        | some factor =>
            have factorAccepted := List.Search.find?_eq_some_accepts_certificate factorFound
            have factorMember := List.Search.find?_eq_some_mem_certificate factorFound
            have factorConditions : 2 ≤ factor ∧ value % factor = 0 := by
              change (decide (2 ≤ factor) && decide (value % factor = 0)) = true at factorAccepted
              cases atLeastTwo : decide (2 ≤ factor) with
              | false =>
                  rw [atLeastTwo] at factorAccepted
                  exact Bool.noConfusion factorAccepted
              | true =>
                  rw [atLeastTwo] at factorAccepted
                  exact ⟨of_decide_eq_true atLeastTwo, of_decide_eq_true factorAccepted⟩
            have factorBelow : factor < value :=
              List.Range.Basic.mem_range.mp factorMember
            have factorDivides : factor ∣ value :=
              Divisibility.of_mod_eq_zero factorConditions.2
            let cofactor := value / factor
            have factorGreaterOne : 1 < factor := factorConditions.1
            have cofactorBelow : cofactor < value :=
              Division.div_lt_self (Nat.pos_of_ne_zero valueZero)
                factorGreaterOne
            have productEquation : factor * cofactor = value :=
              (Nat.mul_comm factor cofactor).trans (Division.div_mul_cancel factorDivides)
            let factorRepresentation := recurse factor factorBelow
            let cofactorRepresentation := recurse cofactor cofactorBelow
            exact productEquation ▸
              factorRepresentation.multiply cofactorRepresentation

end Purelib.NumberTheory.FourSquares.Natural
