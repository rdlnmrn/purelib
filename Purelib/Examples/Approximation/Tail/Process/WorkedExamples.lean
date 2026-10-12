module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Tail.Basic
public import Purelib.Approximation.Tail.Process
import Purelib.Data.Rat.Interval.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Approximation.Tail.Process.WorkedExamples

open Purelib
open Purelib.Examples
open Purelib.Data.Rat

/-! ## Finite tail budgets -/

/-- A retained partial amount three quarters with tail allowance one quarter. -/
def geometricBudget : Approximation.TailBudget where
  amount := 3 / 4
  remainder := 1 / 4
  remainder_nonnegative := by decide

/-- The retained coarse tail budget has endpoints three quarters and one. -/
example : geometricBudget.bound.lower = 3 / 4 ∧
    geometricBudget.bound.upper = 1 := by
  decide

/-- The retained quarter tail allowance resolves a half-tolerance request. -/
example : geometricBudget.Resolves (1 / 2) := by
  unfold Approximation.TailBudget.Resolves geometricBudget
  decide

/-- Advancing by one eighth with an eighth remaining refines the original bound.

Uses the exact nonnegative addition and conserved amount-plus-tail certificate. -/
example : Interval.Refines
    (geometricBudget.advance (1 / 8) (1 / 8) (by decide)).bound
    geometricBudget.bound := by
  apply geometricBudget.advance_bound_refines
  · decide
  · unfold Approximation.TailBudget.Conserves geometricBudget
    decide

/-- The exact amount one with zero remaining tail allowance. -/
def exactGeometricBudget : Approximation.TailBudget
  where
  amount := 1
  remainder := 0
  remainder_nonnegative := le_rfl

/-- The exact budget refines the original budget by adding one quarter.

Keeps the exact amount and remainder conservation equations with a nonnegative added contribution. -/
def exactGeometric_refines :
    Approximation.TailBudget.Refines exactGeometricBudget
      geometricBudget where
  added := 1 / 4
  added_nonnegative := by decide
  amount_eq := by decide
  remainder_eq := by decide

/-- A two-state tail process that completes its retained budget on request.

The original Boolean state selects the coarse or exact budget; every positive request reaches zero remainder and
preserves its certified refinement. -/
def terminatingTailProcess : Approximation.TailProcess
  where
  State := Bool
  budget finished := if finished then exactGeometricBudget else
    geometricBudget
  initial := false
  request _ _ _ := true
  request_refines state epsilon positive := by
    cases state
    · exact exactGeometric_refines
    · exact Approximation.TailBudget.Refines.refl exactGeometricBudget
  accurate state epsilon positive := by
    unfold Approximation.TailBudget.Resolves exactGeometricBudget
    exact positive
  refinesInitial state := by
    cases state
    · exact Approximation.TailBudget.Refines.refl geometricBudget
    · exact exactGeometric_refines

/-- Every positive request to the terminating tail process has bound width below tolerance. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (terminatingTailProcess.budget
      (terminatingTailProcess.request false epsilon positive)).bound.width <
        epsilon :=
  terminatingTailProcess.request_bound_width_lt false epsilon positive

end Purelib.Examples.Approximation.Tail.Process.WorkedExamples

end
