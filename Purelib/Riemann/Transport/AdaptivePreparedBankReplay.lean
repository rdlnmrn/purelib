module
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.Riemann.Transport.BoundedPreparedBankReplay
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
Exact replay of adaptive bank selection.  Every rejected earlier depth
retains the bounded scanner's actual failure; an incomplete replay must not
be used as such a failure.  Private implementation links stay local so the
widely imported selector and generated coefficient banks are not rebuilt.
-/

namespace Purelib.Riemann.Transport.AdaptivePreparedBankReplay

open Purelib.Data.Nat
open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive (Task Banks Selected maximumDepth)
open Purelib.Riemann.Readings Purelib.Riemann.Integration
open Purelib.Riemann.Branches.PreparedSheetContinuation (GaussianPolynomial Coordinate)

variable {polynomial : GaussianPolynomial}

open Purelib.RootIsolation in
/-- Try preparing every retained task at the given depth and positive diameter.

Returns the exact dependent bank list produced by the adaptive bank procedure, or none if that attempt fails. -/
@[expose] def tryBanks (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) : Option
      (SquareRoot.Preparation.Bank.Adaptive.Banks depth diameter positive tasks) :=
  SquareRoot.Preparation.Bank.Adaptive.tryBanks depth diameter positive tasks

open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Retained execution branches for a fixed-depth bank attempt.

Records successful task preparations and their exact outcome identities, or a deferred inconclusive result for the first
failed task. -/
inductive Trial (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :
    List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial) → Type where
  /-- The empty task list has an empty successful trial. -/ | nil : Trial depth diameter positive []
  /-- Deferred inconclusive result for the first failed task. -/ | miss {task :
    SquareRoot.Preparation.Bank.Adaptive.Task polynomial} {tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task
    polynomial)}
      (failure : Thunk (BoundedPreparedBanks.Inconclusive depth diameter positive task.path task.within task.owner)) :
      Trial depth diameter positive (task :: tasks)
  /-- Accepted current bank, its attempt identity and the remaining task trial. -/ | cons {task :
    SquareRoot.Preparation.Bank.Adaptive.Task polynomial} {tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task
    polynomial)}
      (accepted : BoundedPreparedBanks.PathSuccess depth diameter positive task.path task.within task.owner)
      (found : BoundedPreparedBanks.attempt depth diameter positive task.path task.within task.owner = .ok accepted)
      (rest : Trial depth diameter positive tasks) : Trial depth diameter positive (task :: tasks)

constructive_injectivity Trial

section
open Purelib.RootIsolation
/-- Read the retained trial as an optional dependent bank list.

Uses the accepted banks already stored in the trial and returns none at a retained failure. -/
@[expose] def Trial.value {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter} {tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)} :
    Trial depth diameter positive tasks → Option (SquareRoot.Preparation.Bank.Adaptive.Banks depth diameter positive
      tasks)
  | .nil => some .nil
  | .miss _ => none
  | .cons accepted _ rest => match rest.value with
      | none => none
      | some banks => some (.cons accepted.bank banks)

/-- The retained trial reproduces the original fixed-depth bank attempt.

Induction follows the stored success equations and the deferred failure's attempt certificate without choosing new task
results. -/
theorem Trial.equation {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)} (trial : Trial depth diameter positive tasks)
      :
    tryBanks depth diameter positive tasks = trial.value := by
  induction trial with
  | nil => rfl
  | @miss task tasks failure =>
      unfold tryBanks
      unfold SquareRoot.Preparation.Bank.Adaptive.tryBanks
      rw [failure.get.attempt_error]
      rfl
  | @cons task tasks accepted found rest ih =>
      unfold tryBanks
      unfold SquareRoot.Preparation.Bank.Adaptive.tryBanks
      rw [found]
      change (match tryBanks depth diameter positive tasks with
        | none => none
        | some banks => some (SquareRoot.Preparation.Bank.Adaptive.Banks.cons accepted.bank banks)) = _
      rw [ih]
      rfl

end

open Purelib.RootIsolation
/-- Run the original adaptive bank search over its retained finite depth interval.

Keeps the exact upper-depth identity, minimum bound and remaining-step equality supplied to the executable search. -/
@[expose] def search (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter : Coordinate)
  (positive : 0 < diameter)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum)
    (depth : Nat) (minimumLe : minimum ≤ depth) (remaining : Nat) (bound : upper = depth + remaining) :
    SquareRoot.Preparation.Bank.Adaptive.Selected tasks diameter positive minimum :=
  SquareRoot.Preparation.Bank.Adaptive.search tasks diameter positive minimum upper upperEq depth minimumLe remaining
    bound

/-- The public adaptive selector starts the same bounded search.

The initial depth is the requested minimum and the upper depth is its maximum with the tasks' certified depth bound. -/
theorem selectFrom_eq (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter : Coordinate)
  (positive : 0 < diameter)
    (minimum : Nat) :
    SquareRoot.Preparation.Bank.Adaptive.selectFrom tasks diameter positive minimum =
      search tasks diameter positive minimum (max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
        minimum) rfl minimum
        (Nat.le_refl minimum) (max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks) minimum - minimum)
          (by
          apply Eq.symm
          apply Subtraction.add_sub_of_le
          rw [Order.max_eq_natMax]
          exact Order.le_max_right _ _) := rfl

/-- Package accepted banks with their original adaptive depth bounds.

Retains the exact upper-depth equation, current depth and task-indexed banks at a successful nonterminal search step. -/
@[expose] def selected (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter : Coordinate)
  (positive : 0 < diameter)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum)
    (depth : Nat) (minimumLe : minimum ≤ depth) (remaining : Nat) (bound : upper = depth + (remaining + 1))
    (banks : SquareRoot.Preparation.Bank.Adaptive.Banks depth diameter positive tasks) :
      SquareRoot.Preparation.Bank.Adaptive.Selected tasks diameter positive minimum :=
  { upperDepth := upper, upperDepth_eq := upperEq, depth := depth, minimum_le := minimumLe,
    depth_le := by clear upperEq; omega0, banks := banks }

/-- A nonterminal search step tests the current depth and follows its exact outcome.

Success packages the retained banks; a miss increments the current depth and decreases the remaining interval. -/
private theorem search_step (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter :
  Coordinate) (positive : 0 < diameter)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum)
    (depth : Nat) (minimumLe : minimum ≤ depth) (remaining : Nat) (bound : upper = depth + (remaining + 1)) :
    search tasks diameter positive minimum upper upperEq depth minimumLe (remaining + 1) bound =
      match tryBanks depth diameter positive tasks with
      | some banks => selected tasks diameter positive minimum upper upperEq depth minimumLe remaining bound banks
      | none => search tasks diameter positive minimum upper upperEq (depth + 1) (by clear upperEq; omega0) remaining
        (by clear upperEq; omega0) := by
  rfl

/-- A successful retained trial determines the adaptive search result.

Reuses the trial's exact optional-bank equation to identify the selected banks at the current depth. -/
theorem search_accept (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter : Coordinate)
  (positive : 0 < diameter)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum)
    (depth : Nat) (minimumLe : minimum ≤ depth) (remaining : Nat) (bound : upper = depth + (remaining + 1))
    (trial : Trial depth diameter positive tasks) (banks : SquareRoot.Preparation.Bank.Adaptive.Banks depth diameter
      positive tasks)
    (found : trial.value = some banks) :
    search tasks diameter positive minimum upper upperEq depth minimumLe (remaining + 1) bound =
      selected tasks diameter positive minimum upper upperEq depth minimumLe remaining bound banks := by
  rw [search_step, trial.equation, found]

/-- A retained failed trial advances the adaptive search by one depth.

Preserves the original tasks, upper bound and remaining-depth accounting after the failed fixed-depth attempt. -/
theorem search_miss (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) (diameter : Coordinate)
  (positive : 0 < diameter)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum)
    (depth : Nat) (minimumLe : minimum ≤ depth) (remaining : Nat) (bound : upper = depth + (remaining + 1))
    (trial : Trial depth diameter positive tasks) (empty : trial.value = none) :
    search tasks diameter positive minimum upper upperEq depth minimumLe (remaining + 1) bound =
      search tasks diameter positive minimum upper upperEq (depth + 1) (by clear upperEq; omega0) remaining (by
          clear upperEq;
          omega0) := by
  rw [search_step, trial.equation, empty]

end Purelib.Riemann.Transport.AdaptivePreparedBankReplay
