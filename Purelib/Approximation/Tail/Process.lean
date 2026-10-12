module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Approximation.Bound.Process
import Purelib.Approximation.OneSided.BoundProcess
public import Purelib.Approximation.Tail.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite monotone tail processes

This is a constructive surrogate for nonnegative monotone convergence.  A
state contains a displayed partial amount and a rational remainder budget.
Finite advances conserve the old remainder between a nonnegative new amount
and the new remainder.  Arbitrary accuracy is an executable request, not a
completed sum or a theorem about an infinite sequence.
-/

namespace Purelib.Approximation

namespace TailBudget

set_option genInjectivity false in
/-- A later partial amount obtained by consuming a displayed nonnegative piece of the earlier remainder. -/
structure Refines (inner outer : Approximation.TailBudget) : Type where
  /-- The retained amount consumed from the older tail budget. -/ added : Fraction.Rational
  /-- The consumed amount is nonnegative. -/ added_nonnegative : 0 ≤ added
  /-- The new partial amount adds exactly the retained consumed amount. -/ amount_eq : inner.amount = outer.amount +
    added
  /-- The old remainder splits exactly into the consumed amount and new remainder. -/ remainder_eq : outer.remainder =
    added + inner.remainder

constructive_injectivity Refines

namespace Refines

/-- Refine a tail budget by consuming the zero amount. -/
def refl (budget : Approximation.TailBudget) : Approximation.TailBudget.Refines budget budget where
  added := 0
  added_nonnegative := le_rfl
  amount_eq := by ring1
  remainder_eq := by ring1

/-- Compose tail refinements by adding their retained consumed amounts.

The resulting certificate preserves both exact partial-amount and remainder-conservation equations. -/
def trans {inner middle outer : Approximation.TailBudget}
    (innerMiddle : Approximation.TailBudget.Refines inner middle)
    (middleOuter : Approximation.TailBudget.Refines middle outer) : Approximation.TailBudget.Refines inner outer where
  added := middleOuter.added + innerMiddle.added
  added_nonnegative := add_nonneg middleOuter.added_nonnegative
    innerMiddle.added_nonnegative
  amount_eq := by
    rw [innerMiddle.amount_eq, middleOuter.amount_eq]
    ring1
  remainder_eq := by
    rw [middleOuter.remainder_eq, innerMiddle.remainder_eq]
    ring1

/-- Consumed tail makes the displayed partial amount monotone. -/
theorem amount_mono {inner outer : Approximation.TailBudget}
    (refines : Approximation.TailBudget.Refines inner outer) : outer.amount ≤ inner.amount := by
  rw [refines.amount_eq]
  exact le_add_of_nonneg_right refines.added_nonnegative

/-- Consumed tail makes the remainder antitone. -/
theorem remainder_antitone {inner outer : Approximation.TailBudget}
    (refines : Approximation.TailBudget.Refines inner outer) : inner.remainder ≤ outer.remainder := by
  rw [refines.remainder_eq]
  exact le_add_of_nonneg_left refines.added_nonnegative

/-- A conserved finite tail advance narrows its rational total enclosure. -/
theorem bound_refines {inner outer : Approximation.TailBudget}
    (refines : Approximation.TailBudget.Refines inner outer) :
    Interval.Refines inner.bound outer.bound := by
  constructor
  · dsimp only [TailBudget.bound]
    exact refines.amount_mono
  · dsimp only [TailBudget.bound]
    rw [refines.amount_eq, refines.remainder_eq]
    exact le_of_eq (by ring1)

/-- Once a tail request is met, every conserved finite advance retains it. -/
theorem resolves {inner outer : Approximation.TailBudget}
    (refines : Approximation.TailBudget.Refines inner outer) {epsilon : Fraction.Rational}
    (outerResolves : outer.Resolves epsilon) : inner.Resolves epsilon :=
  refines.remainder_antitone.trans_lt outerResolves

end Refines

end TailBudget

set_option genInjectivity false in
/-- Executable arbitrary-accuracy controller for finite nonnegative partial amounts with explicit remainder budgets. -/
structure TailProcess where
  /-- The retained type of finite tail-budget states. -/ State : Type
  /-- The certified partial amount and remainder displayed at each state. -/ budget : State → Approximation.TailBudget
  /-- The distinguished initial tail-budget state. -/ initial : State
  /-- Refine the supplied state to meet a positive rational tail request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- The request conserves the original remainder while consuming a nonnegative amount. -/ request_refines : ∀ state
    epsilon positive,
    Approximation.TailBudget.Refines (budget (request state epsilon positive)) (budget state)
  /-- The requested state has retained remainder strictly below the supplied tolerance. -/ accurate : ∀ state epsilon
    positive,
    (budget (request state epsilon positive)).Resolves epsilon
  /-- Every displayed tail budget refines the original initial budget. -/ refinesInitial : ∀ state,
    Approximation.TailBudget.Refines (budget state) (budget initial)

constructive_injectivity TailProcess

namespace TailProcess

/-- Forget partial-sum syntax only after retaining its finite rational enclosure. -/
def toBoundProcess (process : Approximation.TailProcess) : Approximation.BoundProcess where
  State := process.State
  bound state := (process.budget state).bound
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).bound_refines
  accurate state epsilon positive :=
    TailBudget.bound_width_lt (process.accurate state epsilon positive)
  refinesInitial state := (process.refinesInitial state).bound_refines

/-- A tail request cannot decrease the displayed partial amount. -/
theorem request_amount_mono (process : Approximation.TailProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (process.budget state).amount ≤
      (process.budget (process.request state epsilon positive)).amount :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

/-- A tail request cannot increase the retained remainder. -/
theorem request_remainder_antitone (process : Approximation.TailProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (process.budget (process.request state epsilon positive)).remainder ≤
      (process.budget state).remainder :=
  (process.request_refines state epsilon positive).remainder_antitone

/-- The enclosure after a tail request has width strictly below its positive tolerance. -/
theorem request_bound_width_lt (process : Approximation.TailProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (process.budget (process.request state epsilon positive)).bound.width <
      epsilon :=
  TailBudget.bound_width_lt (process.accurate state epsilon positive)

end TailProcess

end Purelib.Approximation

end
