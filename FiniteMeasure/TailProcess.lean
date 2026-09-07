import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.OneSidedProcess
import FiniteMeasure.Tail

/-!
# Finite monotone tail processes

This is a constructive surrogate for nonnegative monotone convergence.  A
state contains a displayed partial amount and a rational remainder budget.
Finite advances conserve the old remainder between a nonnegative new amount
and the new remainder.  Arbitrary accuracy is an executable request, not a
completed sum or a theorem about an infinite sequence.
-/

namespace FiniteMeasure

namespace TailBudget

/-- A later partial amount obtained by consuming a displayed nonnegative
piece of the earlier remainder. -/
structure Refines (inner outer : TailBudget) : Type where
  added : Coordinate
  added_nonnegative : 0 ≤ added
  amount_eq : inner.amount = outer.amount + added
  remainder_eq : outer.remainder = added + inner.remainder

namespace Refines

def refl (budget : TailBudget) : Refines budget budget where
  added := 0
  added_nonnegative := le_rfl
  amount_eq := by ring1
  remainder_eq := by ring1

def trans {inner middle outer : TailBudget}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer where
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
theorem amount_mono {inner outer : TailBudget}
    (refines : Refines inner outer) : outer.amount ≤ inner.amount := by
  rw [refines.amount_eq]
  exact le_add_of_nonneg_right refines.added_nonnegative

/-- Consumed tail makes the remainder antitone. -/
theorem remainder_antitone {inner outer : TailBudget}
    (refines : Refines inner outer) : inner.remainder ≤ outer.remainder := by
  rw [refines.remainder_eq]
  exact le_add_of_nonneg_left refines.added_nonnegative

/-- A conserved finite tail advance narrows its rational total enclosure. -/
theorem bound_refines {inner outer : TailBudget}
    (refines : Refines inner outer) :
    Bound.Refines inner.bound outer.bound := by
  constructor
  · dsimp only [TailBudget.bound]
    exact refines.amount_mono
  · dsimp only [TailBudget.bound]
    rw [refines.amount_eq, refines.remainder_eq]
    exact le_of_eq (by ring1)

/-- Once a tail request is met, every conserved finite advance retains it. -/
theorem resolves {inner outer : TailBudget}
    (refines : Refines inner outer) {epsilon : Coordinate}
    (outerResolves : outer.Resolves epsilon) : inner.Resolves epsilon :=
  refines.remainder_antitone.trans_lt outerResolves

end Refines

end TailBudget

/-- Executable arbitrary-accuracy controller for finite nonnegative partial
amounts with explicit remainder budgets. -/
structure TailProcess where
  State : Type
  budget : State → TailBudget
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    TailBudget.Refines (budget (request state epsilon positive)) (budget state)
  accurate : ∀ state epsilon positive,
    (budget (request state epsilon positive)).Resolves epsilon
  refinesInitial : ∀ state, TailBudget.Refines (budget state) (budget initial)

namespace TailProcess

/-- Forget partial-sum syntax only after retaining its finite rational
enclosure. -/
def toBoundProcess (process : TailProcess) : BoundProcess where
  State := process.State
  bound state := (process.budget state).bound
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).bound_refines
  accurate state epsilon positive :=
    TailBudget.bound_width_lt (process.accurate state epsilon positive)
  refinesInitial state := (process.refinesInitial state).bound_refines

theorem request_amount_mono (process : TailProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (process.budget state).amount ≤
      (process.budget (process.request state epsilon positive)).amount :=
  (process.toBoundProcess.lowerRequestProcess epsilon positive).monotone state

theorem request_remainder_antitone (process : TailProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (process.budget (process.request state epsilon positive)).remainder ≤
      (process.budget state).remainder :=
  (process.request_refines state epsilon positive).remainder_antitone

theorem request_bound_width_lt (process : TailProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (process.budget (process.request state epsilon positive)).bound.width <
      epsilon :=
  TailBudget.bound_width_lt (process.accurate state epsilon positive)

end TailProcess

end FiniteMeasure
