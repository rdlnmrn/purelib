module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data

open Purelib.Data.Rat

@[expose] public section

/-!
# One-sided rational refinement processes

These processes expose improving rational evidence without postulating a
hidden endpoint.  A lower process only promises increasing lower bounds, and
an upper process only promises decreasing upper bounds.  In particular,
neither structure contains an accuracy request or a convergence claim.

A `LocatedPair` is deliberately stronger: it supplies a finite request which
puts one lower observation and one upper observation within an explicitly
requested positive rational gap.  Only at that boundary do the observations
become an ordinary two-sided `BoundProcess`.
-/

namespace Purelib.Approximation

set_option genInjectivity false in
/-- Executable increasing rational lower evidence. Every state supplied by the process is compatible with its displayed
initial lower bound, but no rate of increase and no limiting value are part of the data. -/
structure LowerProcess where
  /-- The retained type of finite observation states. -/ State : Type
  /-- The rational bound displayed by each state. -/ bound : State → Fraction.Rational
  /-- The distinguished initial observation state. -/ initial : State
  /-- Compute one further finite observation state. -/ refine : State → State
  /-- One refinement can only increase the displayed lower bound. -/ monotone : ∀ state, bound state ≤ bound (refine
    state)
  /-- Every lower observation is at least its initial lower bound. -/ refinesInitial : ∀ state, bound initial ≤ bound
    state

constructive_injectivity LowerProcess

set_option genInjectivity false in
/-- Executable decreasing rational upper evidence. Every state supplied by the process is compatible with its displayed
initial upper bound, but no rate of decrease and no limiting value are part of the data. -/
structure UpperProcess where
  /-- The retained type of finite observation states. -/ State : Type
  /-- The rational bound displayed by each state. -/ bound : State → Fraction.Rational
  /-- The distinguished initial observation state. -/ initial : State
  /-- Compute one further finite observation state. -/ refine : State → State
  /-- One refinement can only decrease the displayed upper bound. -/ antitone : ∀ state, bound (refine state) ≤ bound
    state
  /-- Every upper observation is at most its initial upper bound. -/ refinesInitial : ∀ state, bound state ≤ bound
    initial

constructive_injectivity UpperProcess

namespace LowerProcess

/-- The newer lower observation contains at least the evidence in the older one. -/
def Refines (process : Approximation.LowerProcess)
    (newer older : process.State) : Prop :=
  process.bound older ≤ process.bound newer

namespace Refines

/-- Each state refines itself. -/
theorem refl (process : Approximation.LowerProcess) (state :
  process.State) :
    process.Refines state state :=
  le_rfl

/-- Compose two successive refinements of one-sided evidence. -/
theorem trans {process : Approximation.LowerProcess} {newest newer
  older : process.State}
    (newestNewer : process.Refines newest newer)
    (newerOlder : process.Refines newer older) :
    process.Refines newest older := by
  change process.bound older ≤ process.bound newest
  exact le_trans newerOlder newestNewer

end Refines

/-- Perform exactly the displayed finite number of lower refinements. -/
def advance (process : Purelib.Approximation.LowerProcess) : Nat →
  process.State → process.State
  | 0, state => state
  | count + 1, state => process.refine (advance process count state)

/-- Advancing zero steps returns the supplied state. -/
@[simp] theorem advance_zero (process : Approximation.LowerProcess) (state :
  process.State) :
    process.advance 0 state = state :=
  rfl

/-- Advancing a successor number of steps applies one refinement after the preceding advance. -/
theorem advance_succ (process : Approximation.LowerProcess) (count : Nat)
    (state : process.State) :
    process.advance (count + 1) state =
      process.refine (process.advance count state) :=
  rfl

/-- Any finite advance preserves or improves the original lower bound. -/
theorem bound_le_advance (process : Approximation.LowerProcess) :
    ∀ (count : Nat) (state : process.State),
      process.bound state ≤ process.bound (process.advance count state)
  | 0, _ => le_rfl
  | count + 1, state =>
      (process.bound_le_advance count state).trans
        (process.monotone (process.advance count state))

/-- Split a finite advance into two successive advances of the displayed lengths. -/
theorem advance_add (process : Approximation.LowerProcess) (left right : Nat)
    (state : process.State) :
    process.advance (left + right) state =
      process.advance right (process.advance left state) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ, Approximation.LowerProcess.advance_succ, Approximation.LowerProcess.advance_succ,
        inductionHypothesis]

/-- Later finite schedules return at least as strong a lower bound. -/
theorem advance_mono (process : Approximation.LowerProcess) {earlier later :
  Nat}
    (order : earlier ≤ later) (state : process.State) :
    process.bound (process.advance earlier state) ≤
      process.bound (process.advance later state) := by
  let extra := later - earlier
  have reconstructed : earlier + extra = later :=
    Data.Nat.Subtraction.add_sub_of_le order
  rw [← reconstructed, process.advance_add earlier extra state]
  exact process.bound_le_advance extra (process.advance earlier state)

/-- A direct common finite refinement for two lower-bound schedules. -/
def commonAdvance (process : Approximation.LowerProcess) (left right : Nat)
    (state : process.State) : process.State :=
  process.advance (max left right) state

/-- The common advance has a lower bound at least as strong as the left schedule. -/
theorem left_le_commonAdvance (process : Approximation.LowerProcess) (left
  right : Nat)
    (state : process.State) :
    process.bound (process.advance left state) ≤
      process.bound (process.commonAdvance left right state) :=
  process.advance_mono (Data.Nat.Order.le_max_left left right) state

/-- The common advance has a lower bound at least as strong as the right schedule. -/
theorem right_le_commonAdvance (process : Approximation.LowerProcess) (left
  right : Nat)
    (state : process.State) :
    process.bound (process.advance right state) ≤
      process.bound (process.commonAdvance left right state) :=
  process.advance_mono (Data.Nat.Order.le_max_right left right) state

/-- Constant exact lower evidence. -/
def exact (value : Fraction.Rational) : Approximation.LowerProcess where
  State := Unit
  bound _ := value
  initial := ()
  refine state := state
  monotone _ := le_rfl
  refinesInitial _ := le_rfl

/-- Pointwise addition of independently refinable lower evidence. -/
def add (left right : Approximation.LowerProcess) : Approximation.LowerProcess
  where
  State := left.State × right.State
  bound state := left.bound state.1 + right.bound state.2
  initial := ⟨left.initial, right.initial⟩
  refine state := ⟨left.refine state.1, right.refine state.2⟩
  monotone state := add_le_add (left.monotone state.1)
    (right.monotone state.2)
  refinesInitial state := add_le_add (left.refinesInitial state.1)
    (right.refinesInitial state.2)

/-- Scaling lower evidence by an explicitly nonnegative rational preserves its direction. -/
def scale (process : Approximation.LowerProcess) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) : Approximation.LowerProcess where
  State := process.State
  bound state := factor * process.bound state
  initial := process.initial
  refine := process.refine
  monotone state :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (process.monotone state) nonnegative
  refinesInitial state :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (process.refinesInitial state) nonnegative

/-- Negation turns lower evidence into upper evidence. -/
def neg (process : Approximation.LowerProcess) : Approximation.UpperProcess
  where
  State := process.State
  bound state := -process.bound state
  initial := process.initial
  refine := process.refine
  antitone state :=
    Fraction.Order.Arithmetic.neg_le_neg_direct (process.monotone state)
  refinesInitial state :=
    Fraction.Order.Arithmetic.neg_le_neg_direct
      (process.refinesInitial state)

/-- A finite list of lower processes can be summed without imposing a common state type or an infinite schedule. -/
def sum : List Purelib.Approximation.LowerProcess →
  Purelib.Approximation.LowerProcess
  | [] => exact 0
  | process :: remaining => process.add (sum remaining)

/-- The sum of no one-sided processes is the exact zero process. -/
@[simp] theorem sum_nil : Approximation.LowerProcess.sum [] =
  Approximation.LowerProcess.exact 0 :=
  rfl

/-- The sum of a nonempty process list adds its first process to the sum of the remainder. -/
@[simp] theorem sum_cons (process : Approximation.LowerProcess)
    (remaining : List Approximation.LowerProcess) :
    Approximation.LowerProcess.sum (process :: remaining) = process.add (Approximation.LowerProcess.sum remaining) :=
  rfl

/-- Extract lower evidence from any certified two-sided refinement step. -/
def ofBoundRefinement (State : Type) (bound : State → Rat.Interval)
    (initial : State) (refine : State → State)
    (step : ∀ state, Interval.Refines (bound (refine state)) (bound state))
    (initialRefinement : ∀ state,
      Interval.Refines (bound state) (bound initial)) : Approximation.LowerProcess where
  State := State
  bound state := (bound state).lower
  initial := initial
  refine := refine
  monotone state := (step state).lower
  refinesInitial state := (initialRefinement state).lower

end LowerProcess

namespace UpperProcess

/-- The newer upper observation contains at least the evidence in the older one. -/
def Refines (process : Approximation.UpperProcess)
    (newer older : process.State) : Prop :=
  process.bound newer ≤ process.bound older

namespace Refines

/-- Each state refines itself. -/
theorem refl (process : Approximation.UpperProcess) (state :
  process.State) :
    process.Refines state state :=
  le_rfl

/-- Compose two successive refinements of one-sided evidence. -/
theorem trans {process : Approximation.UpperProcess} {newest newer
  older : process.State}
    (newestNewer : process.Refines newest newer)
    (newerOlder : process.Refines newer older) :
    process.Refines newest older := by
  change process.bound newest ≤ process.bound older
  exact le_trans newestNewer newerOlder

end Refines

/-- Perform exactly the displayed finite number of upper refinements. -/
def advance (process : Purelib.Approximation.UpperProcess) : Nat →
  process.State → process.State
  | 0, state => state
  | count + 1, state => process.refine (advance process count state)

/-- Advancing zero steps returns the supplied state. -/
@[simp] theorem advance_zero (process : Approximation.UpperProcess) (state :
  process.State) :
    process.advance 0 state = state :=
  rfl

/-- Advancing a successor number of steps applies one refinement after the preceding advance. -/
theorem advance_succ (process : Approximation.UpperProcess) (count : Nat)
    (state : process.State) :
    process.advance (count + 1) state =
      process.refine (process.advance count state) :=
  rfl

/-- Any finite advance preserves or improves the original upper bound. -/
theorem advance_bound_le (process : Approximation.UpperProcess) :
    ∀ (count : Nat) (state : process.State),
      process.bound (process.advance count state) ≤ process.bound state
  | 0, _ => le_rfl
  | count + 1, state =>
      (process.antitone (process.advance count state)).trans
        (process.advance_bound_le count state)

/-- Split a finite advance into two successive advances of the displayed lengths. -/
theorem advance_add (process : Approximation.UpperProcess) (left right : Nat)
    (state : process.State) :
    process.advance (left + right) state =
      process.advance right (process.advance left state) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ, Approximation.UpperProcess.advance_succ, Approximation.UpperProcess.advance_succ,
        inductionHypothesis]

/-- Later finite schedules return at least as strong an upper bound. -/
theorem advance_antitone (process : Approximation.UpperProcess) {earlier later
  : Nat}
    (order : earlier ≤ later) (state : process.State) :
    process.bound (process.advance later state) ≤
      process.bound (process.advance earlier state) := by
  let extra := later - earlier
  have reconstructed : earlier + extra = later :=
    Data.Nat.Subtraction.add_sub_of_le order
  rw [← reconstructed, process.advance_add earlier extra state]
  exact process.advance_bound_le extra (process.advance earlier state)

/-- A direct common finite refinement for two upper-bound schedules. -/
def commonAdvance (process : Approximation.UpperProcess) (left right : Nat)
    (state : process.State) : process.State :=
  process.advance (max left right) state

/-- The common advance has an upper bound at least as strong as the left schedule. -/
theorem commonAdvance_le_left (process : Approximation.UpperProcess) (left
  right : Nat)
    (state : process.State) :
    process.bound (process.commonAdvance left right state) ≤
      process.bound (process.advance left state) :=
  process.advance_antitone (Data.Nat.Order.le_max_left left right) state

/-- The common advance has an upper bound at least as strong as the right schedule. -/
theorem commonAdvance_le_right (process : Approximation.UpperProcess) (left
  right : Nat)
    (state : process.State) :
    process.bound (process.commonAdvance left right state) ≤
      process.bound (process.advance right state) :=
  process.advance_antitone (Data.Nat.Order.le_max_right left right) state

/-- Constant exact upper evidence. -/
def exact (value : Fraction.Rational) : Approximation.UpperProcess where
  State := Unit
  bound _ := value
  initial := ()
  refine state := state
  antitone _ := le_rfl
  refinesInitial _ := le_rfl

/-- Pointwise addition of independently refinable upper evidence. -/
def add (left right : Approximation.UpperProcess) : Approximation.UpperProcess
  where
  State := left.State × right.State
  bound state := left.bound state.1 + right.bound state.2
  initial := ⟨left.initial, right.initial⟩
  refine state := ⟨left.refine state.1, right.refine state.2⟩
  antitone state := add_le_add (left.antitone state.1)
    (right.antitone state.2)
  refinesInitial state := add_le_add (left.refinesInitial state.1)
    (right.refinesInitial state.2)

/-- Scaling upper evidence by an explicitly nonnegative rational preserves its direction. -/
def scale (process : Approximation.UpperProcess) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) : Approximation.UpperProcess where
  State := process.State
  bound state := factor * process.bound state
  initial := process.initial
  refine := process.refine
  antitone state :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (process.antitone state) nonnegative
  refinesInitial state :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (process.refinesInitial state) nonnegative

/-- Negation turns upper evidence into lower evidence. -/
def neg (process : Approximation.UpperProcess) : Approximation.LowerProcess
  where
  State := process.State
  bound state := -process.bound state
  initial := process.initial
  refine := process.refine
  monotone state :=
    Fraction.Order.Arithmetic.neg_le_neg_direct (process.antitone state)
  refinesInitial state :=
    Fraction.Order.Arithmetic.neg_le_neg_direct
      (process.refinesInitial state)

/-- A finite list of upper processes can be summed without imposing a common state type or an infinite schedule. -/
def sum : List Purelib.Approximation.UpperProcess →
  Purelib.Approximation.UpperProcess
  | [] => exact 0
  | process :: remaining => process.add (sum remaining)

/-- The sum of no one-sided processes is the exact zero process. -/
@[simp] theorem sum_nil : Approximation.UpperProcess.sum [] =
  Approximation.UpperProcess.exact 0 :=
  rfl

/-- The sum of a nonempty process list adds its first process to the sum of the remainder. -/
@[simp] theorem sum_cons (process : Approximation.UpperProcess)
    (remaining : List Approximation.UpperProcess) :
    Approximation.UpperProcess.sum (process :: remaining) = process.add (Approximation.UpperProcess.sum remaining) :=
  rfl

/-- Extract upper evidence from any certified two-sided refinement step. -/
def ofBoundRefinement (State : Type) (bound : State → Rat.Interval)
    (initial : State) (refine : State → State)
    (step : ∀ state, Interval.Refines (bound (refine state)) (bound state))
    (initialRefinement : ∀ state,
      Interval.Refines (bound state) (bound initial)) : Approximation.UpperProcess where
  State := State
  bound state := (bound state).upper
  initial := initial
  refine := refine
  antitone state := (step state).upper
  refinesInitial state := (initialRefinement state).upper

end UpperProcess

/-! ## One-sided views of a fixed rational-bound request -/

namespace BoundProcess
end BoundProcess
namespace PairedObservation
namespace Refines
end Refines

end PairedObservation
namespace LocatedPair
end LocatedPair

end Purelib.Approximation

end
