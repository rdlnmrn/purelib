module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Interval.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

@[expose] public section

/-!
# Finite-request refinement protocols

The structures here retain only finite observations.  They express arbitrary
accuracy, finite satisfiability, monotone refinement, and pairwise shrinking
without constructing a stream, an intersection, or a completed value.
-/

namespace Purelib.Approximation
namespace Observation
namespace Refines
end Refines
namespace History
end History

end Observation
namespace ProgressiveObservation
end ProgressiveObservation

/-! ## Rational enclosure processes -/

set_option genInjectivity false in
/-- Finite-request rational bounds, useful for measures, integrals, and tail budgets. Coherence is expressed by endpoint
refinement, not by a completed rational or real value. -/
structure BoundProcess where
  /-- The finite-observation state type retained by this process. -/ State : Type
  /-- The certified rational interval displayed at each state. -/ bound : State → Rat.Interval
  /-- The distinguished initial state. -/ initial : State
  /-- Refine a supplied state to meet a positive rational width request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- A requested interval refines the exact input state's interval. -/ request_refines : ∀ state epsilon positive,
    Interval.Refines (bound (request state epsilon positive)) (bound state)
  /-- The requested interval has width strictly below the supplied tolerance. -/ accurate : ∀ state epsilon positive,
    (bound (request state epsilon positive)).width < epsilon
  /-- Every displayed state interval refines the initial interval. -/ refinesInitial : ∀ state, Interval.Refines (bound
    state) (bound initial)

constructive_injectivity BoundProcess

namespace BoundProcess

/-- Constant exact rational process, useful as a terminal finite name. -/
def exact (value : Fraction.Rational) : Approximation.BoundProcess where
  State := Unit
  bound _ := Interval.exact value
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive := Refines.refl _
  accurate state epsilon positive := by
    simpa only [Interval.exact_width] using positive
  refinesInitial state := Refines.refl _

/-- Additive inverse of a finite rational enclosure process. -/
def neg (process : Approximation.BoundProcess) : Approximation.BoundProcess
  where
  State := process.State
  bound state := (process.bound state).neg
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).neg
  accurate state epsilon positive := by
    rw [Interval.neg_width]
    exact process.accurate state epsilon positive
  refinesInitial state := (process.refinesInitial state).neg

/-- Sum of two finite rational enclosure processes. Each request allocates half of its tolerance to each operand. -/
def add (left right : Approximation.BoundProcess) : Approximation.BoundProcess
  where
  State := left.State × right.State
  bound state := (left.bound state.1).add (right.bound state.2)
  initial := ⟨left.initial, right.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := Fraction.Order.Field.div_pos_direct positive
      (by decide : (0 : Fraction.Rational) < 2)
    ⟨left.request state.1 half halfPositive,
      right.request state.2 half halfPositive⟩
  request_refines state epsilon positive :=
    Refines.add
      (left.request_refines state.1 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
      (right.request_refines state.2 (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
  accurate state epsilon positive := by
    rw [Interval.add_width]
    have halfPositive : (0 : Fraction.Rational) < epsilon / 2 :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    have leftSmall := left.accurate state.1 (epsilon / 2) halfPositive
    have rightSmall := right.accurate state.2 (epsilon / 2) halfPositive
    calc
      (left.bound (left.request state.1 (epsilon / 2) halfPositive)).width +
          (right.bound
            (right.request state.2 (epsilon / 2) halfPositive)).width <
          epsilon / 2 + epsilon / 2 :=
        Fraction.Order.Arithmetic.add_lt_add_direct leftSmall rightSmall
      _ = epsilon := by
        calc
          epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
          _ = epsilon :=
            Fraction.Field.div_mul_cancel_of_ne epsilon 2
              (by decide)
  refinesInitial state :=
    Refines.add (left.refinesInitial state.1)
      (right.refinesInitial state.2)

/-- Difference of two finite rational enclosure processes. -/
def sub (left right : Approximation.BoundProcess) : Approximation.BoundProcess
  :=
  left.add right.neg

/-- Positive rational scaling of a finite enclosure process. -/
def scalePositive (process : Approximation.BoundProcess) (factor :
  Fraction.Rational)
    (positive : 0 < factor) : Approximation.BoundProcess where
  State := process.State
  bound state := (process.bound state).scale factor positive.le
  initial := process.initial
  request state epsilon epsilonPositive :=
    process.request state (epsilon / factor)
      (Fraction.Order.Field.div_pos_direct epsilonPositive positive)
  request_refines state epsilon epsilonPositive :=
    Refines.scale factor positive.le
      (process.request_refines state (epsilon / factor)
        (Fraction.Order.Field.div_pos_direct epsilonPositive positive))
  accurate state epsilon epsilonPositive := by
    rw [Interval.scale_width]
    have requestPositive : (0 : Fraction.Rational) < epsilon / factor :=
      Fraction.Order.Field.div_pos_direct epsilonPositive positive
    have small := process.accurate state (epsilon / factor) requestPositive
    have scaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive small
    calc
      factor *
          (process.bound
            (process.request state (epsilon / factor) requestPositive)).width <
          factor * (epsilon / factor) := scaled
      _ = epsilon := by
        calc
          factor * (epsilon / factor) = (epsilon / factor) * factor := by ring1
          _ = epsilon :=
            Fraction.Field.div_mul_cancel_of_ne epsilon factor
              positive.ne'
  refinesInitial state :=
    Refines.scale factor positive.le (process.refinesInitial state)

/-- Each requested enclosure refines the initial enclosure. -/
theorem request_refines_initial (process : Approximation.BoundProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Interval.Refines
      (process.bound (process.request state epsilon positive))
      (process.bound process.initial) :=
  (process.request_refines state epsilon positive).trans
    (process.refinesInitial state)

/-- Any two explicitly supplied rational values admitted by the same finite request differ by less than the requested
tolerance in both directions. -/
theorem request_pairwise_difference_lt (process : Approximation.BoundProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {left right : Fraction.Rational}
    (leftInside :
      (process.bound (process.request state epsilon positive)).Contains left)
    (rightInside :
      (process.bound (process.request state epsilon positive)).Contains right) :
    left - right < epsilon ∧ right - left < epsilon := by
  have pairwise := Interval.pairwise_difference_le leftInside rightInside
  exact ⟨pairwise.1.trans_lt (process.accurate state epsilon positive),
    pairwise.2.trans_lt (process.accurate state epsilon positive)⟩

/-- Execute one finite request and return its canonical rational endpoint representative. -/
def approximate (process : Approximation.BoundProcess) (state : process.State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) : Fraction.Rational :=
  (process.bound (process.request state epsilon positive)).sample

/-- The computed rational representative belongs to the requested enclosure. -/
theorem approximate_inside (process : Approximation.BoundProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (process.bound (process.request state epsilon positive)).Contains
      (process.approximate state epsilon positive) :=
  (process.bound (process.request state epsilon positive)).sample_contains

/-- Every rational still admitted by the requested finite enclosure is within the request tolerance of the computed
rational representative. -/
theorem candidate_close_to_approximate (process : Approximation.BoundProcess)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {candidate : Fraction.Rational}
    (inside :
      (process.bound (process.request state epsilon positive)).Contains
        candidate) :
    candidate - process.approximate state epsilon positive < epsilon ∧
      process.approximate state epsilon positive - candidate < epsilon :=
  process.request_pairwise_difference_lt state epsilon positive inside
    (process.approximate_inside state epsilon positive)

end BoundProcess

end Purelib.Approximation

end
