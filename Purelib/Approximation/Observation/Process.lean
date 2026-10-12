module

import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.Observation.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

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

set_option genInjectivity false in
/-- An executable arbitrary-accuracy name whose results remain finite observations. -/
structure ProgressiveObservation (α : Type)
    (distance : α → α → Fraction.Rational) where
  /-- The retained state type of finite observations. -/ State : Type
  /-- The certified finite observation displayed at each state. -/ observation : State → Approximation.Observation α
    distance
  /-- The distinguished initial observation state. -/ initial : State
  /-- Refine a supplied state to meet a positive rational spread request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- A requested observation refines the supplied observation. -/ request_refines : ∀ state epsilon positive,
    Observation.Refines
      (observation (request state epsilon positive)) (observation state)
  /-- The requested observation has spread strictly below the supplied tolerance. -/ accurate : ∀ state epsilon
    positive,
    (observation (request state epsilon positive)).spread < epsilon
  /-- Every state observation refines the initial observation. -/ refinesInitial : ∀ state,
    Observation.Refines (observation state) (observation initial)

constructive_injectivity ProgressiveObservation

namespace ProgressiveObservation

/-- Every two candidates at a requested finite precision meet the displayed distance request. -/
theorem request_pairwise
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance)
    (state : name.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {left right : α}
    (leftPossible :
      (name.observation (name.request state epsilon positive)).Possible left)
    (rightPossible :
      (name.observation (name.request state epsilon positive)).Possible right) :
    distance left right < epsilon :=
  (name.observation (name.request state epsilon positive)).pairwise
    leftPossible rightPossible |>.trans_lt
      (name.accurate state epsilon positive)

/-- One request extends any already displayed finite history. -/
def requestHistory
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance)
    {latest : name.State}
    (history : Observation.History
      (name.observation name.initial) (name.observation latest))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Observation.History (name.observation name.initial)
      (name.observation (name.request latest epsilon positive)) :=
  .step history (name.request_refines latest epsilon positive)

/-- The witness produced after a finite request remains a candidate at the displayed initial observation. -/
theorem request_witness_possible_initial
    {α : Type} {distance : α → α → Fraction.Rational}
    (name : Approximation.ProgressiveObservation α distance)
    (state : name.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (name.observation name.initial).Possible
      (name.observation (name.request state epsilon positive)).witness :=
  (name.request_refines state epsilon positive).trans
    (name.refinesInitial state) |>.witness_possible

end ProgressiveObservation
namespace BoundProcess
end BoundProcess

end Purelib.Approximation

end
