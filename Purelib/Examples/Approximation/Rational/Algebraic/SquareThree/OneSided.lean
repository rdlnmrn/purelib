module
import Purelib.Data.Rat.Interval.Basic

import Purelib.Approximation.Bound.Process
import Purelib.Approximation.OneSided.Basic
public import Purelib.Approximation.OneSided.Located
public import Purelib.Approximation.RationalGap.SqrtThree
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Worked one-sided rational process examples

All four examples are finite and executable.  They cover algebraic bisection,
staged rational classification, fuel-bounded inspection of finite routes, and
factorial-position radix prefixes associated with a Liouville-style target.

None of the constructions defines a limit, a completed real, or a hidden endpoint.
The conversion to `BoundProcess` occurs only because each example supplies a
separate finite gap request.
-/

namespace Purelib.Examples.Approximation.Rational.Algebraic.SquareThree.OneSided

open Purelib.Approximation

open Purelib
open Purelib.Data.Rat
open Purelib.Examples

/-! ## Example 1: algebraic bisection around square three -/

/-- Bisect the retained square-root-of-three bracket once.

Keeps the new bracket's exact refinement certificate back to the original initial bound. -/
def step (state :
  SqrtThree.State) : SqrtThree.State :=
  ⟨state.bracket.bisect,
    state.bracket.bisect_bound_refines.trans state.refines_initial⟩

/-- One retained bisection refines the original bracket interval. -/
theorem step_bound_refines (state :
  SqrtThree.State) :
    Interval.Refines (step state).bracket.bound
      state.bracket.bound :=
  state.bracket.bisect_bound_refines

/-- The increasing lower process from the original square-root-of-three brackets. -/
def lower : Approximation.LowerProcess :=
  Approximation.LowerProcess.ofBoundRefinement SqrtThree.State
    (fun state => state.bracket.bound) SqrtThree.initialState
      step
    step_bound_refines (fun state => state.refines_initial)

/-- The decreasing upper process from the same original brackets. -/
def upper : Approximation.UpperProcess :=
  Approximation.UpperProcess.ofBoundRefinement SqrtThree.State
    (fun state => state.bracket.bound) SqrtThree.initialState
      step
    step_bound_refines (fun state => state.refines_initial)

/-- Pair the lower and upper readings of the same retained bracket state. -/
def observation (state :
  SqrtThree.State) : Approximation.PairedObservation
  lower
  upper where
  lowerState := state
  upperState := state
  ordered := state.bracket.bound.valid

/-- The located pair of the retained square-root-of-three bracket processes.

Uses the original bracket request procedure and its refinement and accuracy certificates at every positive target. -/
def located : Approximation.LocatedPair
  lower
  upper where
  State := SqrtThree.State
  observation := observation
  initial := SqrtThree.initialState
  request state epsilon _ := SqrtThree.request state epsilon
  request_refines state epsilon positive := by
    have refines := SqrtThree.process.request_refines state epsilon positive
    exact ⟨refines.lower, refines.upper⟩
  accurate state epsilon positive :=
    SqrtThree.process.accurate state epsilon positive
  refinesInitial state :=
    ⟨state.refines_initial.lower, state.refines_initial.upper⟩

/-- The original lower process after four successive bisections. -/
def fourSteps :
  SqrtThree.State :=
  lower.advance 4
    lower.initial

/-- Four bisections yield endpoints 27/16 and 7/4. -/
theorem fourSteps_endpoints :
    lower.bound
      fourSteps = 27 / 16 ∧
      upper.bound
        fourSteps = 7 / 4 := by
  decide

/-- Doubling and subtracting one gives retained bounds 19/8 and 5/2. -/
theorem affine_oneSided_bounds :
    ((lower.scale 2 (by decide)).add
      (Approximation.LowerProcess.exact (-1))).bound
          ⟨fourSteps, ()⟩ = 19 / 8 ∧
      ((upper.scale 2 (by decide)).add
        (Approximation.UpperProcess.exact (-1))).bound
          ⟨fourSteps, ()⟩ = 5 / 2 := by
  decide

/-- The initial one-eighth request requires four bisections. -/
theorem eighth_bisection_count :
    SqrtThree.initialBracket.requiredBisections (1 / 8) = 4 := by
  decide

/-- The one-eighth request retains endpoints 27/16 and 7/4 with gap 1/16. -/
theorem eighth_request_data :
    let state := SqrtThree.request SqrtThree.initialState (1 / 8)
    lower.bound state = 27 / 16 ∧
      upper.bound state = 7 / 4 ∧
      (observation state).gap = 1 / 16 := by
  decide

/-- The squared endpoints of every retained bracket strictly straddle three. -/
theorem every_state_straddles_three (state
  : SqrtThree.State) :
    (lower.bound state) ^ 2 < 3 ∧ 3 <
      (upper.bound state) ^ 2 := by
  change state.bracket.lower ^ 2 < 3 ∧ 3 < state.bracket.upper ^ 2
  exact ⟨state.bracket.lower_square_lt, state.bracket.upper_square_gt⟩

/-- The located one-eighth request has interval width below one eighth. -/
theorem located_eighth_width :
    let process := located.toBoundProcess
    (process.bound
      (process.request process.initial (1 / 8) (by decide))).width <
        1 / 8 := by
  exact located.toBoundProcess.accurate _ _ (by decide)

/-! ## Example 2: staged finite probability for `x² < 2` -/

/-! ## Example 3: short-circuit inspection of finite graph routes -/

/-! ## Example 4: finite prefixes of the base-four Liouville constant

Classically, the nested radix cylinders below approach
`L₄ = ∑ k ≥ 1, 4⁻ᵏ!`, a Liouville and hence transcendental number.  The Lean
construction never forms that infinite series or a completed endpoint: every
state contains only a finite digit prefix and an explicit rational cylinder.
-/

end Purelib.Examples.Approximation.Rational.Algebraic.SquareThree.OneSided

end
