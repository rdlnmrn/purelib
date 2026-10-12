module
public import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Sampling

import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Name

section
section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.State.Schedule

/-- A displayed finite schedule of canonical source refinements. -/
def advanceN {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed} (state :
  Approximation.Gaussian.Acquisition.State tau) : Nat →
  Approximation.Gaussian.Acquisition.State tau
  | 0 => state
  | count + 1 => advanceN
    (Purelib.Approximation.Gaussian.Acquisition.State.advance state) count
end Purelib.Approximation.Gaussian.Acquisition.State.Schedule

end

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.State.Schedule

namespace Gap
end Gap

/-- One additional canonical refinement may be performed after the preceding finite schedule. -/
theorem advanceN_succ {tau : Coherent.CoherentNamed}
  (state : Approximation.Gaussian.Acquisition.State tau) (count : Nat) :
    advanceN state (count + 1) = State.advance
      (advanceN state count) := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      exact inductionHypothesis (State.advance state)

/-- A finite canonical refinement schedule increments the retained retry index by its exact length. -/
theorem advanceN_nextIndex {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau) (count : Nat) :
    (advanceN state count).retained.nextIndex =
      state.retained.nextIndex + count := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [advanceN, inductionHypothesis]
      change state.retained.nextIndex + 1 + count = state.retained.nextIndex + (count + 1)
      omega

/-- After a nonempty canonical schedule, the cached enclosure radius is smaller than the request at the final refinement
index. -/
theorem advanceN_accurate {tau :
  Coherent.CoherentNamed} (state : Approximation.Gaussian.Acquisition.State tau) (count : Nat) :
    (advanceN state (count + 1)).ball.radiusSq <
      Gaussian.Process.Sampling.refinementTarget (state.retained.nextIndex + count) := by
  rw [advanceN_succ]
  have accurate := tau.name.process.accurate (advanceN state
    count).retained.source
    (Gaussian.Process.Sampling.refinementTarget (advanceN state
      count).retained.nextIndex)
    (Gaussian.Process.Sampling.refinementTarget_pos (advanceN state
      count).retained.nextIndex)
  exact accurate.trans_le (le_of_eq (congrArg Gaussian.Process.Sampling.refinementTarget
    (advanceN_nextIndex state count)))
end Purelib.Approximation.Gaussian.Acquisition.State.Schedule

end

end

