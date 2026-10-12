module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Based

/-! ## Rebasing and exact translations -/

set_option genInjectivity false in
/-- A later source state together with a finite proof that all its candidates were already candidates of one fixed base
state. -/
structure BasedState (process : Approximation.Gaussian.Process)
  (base : process.State) where
  /-- The retained source-process state whose possibilities persist to the original base. -/ source : process.State
  /-- Every reading possible at the retained source state is possible at the original base state. -/ persists : ∀ {value
    : Data.Gaussian.Basic.Canonical},
    process.Possible source value → process.Possible base value

constructive_injectivity BasedState

namespace BasedState

/-- Use the original base state as its own based state with identity persistence. -/
def initial (process : Approximation.Gaussian.Process)
  (base : process.State) :
    Approximation.Gaussian.Process.Based.BasedState process base :=
  { source := base
    persists := fun possible => possible }

end BasedState

/-- Restrict a progressive process to the refinement future of one explicit finite base state. -/
def based (process : Approximation.Gaussian.Process) (base :
  process.State) : Approximation.Gaussian.Process where
  State := BasedState process base
  ball state := process.ball state.source
  Possible state value := process.Possible state.source value
  witness state := process.witness state.source
  possible_inside possible := process.possible_inside possible
  refine state target positive :=
    { source := process.refine state.source target positive
      persists := fun possible =>
        state.persists
          (process.refine_persists state.source target positive possible) }
  refine_persists := by
    intro state target positive value possible
    exact process.refine_persists state.source target positive possible
  accurate state target positive := process.accurate state.source target positive
  centerBound := process.centerBound
  centerBound_nonneg := process.centerBound_nonneg
  center_bounded state := process.center_bounded state.source

/-- Every possible reading of a based process remains possible at its original source base state. -/
theorem based_initial_persists (process :
  Approximation.Gaussian.Process) (base : process.State)
    {state : (based process base).State} {value : Data.Gaussian.Basic.Canonical}
    (possible : (based process base).Possible state value) :
    process.Possible base value :=
  state.persists possible
end Purelib.Approximation.Gaussian.Process.Based

end
