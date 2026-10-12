module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Quotient.State
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude

open Purelib.Approximation.Gaussian.Logarithm.Quotient (Client State)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Name

section
public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.Run

/-! ## Caller-bounded execution -/

/-- The reason a finite logarithm-quotient scheduler run stopped. -/
inductive RunKind
  /-- The scheduler has a certified quotient output. -/ | ready
  /-- The scheduler requires typed evidence for a retained child. -/ | blocked
  /-- The supplied finite scheduler budget is exhausted. -/ | exhausted
  deriving DecidableEq

set_option genInjectivity false in
/-- The certified output, typed requirement or exhaustion evidence indexed by the retained scheduler state and stop
kind. -/
inductive RunPayload (client :
    Client) (state :
  State client) :
    RunKind → Type 2
  /-- Retain the ordinary coherent quotient output and its readiness certificate. -/ | ready (output :
    Coherent.CoherentNamed) (valid : Approximation.Gaussian.Logarithm.Quotient.Ready client output) :
      RunPayload client state .ready
  /-- Retain the exact child requirement and equality to the terminal scheduler state. -/ | blocked (request :
    Requirement.Blocked client) (retained : request.state = state) :
      RunPayload client state .blocked
  /-- Record budget exhaustion without asserting readiness or exclusion. -/ | exhausted :
    RunPayload client state .exhausted

constructive_injectivity RunPayload

set_option genInjectivity false in
/-- A bounded run retains one current dependency-tree state and finite reachability from its start. -/
structure RunResult (client :
    Client) (start :
  State client) : Type 2 where
  /-- The retained reason for stopping the finite scheduler run. -/ kind :
    RunKind
  /-- The current dependency-tree state retained at termination. -/
  state : State client
  /-- A finite sequence of certified scheduler transitions reaches the retained state from the original start. -/
    reachable : Step.Reachable start state
  /-- The terminal evidence indexed by the retained state and stop kind. -/ payload :
    RunPayload client state kind

constructive_injectivity RunResult

/-- Retain the current dependency-tree state with an exhausted result. -/
@[expose] def exhaustedResult (client :
    Client)
  (state : State client) :
    RunResult client state where
  kind := .exhausted
  state := state
  reachable := .refl state
  payload := .exhausted

/-- Retain a certified quotient output at the current dependency-tree state. -/
@[expose] def readyResult (client :
    Client) (state :
  State client)
    (output : Coherent.CoherentNamed) (valid : Approximation.Gaussian.Logarithm.Quotient.Ready client output) :
    RunResult client state where
  kind := .ready
  state := state
  reachable := .refl state
  payload := .ready output valid

/-- Retain the typed child requirement and its equality to the current dependency-tree state. -/
@[expose] def blockedResult (client :
    Client) (state
  : State client)
    (request : Requirement.Blocked client) (retained : request.state = state) :
    RunResult client state where
  kind := .blocked
  state := state
  reachable := .refl state
  payload := .blocked request retained

/-- Prepend one certified scheduler transition while retaining the terminal state and payload. -/
@[expose] def prefixResult {client :
    Client} {start
  next : State client}
    (progress : Step.Progress client start next) (later : RunResult client
      next) :
    RunResult client start where
  kind := later.kind
  state := later.state
  reachable := .tail progress later.reachable
  payload := later.payload

/-- Structurally recursive scheduler. One unit of fuel performs at most one operation-specific child action; blocked and
ready results consume no further fuel. -/
@[expose] def attempt (client :
    Client) (state :
  State client) :
    Nat → RunResult client state
  | 0 => exhaustedResult client state
  | fuel + 1 =>
      match Step.step client state with
      | .ready output valid => readyResult client state output valid
      | .blocked request retained =>
          blockedResult client state request retained
      | .progressed next progress =>
          prefixResult progress
            (attempt client next fuel)

/-- A zero-fuel quotient attempt immediately retains its initial state as exhausted. -/
@[simp] theorem attempt_zero (client :
    Client)
  (state : State client) :
    attempt client state 0 =
      exhaustedResult client state := rfl

end Purelib.Approximation.Gaussian.Logarithm.Quotient.Run

end
