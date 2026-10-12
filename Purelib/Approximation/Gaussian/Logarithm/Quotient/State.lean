module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

open Purelib.Approximation.Gaussian.Process.Apart

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

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient

namespace State

set_option genInjectivity false in
/-- Retained state of the anchored-logarithm child. Once ready, its ordinary anchored chart and validity proof are
retained and never recomputed. -/
inductive LogSlot (client : Client) : Type 2
  /-- Retain the pending logarithm child state. -/ | searching (state : LogarithmState.State client.argument)
  /-- Cache the ready logarithm child state, anchored chart and validity certificate. -/ | ready (state :
    LogarithmState.State client.argument)
      (output : Anchored.AnchoredChart (preparedTarget state))
      (valid : Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready client.sourceInput client.argument
        client.source
        state output)

constructive_injectivity LogSlot

set_option genInjectivity false in
/-- Retained state of denominator-only apartness acquisition. -/
inductive DenominatorSlot (client : Client) : Type
  /-- Retain the pending denominator child state. -/ | searching (state :
    Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
  /-- Cache denominator apartness at the exact retained child state. -/ | ready (state :
    Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
      (evidence : Possible.PossibleApart
        (Gaussian.Process.Based.based client.denominator.name.process
          state.source))

constructive_injectivity DenominatorSlot

end State

set_option genInjectivity false in
/-- Current finite dependency tree. `cursor = false` gives the logarithm child priority when both children are still
pending; `true` gives the denominator priority. -/
structure State (client : Client) : Type 2 where
  /-- The retained searching or ready state of the logarithm child. -/ log :
    State.LogSlot client
  /-- The retained searching or ready state of the denominator child. -/ denominator :
    State.DenominatorSlot client
  /-- The scheduling priority: false for the logarithm child and true for the denominator child. -/ cursor : Bool

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity State

namespace State

/-- Start both child searches at their original states, giving the logarithm child priority. -/
@[expose] def initial (client : Client) :
  State client where
  log := .searching
    (Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState.State.initial client.argument)
  denominator := .searching
    (Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State.initial client.denominator)
  cursor := false

/-- Assemble a scheduler state with the supplied pending logarithm state and retained denominator slot. -/
@[expose] def withLogSearching {client :
  Client}
    (logState : LogarithmState.State client.argument)
    (denominator : Approximation.Gaussian.Logarithm.Quotient.State.DenominatorSlot client) (cursor : Bool) :
      State client :=
  { log := .searching logState, denominator := denominator, cursor := cursor }

/-- Assemble a scheduler state retaining the supplied ready logarithm chart, proof and denominator slot. -/
@[expose] def withLogReady {client : Client}
    (logState : LogarithmState.State client.argument)
    (output : Anchored.AnchoredChart (preparedTarget logState))
    (valid : Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready client.sourceInput client.argument
      client.source
      logState output)
    (denominator : Approximation.Gaussian.Logarithm.Quotient.State.DenominatorSlot client) (cursor : Bool) :
      State client :=
  { log := .ready logState output valid
    denominator := denominator
    cursor := cursor }

/-- Assemble a scheduler state with the supplied pending denominator state and retained logarithm slot. -/
@[expose] def withDenominatorSearching {client :
  Client}
    (log : Approximation.Gaussian.Logarithm.Quotient.State.LogSlot client)
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
    (cursor : Bool) : State client :=
  { log := log, denominator := .searching denominatorState, cursor := cursor }

/-- Assemble a scheduler state retaining the supplied denominator apartness proof and logarithm slot. -/
@[expose] def withDenominatorReady {client :
  Client}
    (log : Approximation.Gaussian.Logarithm.Quotient.State.LogSlot client)
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based client.denominator.name.process
        denominatorState.source))
    (cursor : Bool) : State client :=
  { log := log
    denominator := .ready denominatorState evidence
    cursor := cursor }

end State

namespace State

/-- Finite path of a partial child in this two-node dependency tree. -/
inductive NodePath
  /-- Identify the anchored-logarithm child. -/ | logarithm
  /-- Identify the denominator apartness child. -/ | denominator
  deriving DecidableEq

end State

end Purelib.Approximation.Gaussian.Logarithm.Quotient

end
