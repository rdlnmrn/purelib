module

public import Purelib.Data.CCL.Transducer.Mode.Semantics
public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

/-!
# Cached observations of retained productive modes

The observation keeps the original mode's process and dependent state. Its
ball and possible witness are read once through that same process interface.
Transport across an unchanged mode reuses the exact retained observation.
-/

public section

namespace Purelib.Data.CCL.Transducer.Mode

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Semantics

/-- Read the original Gaussian process retained by a productive mode. -/
@[expose] def process : Mode → Process
  | .initial current => current.process
  | .low current => current.process
  | .loop current => current.process
  | .residual current => current.process

/-- Read the original dependent state of the process retained by the same mode. -/
@[expose] def state : (mode : Mode) → mode.process.State
  | .initial current => current.state
  | .low current => current.state
  | .loop current => current.state
  | .residual current => current.state

/-- The original process observation at the mode's exact retained dependent state. -/
abbrev Observation (mode : Mode) := Process.Observation mode.process mode.state

namespace Observation

/-- Read and retain the original mode's ball and possible witness once. -/
@[expose] def build (mode : Mode) : Observation mode :=
  Process.Observation.build mode.process mode.state

/-- Transporting a retained observation to an equal mode preserves its actual ball. -/
theorem transport_ball (before after : Mode) (same : after = before)
    (observation : Observation before) :
    (same.symm ▸ observation).ball = observation.ball := by
  cases same
  rfl

/-- The cached witness belongs to the original same mode possibility predicate. -/
theorem possible {mode : Mode} (observation : Observation mode) :
    SemanticMode.possible mode observation.witness.val := by
  cases mode with
  | initial current | low current | loop current | residual current => exact observation.witness.property

/-- Read the cached original witness with its same mode possibility evidence. -/
@[expose] def candidate {mode : Mode} (observation : Observation mode) :
    { value : Basic.Canonical // SemanticMode.possible mode value } :=
  ⟨observation.witness.val, observation.possible⟩

/-- The retained mode witness is the exact original process witness at that state. -/
theorem candidate_eq {mode : Mode} (observation : Observation mode) :
    observation.candidate = SemanticMode.witness mode := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact observation.witnessEq

end Observation

namespace Basic.ResidualState

open Purelib.Data.ComplexContinuedFraction.Encoding (Sector)

/-- Construct the original zero-count residual state from the same cached source observation and selected sector.

The retained process and dependent base are the original sector translation.
Its strict upper quadrance is computed from the cached ball; the bounds and
next state perform no source refinement, ball read or witness read.
-/
@[expose] def ofObservation (source : Process) (base : source.State) (sector : Sector)
    (observation : Process.Observation source base)
    (certificate : Enclosure.Sector.Safe.SafeBall sector observation.ball) : ResidualState :=
  let original : Enclosure.Sector.Safe.SafeBall sector (source.ball base) := observation.ballEq ▸ certificate
  let upper := Process.Sector.Residual.safeResidualUpper sector observation.ball
  let upperEq := congrArg (Process.Sector.Residual.safeResidualUpper sector) observation.ballEq
  { process := Process.Sector.Residual.residualProcess source base sector
    state := Process.Sector.Residual.residualInitial source base sector
    count := 0
    upper := upper
    upperBound := by
      intro value possible
      change Norm.Basic.normSq value ≤ Process.Sector.Residual.safeResidualUpper sector observation.ball
      exact upperEq.symm ▸ Process.Sector.Residual.translated_based_norm_le_safeResidualUpper
        source base sector original possible
    upperStrict := Process.Sector.Residual.safeResidualUpper_lt_half certificate }

end Basic.ResidualState

end Purelib.Data.CCL.Transducer.Mode
