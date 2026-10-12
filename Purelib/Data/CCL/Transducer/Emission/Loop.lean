module
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Approximation.Gaussian.Process.Normalization.Decision
public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Loop

section
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Build the exact residual mode state from a retained loop state and safe sector-ball certificate.

Use the already selected refined state as the residual process base. Retain that process's initial state, zero count and
the safe-sector residual upper bound with its strict one-half comparison. -/
@[expose] public def loopSectorResidualState (current : Mode.Basic.LoopState)
    (sector : ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) : Mode.Basic.ResidualState :=
  let base := current.domain.refinedState current.state
  let nextProcess := Process.Sector.Residual.residualProcess current.process base sector
  let nextState := Process.Sector.Residual.residualInitial current.process base sector
  let upper := Process.Sector.Residual.safeResidualUpper sector (current.process.ball base)
  { process := nextProcess
    state := nextState
    count := 0
    upper := upper
    upperBound := by
      intro value possible
      exact Process.Sector.Residual.translated_based_norm_le_safeResidualUpper
        current.process base sector certificate possible
    upperStrict := Process.Sector.Residual.safeResidualUpper_lt_half certificate }

/-- The residual state built from a loop sector starts at count zero.

The retained safe-sector construction stores zero in its original count
field. Reading that field reduces directly without replacing the process,
refined state or sector certificate. -/
@[simp] public theorem loopSectorResidualState_count (current : Mode.Basic.LoopState)
    (sector : ComplexContinuedFraction.Encoding.Sector)
    (certificate : Enclosure.Sector.Safe.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) :
    (Emission.Loop.loopSectorResidualState current sector certificate).count = 0 := rfl

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- Emit the next nonempty loop chunk using the retained domain decision and refined state.

A unary decision emits one true bit and retains the corresponding scaled process at the successor count. A sector
decision emits its false separator and exact sector code, retaining the residual state built from that same decision
certificate. -/
@[expose] public def loopStep (current : Mode.Basic.LoopState) : Emission := by
  let base := current.domain.refinedState current.state
  match decision : current.domain.decide current.state with
  | .unary certificate =>
      let nextProcess := Process.Gamma.Downscale.unaryScaledProcess current.process base
      let nextState := Process.Gamma.Downscale.unaryScaledInitial current.process base
      let nextDomain := Process.Gamma.Downscale.unaryScaledLoopDomain current.process base certificate
      exact
        { bits := [true]
          nonempty := by decide
          next := .loop
            { kind := current.kind
              count := current.count + 1
              process := nextProcess
              state := nextState
              domain := nextDomain } }
  | .sector sector certificate =>
      exact
        { bits := false :: sector.code
          nonempty := by
            intro empty
            cases empty
          next := .residual
            (Emission.Loop.loopSectorResidualState current sector certificate) }

end Purelib.Data.CCL.Transducer.Emission.Loop
