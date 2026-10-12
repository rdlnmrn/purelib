module
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
public import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
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

namespace Purelib.Data.CCL.Transducer.Emission.Initial

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Emit the first certified nonempty chunk from the exact initial refinement and center decision.

A normalized center selects unary downscaling or a safe sector residual using the retained decision certificate. A
center below unit squared norm emits the low-entry pair and retains the gamma-upscaled process at count one. -/
@[expose] public def initialStep (current : Mode.Basic.InitialState) : Emission := by
  let base := Emission.Initial.Preparation.initialRefinedState current.process current.state
  have accurate := Emission.Initial.Preparation.initialRefined_accurate current.process current.state
  have uniform := Emission.Initial.Preparation.initialRefined_uniform current.process current.state
  by_cases normalized : 1 ≤ Gaussian.Norm.Basic.normSq (current.process.ball base).center
  · match decision : Enclosure.Sector.Decision.decide
        (current.process.ball base) normalized uniform with
    | .unary certificate =>
        let nextProcess := Process.Gamma.Downscale.unaryScaledProcess current.process base
        let nextState := Process.Gamma.Downscale.unaryScaledInitial current.process base
        let nextDomain := Process.Gamma.Downscale.unaryScaledLoopDomain current.process base
          certificate
        exact
          { bits := [true]
            nonempty := by decide
            next := .loop
              { kind := .initialHigh
                count := 1
                process := nextProcess
                state := nextState
                domain := nextDomain } }
    | .sector sector certificate =>
        let nextProcess := Process.Sector.Residual.residualProcess current.process base sector
        let nextState := Process.Sector.Residual.residualInitial current.process base sector
        let upper := Process.Sector.Residual.safeResidualUpper sector (current.process.ball base)
        exact
          { bits := false :: false :: sector.code
            nonempty := by
              intro empty
              cases empty
            next := .residual
              { process := nextProcess
                state := nextState
                count := 0
                upper := upper
                upperBound := by
                  intro value possible
                  exact Process.Sector.Residual.translated_based_norm_le_safeResidualUpper
                    current.process base sector certificate possible
                upperStrict := Process.Sector.Residual.safeResidualUpper_lt_half certificate } }
  · have centerSmall : Gaussian.Norm.Basic.normSq (current.process.ball base).center < 1 :=
      lt_of_not_ge normalized
    exact
      { bits := [false, true]
        nonempty := by decide
        next := .low (Emission.Low.Preparation.nextLowState current.process base accurate
          centerSmall 1) }

end Purelib.Data.CCL.Transducer.Emission.Initial
