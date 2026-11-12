module
import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Observation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
import Purelib.Data.CCL.Encoding.Padding.Process
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Emission.Low
import Purelib.Data.CCL.Transducer.Emission.Residual
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Data.CCL.Encoding.Parser.Syntax.Chunks
public import Purelib.Data.CCL.Transducer.Emission.Grammar.Basic
import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
import Purelib.Data.CCL.Transducer.Emission.Low.Preparation
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Grammar of transducer emission chunks

Every selected emission advances the syntax phase to the phase of its retained next mode.
The certificates follow the same unary, sector and residual branches as the emission procedures.
-/

public section

namespace Purelib.Data.CCL.Transducer.Emission.Grammar.Step

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian

/-- Every certified loop chunk advances the parser phase to its retained next mode.

A unary chunk increments the same regular count. A separator and the selected sector code complete that block and enter
loop-unary count zero. -/
theorem loopStep_follows (current : Mode.Basic.LoopState) :
    Emission.Grammar.Basic.EmissionFollows (.loop current) (Emission.Loop.loopStep current) := by
  unfold Emission.Grammar.Basic.EmissionFollows
  rewrite [Emission.Loop.loopStep_eq]
  split
  · change Parser.Syntax.Phase.consume
        (Mode.Grammar.regularRawPhase current.kind current.count) [true] =
          Mode.Grammar.regularRawPhase current.kind (current.count + 1)
    exact Emission.Grammar.Basic.consume_regular_unary current.kind current.count
  · rename_i sector certificate decision
    change Parser.Syntax.Phase.consume
        (Mode.Grammar.regularRawPhase current.kind current.count)
        (false :: sector.code) = .loopUnary 0
    exact Emission.Grammar.Basic.consume_regular_sector current.kind current.count sector

/-- Every transducer emission advances the exact raw parser phase to its retained next mode.

The proof follows the original initial, low, loop and residual decisions, including the apart residual bridge to the
same normalized-inverse loop state. -/
theorem step_follows (mode : Mode) : Emission.Grammar.Basic.EmissionFollows mode (Emission.Step.step mode) :=
  by
  cases mode with
  | initial current =>
      let route : Process.Route current.process current.process := .input
      let receipt := route.refine current.state Emission.Initial.Budget.initialRadiusSq
        Emission.Initial.Budget.initialRadiusSq_pos
      have accurate : (current.process.ball receipt.state).radiusSq < Emission.Initial.Budget.initialRadiusSq :=
        receipt.stateEq.symm ▸ current.process.accurate current.state
          Emission.Initial.Budget.initialRadiusSq Emission.Initial.Budget.initialRadiusSq_pos
      have fine := receipt.observation.ballEq.symm ▸ accurate
      let selected := Emission.Initial.Selection.decide receipt.observation.ball
        (fine.trans Emission.Initial.Budget.initialRadiusSq_lt_uniform)
      change Emission.Grammar.Basic.EmissionFollows (.initial current)
        (selected.emission current receipt.state receipt.observation accurate)
      unfold Emission.Grammar.Basic.EmissionFollows
      cases selected with
      | low small => exact Parser.Syntax.Chunks.consume_initial_low_unary
      | high decision =>
          cases decision with
          | unary certificate => rfl
          | sector sector certificate => exact Parser.Syntax.Chunks.consume_initial_low_sector sector
  | low current =>
      let route : Process.Route current.process current.process := .input
      let receipt := route.refine current.state Emission.Initial.Budget.initialRadiusSq
        Emission.Initial.Budget.initialRadiusSq_pos
      have accurate : (current.process.ball receipt.state).radiusSq < Emission.Initial.Budget.initialRadiusSq :=
        receipt.stateEq.symm ▸ current.process.accurate current.state
          Emission.Initial.Budget.initialRadiusSq Emission.Initial.Budget.initialRadiusSq_pos
      have upper : Norm.Basic.normSq (current.process.ball receipt.state).center < 13 / 6 :=
        receipt.stateEq.symm ▸ Emission.Low.Preparation.low_center_lt_extended_upper current
      have fine := receipt.observation.ballEq.symm ▸ accurate
      have cachedUpper := receipt.observation.ballEq.symm ▸ upper
      let selected := Emission.Low.Selection.decide receipt.observation.ball cachedUpper
        (fine.trans Emission.Initial.Budget.initialRadiusSq_lt_uniform)
      change Emission.Grammar.Basic.EmissionFollows (.low current)
        (selected.emission current receipt.state receipt.observation accurate)
      unfold Emission.Grammar.Basic.EmissionFollows
      cases selected with
      | low small => exact Parser.Syntax.Chunks.consume_low_unary current.count
      | sector chosen certificate => exact Parser.Syntax.Chunks.consume_low_sector current.count chosen
  | loop current => exact loopStep_follows current
  | residual current =>
      change Emission.Grammar.Basic.EmissionFollows (.residual current) (Emission.Residual.residualStep current)
      unfold Emission.Grammar.Basic.EmissionFollows
      rewrite [Emission.Residual.residualStep_eq]
      dsimp only
      split
      · exact Parser.Syntax.Chunks.consume_residual_unary current.count
      · rename_i certificate decision
        let requestedCount := current.count + 1
        let refined :=
          Padding.Process.residualState
            current.process current.state requestedCount
        have upperBoundAtRefined : ∀
            {value : Basic.Canonical},
            current.process.Possible refined value →
              Gaussian.Norm.Basic.normSq value ≤
                current.upper := by
          intro value possible
          exact current.upperBound
            (current.process.refine_persists current.state _ _ possible)
        let nextProcess := Process.Gamma.Inverse.Scale.normalizedInverseProcess current.process refined
          certificate current.count
        let nextState := Process.Gamma.Inverse.Scale.normalizedInverseInitial current.process refined
          certificate current.count
        let nextDomain := Process.Gamma.Inverse.Scale.normalizedInverseLoopDomain current.process refined
          certificate current.count current.upper upperBoundAtRefined
          current.upperStrict
        let next : Mode.Basic.LoopState :=
          { kind := .loop
            count := current.count
            process := nextProcess
            state := nextState
            domain := nextDomain }
        change Parser.Syntax.Phase.consume (.loopUnary current.count)
            (Emission.Loop.loopStep next).bits = Mode.Grammar.modeRawPhase (Emission.Loop.loopStep next).next
        exact loopStep_follows next

end Purelib.Data.CCL.Transducer.Emission.Grammar.Step
