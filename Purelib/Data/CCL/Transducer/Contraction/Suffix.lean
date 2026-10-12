module
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Transducer.Contraction.Loop
import Purelib.Data.CCL.Transducer.Contraction.Residual
public import Purelib.Data.CCL.Transducer.Contraction.Trace
import Purelib.Data.CCL.Transducer.Contraction.Transition
import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Emission.Residual
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.CCL.Encoding.Padding.Process
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Approximation.Gaussian.Process.Normalization.Decision
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision

section
@[expose] public section

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace Purelib.Data.CCL.Transducer.Contraction.Suffix

section
open Purelib.Data.CCL.Transducer
/-- Require the exact transducer mode to be in its loop or residual suffix phase. -/
inductive SuffixMode : Data.CCL.Transducer.Mode → Prop where
  /-- The exact loop state is a suffix mode. -/ | loop (current : Mode.Basic.LoopState) :
    SuffixMode (.loop current)
  /-- The exact residual state is a suffix mode. -/ | residual (current : Mode.Basic.ResidualState) :
    SuffixMode (.residual current)

/-- The next mode of every loop emission remains a loop-or-residual suffix mode. -/
theorem loopStep_next_suffix (current : Mode.Basic.LoopState) :
    SuffixMode (Emission.Loop.loopStep current).next := by
  unfold Emission.Loop.loopStep
  split
  · exact .loop _
  · exact .residual _

/-- The next mode of every residual emission remains a loop-or-residual suffix mode. -/
theorem residualStep_next_suffix (current :
  Mode.Basic.ResidualState) :
    SuffixMode (Emission.Step.step (.residual current)).next := by
  change SuffixMode (Emission.Residual.residualStep current).next
  simp only [Emission.Residual.residualStep]
  split
  · exact .residual _
  · exact loopStep_next_suffix (Emission.Residual.residualApartLoopState current _)

/-- Every suffix-mode emission is neutral or contracts through one exact retained safe block. -/
theorem suffixStep_accounted {mode : Data.CCL.Transducer.Mode}
  (suffix :
  SuffixMode mode) :
    Contraction.Transition.AccountedStep mode (Emission.Step.step mode).next := by
  cases suffix with
  | loop current => exact Contraction.Loop.loopStep_accounted current
  | residual current => exact Contraction.Residual.residualStep_accounted current

/-- Every suffix-mode emission retains a suffix-mode successor. -/
theorem suffixStep_next {mode : Data.CCL.Transducer.Mode} (suffix
  :
  SuffixMode mode) :
    SuffixMode (Emission.Step.step mode).next := by
  cases suffix with
  | loop current => exact loopStep_next_suffix current
  | residual current => exact residualStep_next_suffix current

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- Construct an accounted finite trace from a retained suffix mode for any requested step count.

The recursive construction follows the exact emitted successor modes. Neutral steps keep the block list and contracting
steps retain their selected block in order; the final mode remains a suffix mode. -/
theorem exists_trace (mode : Data.CCL.Transducer.Mode) (suffix :
  SuffixMode mode) :
    ∀ _count : Nat,
      ∃ after : Data.CCL.Transducer.Mode, ∃ blocks : List Data.CCL.Encoding.Block.Redundant,
        SuffixMode after ∧ Data.CCL.Transducer.Contraction.Trace mode after blocks
  | 0 => ⟨mode, [], suffix, .done mode⟩
  | count + 1 => by
      let middle := (Emission.Step.step mode).next
      have middleSuffix : SuffixMode middle := suffixStep_next suffix
      rcases exists_trace middle middleSuffix count with
        ⟨after, blocks, afterSuffix, rest⟩
      rcases suffixStep_accounted suffix with
        neutral | ⟨entry, contracting⟩
      · exact ⟨after, blocks, afterSuffix, .neutral neutral rest⟩
      · exact ⟨after, entry :: blocks, afterSuffix,
          .sector entry contracting rest⟩
end Purelib.Data.CCL.Transducer.Contraction.Suffix

end
