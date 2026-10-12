module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
import Purelib.Data.CCL.Encoding.Padding.Process
public import Purelib.Data.CCL.Transducer.Contraction.Transition
import Purelib.Data.CCL.Transducer.Emission.Residual
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Transducer.Contraction.Loop
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Projective
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Approximation.Gaussian.Process.Normalization.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Transducer.Emission.Basic

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

namespace Purelib.Data.CCL.Transducer.Contraction.Residual

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- The exact apart residual refinement and normalized inverse preserve the projective parser tail.

Recover the possible residual from that same inverse process and refined base state. Persistence returns it to the
original residual mode, retaining the original count and projective chart identity. -/
theorem residualApart_neutralTransition
    (current : Mode.Basic.ResidualState)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (current.process.ball
        (Padding.Process.residualState
          current.process current.state (current.count + 1)))) :
    Contraction.Transition.NeutralTransition (.residual current)
      (.loop (Emission.Residual.residualApartLoopState current certificate)) := by
  intro tail possible
  simp only [Mode.Semantics.SemanticMode.possible] at possible
  let refined := Padding.Process.residualState
    current.process current.state (current.count + 1)
  have inversePossible :
      (Process.Gamma.Inverse.Scale.normalizedInverseProcess current.process refined certificate
        current.count).Possible
          (Process.Gamma.Inverse.Scale.normalizedInverseInitial current.process refined certificate
            current.count) tail := by
    exact possible
  rcases Process.Gamma.Inverse.Projective.normalizedInverse_tail_equivalent current.process refined
      certificate current.count inversePossible with
    ⟨residual, residualAtRefined, chartEquivalent⟩
  have residualAtCurrent :
      current.process.Possible current.state residual :=
    current.process.refine_persists current.state _ _ residualAtRefined
  refine ⟨residual, residualAtCurrent, ?_⟩
  have chartEquivalent' :
      (Mode.Semantics.SemanticMode.parserTail
        (.loop (Emission.Residual.residualApartLoopState current certificate)) tail).Equivalent
        (Mode.Semantics.SemanticMode.parserTail (.residual current) residual) := by
    simpa only [Mode.Semantics.SemanticMode.parserTail, Emission.Residual.residualApartLoopState] using
      chartEquivalent
  exact chartEquivalent'.symm

open Purelib.Data.CCL.Transducer in
open Purelib.Geometry.Projective in
/-- Every residual emission is neutral or contracts through an exact retained safe block.

Small residual padding preserves the same tail. The apart branch composes its neutral inverse-chart transition with the
accounted loop emission built from that exact refinement. -/
theorem residualStep_accounted (current :
  Mode.Basic.ResidualState) :
    Contraction.Transition.AccountedStep (.residual current) (Emission.Step.step (.residual current)).next := by
  change Contraction.Transition.AccountedStep (.residual current) (Emission.Residual.residualStep current).next
  generalize hStep : Emission.Residual.residualStep current = emission
  unfold Contraction.Transition.AccountedStep
  unfold Emission.Residual.residualStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    apply Or.inl
    intro residual possible
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    have previousPossible :
        current.process.Possible current.state residual :=
      current.process.refine_persists current.state _ _ possible
    exact ⟨residual, previousPossible, Line.Proj.Equivalent.refl _⟩
  · rename_i certificate selected
    cases hStep
    let next := Emission.Residual.residualApartLoopState current certificate
    have bridge : Contraction.Transition.NeutralTransition (.residual current) (.loop next) := by
      exact residualApart_neutralTransition current certificate
    rcases Contraction.Loop.loopStep_accounted next with neutral | ⟨entry, contracting⟩
    · exact Or.inl (Contraction.Transition.NeutralTransition.trans bridge neutral)
    · exact Or.inr
        ⟨entry, Contraction.Transition.NeutralTransition.thenContracting bridge contracting⟩
end Purelib.Data.CCL.Transducer.Contraction.Residual

end
