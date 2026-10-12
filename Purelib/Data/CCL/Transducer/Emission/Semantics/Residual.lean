module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
import Purelib.Data.CCL.Encoding.Padding.Process
import Purelib.Data.CCL.Encoding.Parser.Matrix.Chunks
import Purelib.Data.CCL.Transducer.Emission.Residual
public import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
public import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Transducer.Emission.Semantics.Loop
import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Projective
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Mode.Parser

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Residual

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The residual emission preserves the exact projective parser representation of every possible next tail.

Padding keeps the same projective residual tail. The apart branch composes the exact loop emission with its retained
normalized-inverse chart relation and the original nonsingular parser action. -/
theorem residualStep_exact (current :
  Mode.Basic.ResidualState) :
    Emission.Semantics.Basic.ExactEmission (.residual current) (Emission.Step.step (.residual current)) := by
  change Emission.Semantics.Basic.ExactEmission (.residual current) (Emission.Residual.residualStep current)
  generalize hStep : Emission.Residual.residualStep current = emission
  unfold Emission.Semantics.Basic.ExactEmission
  intro parser determinant phase tail possible
  unfold Emission.Residual.residualStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    have previousPossible :
        current.process.Possible current.state tail :=
      current.process.refine_persists current.state _ _ possible
    refine ⟨tail, previousPossible, ?_⟩
    rw [Parser.Matrix.Chunks.fold_residual_unary_matrix parser current.count phase]
    simp only [Mode.Semantics.SemanticMode.parserTail]
    exact Line.Proj.Equivalent.refl _
  · rename_i certificate decisionEqual
    cases hStep
    simp only [Mode.Semantics.SemanticMode.possible] at possible
    let requestedCount := current.count + 1
    let refined :=
      Padding.Process.residualState
        current.process current.state requestedCount
    have upperBoundAtRefined : ∀ {value : Basic.Canonical},
        current.process.Possible refined value →
          Data.Gaussian.Norm.Basic.normSq value ≤ current.upper := by
      intro value valuePossible
      exact current.upperBound
        (current.process.refine_persists current.state _ _ valuePossible)
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
    have nextPhase : parser.phase = Mode.Grammar.modeRawPhase (.loop next) := by
      simpa [Mode.Grammar.modeRawPhase, Mode.Grammar.regularRawPhase, next] using phase
    rcases Emission.Semantics.Loop.loopStep_exact next parser determinant nextPhase possible with
      ⟨inverseTail, inversePossible, loopExact⟩
    have inversePossible' :
        (Process.Gamma.Inverse.Scale.normalizedInverseProcess current.process refined certificate
          current.count).Possible
            (Process.Gamma.Inverse.Scale.normalizedInverseInitial current.process refined certificate
              current.count) inverseTail := by
      exact inversePossible
    rcases Process.Gamma.Inverse.Projective.normalizedInverse_tail_equivalent current.process refined
        certificate current.count inversePossible' with
      ⟨residual, residualAtRefined, chartEquivalent⟩
    have residualAtCurrent :
        current.process.Possible current.state residual :=
      current.process.refine_persists current.state _ _ residualAtRefined
    refine ⟨residual, residualAtCurrent, ?_⟩
    have chartEquivalent' :
        (Mode.Semantics.SemanticMode.parserTail (.loop next) inverseTail).Equivalent
          (Mode.Semantics.SemanticMode.parserTail (.residual current) residual) := by
      simpa only [Mode.Semantics.SemanticMode.parserTail, next] using chartEquivalent
    have actedChartEquivalent :=
      Line.Matrix.act_respects_equivalent parser.matrix chartEquivalent'
    exact Line.Gaussian.Proj.equivalent_trans
      loopExact actedChartEquivalent
      (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate determinant
        (Mode.Semantics.SemanticMode.parserTail_valid (.loop next) inverseTail))
      (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate determinant
        (Mode.Semantics.SemanticMode.parserTail_valid (.residual current) residual))

end Purelib.Data.CCL.Transducer.Emission.Semantics.Residual

end
