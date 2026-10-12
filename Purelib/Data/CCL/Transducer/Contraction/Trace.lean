module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Safe.Projective
import Purelib.Data.CCL.Encoding.Cylinder.Safe.Projective.Transport
public import Purelib.Data.CCL.Transducer.Contraction.Transition
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

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

namespace Purelib.Data.CCL.Transducer.Contraction

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- Retain a finite chain of neutral and safe-block transitions between exact transducer modes.

Neutral steps preserve the retained block list. Each contracting step prepends its exact block and certificate; the
remaining trace starts at that same intermediate mode. -/
inductive Trace : Mode → Mode → List
  Encoding.Block.Redundant → Prop where
  /-- The empty trace keeps the same exact mode and has no retained blocks. -/ | done (mode : Mode) :
    Trace mode mode []
  /-- Prepend a neutral transition at the exact intermediate mode without changing the retained block list. -/ | neutral
    {before middle after : Mode} {blocks : List Encoding.Block.Redundant}
      (transition : Contraction.Transition.NeutralTransition before middle)
      (rest : Trace middle after blocks) :
      Trace before after blocks
  /-- Prepend a contracting transition and its exact safe block to the remaining trace. -/ | sector {before middle after
    : Mode} {blocks : List Encoding.Block.Redundant}
      (entry : Encoding.Block.Redundant)
      (transition : Contraction.Transition.ContractingTransition before middle entry)
      (rest : Trace middle after blocks) :
      Trace before after (entry :: blocks)

namespace Trace

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Pull every possible final tail back to a possible initial tail realizing the exact retained safe-block list. -/
theorem realizes {before after : Mode} {blocks :
  List Encoding.Block.Redundant}
    (trace : Trace before after blocks) {tail : Basic.Canonical}
    (possible : Mode.Semantics.SemanticMode.possible after tail) :
    ∃ previous : Basic.Canonical,
      Mode.Semantics.SemanticMode.possible before previous ∧
        Cylinder.Safe.Projective.ProjectiveRealizes blocks
          (Mode.Semantics.SemanticMode.parserTail before previous) := by
  induction trace with
  | done mode =>
      exact ⟨tail, possible,
        .done _ (Mode.Semantics.SemanticMode.parserTail_valid mode tail)⟩
  | @neutral before middle after blocks transition rest inductionHypothesis =>
      rcases inductionHypothesis possible with
        ⟨middleValue, middlePossible, middleRealizes⟩
      rcases transition middlePossible with
        ⟨previous, previousPossible, equivalent⟩
      exact ⟨previous, previousPossible,
        Cylinder.Safe.Projective.ProjectiveRealizes.ofEquivalent
          (Mode.Semantics.SemanticMode.parserTail_valid before previous)
          equivalent middleRealizes⟩
  | @sector before middle after blocks entry transition rest
      inductionHypothesis =>
      rcases inductionHypothesis possible with
        ⟨middleValue, middlePossible, middleRealizes⟩
      rcases transition middlePossible with
        ⟨previous, previousPossible, blockTail, outputEquivalent,
          tailEquivalent⟩
      exact ⟨previous, previousPossible,
        .step entry blockTail
          (Mode.Semantics.SemanticMode.parserTail_valid before previous)
          outputEquivalent tailEquivalent middleRealizes⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A trace with n retained safe blocks bounds the squared chordal distance of two pulled-back initial tails by one-half
to n. -/
theorem pair_chordalSq_le_half_pow
    {before after : Mode} {blocks : List Encoding.Block.Redundant}
    (trace : Trace before after blocks)
    {leftTail rightTail : Basic.Canonical}
    (leftPossible : Mode.Semantics.SemanticMode.possible after leftTail)
    (rightPossible : Mode.Semantics.SemanticMode.possible after rightTail) :
    ∃ leftPrevious : Basic.Canonical,
      Mode.Semantics.SemanticMode.possible before leftPrevious ∧
        ∃ rightPrevious : Basic.Canonical,
          Mode.Semantics.SemanticMode.possible before rightPrevious ∧
            Chordal.Basic.chordalSq
                (Mode.Semantics.SemanticMode.parserTail before leftPrevious)
                (Mode.Semantics.SemanticMode.parserTail before rightPrevious) ≤
              (1 / 2 : Fraction.Rational) ^ blocks.length := by
  rcases trace.realizes leftPossible with
    ⟨leftPrevious, leftPreviousPossible, leftRealizes⟩
  rcases trace.realizes rightPossible with
    ⟨rightPrevious, rightPreviousPossible, rightRealizes⟩
  exact ⟨leftPrevious, leftPreviousPossible,
    rightPrevious, rightPreviousPossible,
    Cylinder.Safe.Projective.ProjectiveRealizes.chordalSq_le_half_pow
      leftRealizes rightRealizes⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Applying a nonsingular retained matrix multiplies the trace's chordal contraction bound by its exact transport
coefficient. -/
theorem pair_chordalSq_act_le_transportCoefficient_half_pow
    {before after : Mode} {blocks : List Encoding.Block.Redundant}
    (trace : Trace before after blocks)
    (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant matrix ≠ 0)
    {leftTail rightTail : Basic.Canonical}
    (leftPossible : Mode.Semantics.SemanticMode.possible after leftTail)
    (rightPossible : Mode.Semantics.SemanticMode.possible after rightTail) :
    ∃ leftPrevious : Basic.Canonical,
      Mode.Semantics.SemanticMode.possible before leftPrevious ∧
        ∃ rightPrevious : Basic.Canonical,
          Mode.Semantics.SemanticMode.possible before rightPrevious ∧
            Chordal.Basic.chordalSq
                (Line.Matrix.act matrix
                  (Mode.Semantics.SemanticMode.parserTail before leftPrevious))
                (Line.Matrix.act matrix
                  (Mode.Semantics.SemanticMode.parserTail before rightPrevious)) ≤
              Chordal.Transport.transportCoefficient matrix *
                (1 / 2 : Fraction.Rational) ^ blocks.length := by
  rcases trace.realizes leftPossible with
    ⟨leftPrevious, leftPreviousPossible, leftRealizes⟩
  rcases trace.realizes rightPossible with
    ⟨rightPrevious, rightPreviousPossible, rightRealizes⟩
  exact ⟨leftPrevious, leftPreviousPossible,
    rightPrevious, rightPreviousPossible,
    Cylinder.Safe.Projective.Transport.chordalSq_act_projectiveRealizes_le_transportCoefficient_half_pow
        matrix determinantNonzero leftRealizes rightRealizes⟩

end Trace
end Purelib.Data.CCL.Transducer.Contraction

end
