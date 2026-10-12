module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Safe.Tail

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Geometry.Projective.Line.Basic

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

namespace Purelib.Data.CCL.Transducer.Contraction.Transition

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Require every possible later tail to have an equivalent projective tail at the retained earlier mode.

The witness belongs to the earlier mode's exact process state. The relation compares their parser-tail projective points
without inserting a block or changing either process owner. -/
def NeutralTransition (before after :
  Data.CCL.Transducer.Mode) : Prop
  :=
  ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible after tail →
    ∃ previous : Basic.Canonical,
      Mode.Semantics.SemanticMode.possible before previous ∧
        (Mode.Semantics.SemanticMode.parserTail before previous).Equivalent
          (Mode.Semantics.SemanticMode.parserTail after tail)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Require each later tail to pull back through the exact retained safe block.

Keep an earlier possible witness and a safe projective tail for this same block. The earlier parser tail equals its
block-matrix image, while the safe tail equals the later parser tail projectively. -/
def ContractingTransition (before after :
  Data.CCL.Transducer.Mode)
  (entry : Data.CCL.Encoding.Block.Redundant) : Prop :=
  ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible after tail →
    ∃ previous : Basic.Canonical,
      Mode.Semantics.SemanticMode.possible before previous ∧
        ∃ blockTail : Geometry.Projective.SectorBlock.Safe.Tail entry.sector,
          (Mode.Semantics.SemanticMode.parserTail before previous).Equivalent
              (Line.Matrix.act entry.matrix blockTail.point) ∧
            blockTail.point.Equivalent
              (Mode.Semantics.SemanticMode.parserTail after tail)

namespace NeutralTransition

open Purelib.Data.CCL.Transducer in
open Purelib.Geometry.Projective in
/-- Compose neutral transitions through their exact retained middle mode and possible witness. -/
theorem trans {before middle after :
  Data.CCL.Transducer.Mode}
    (first : NeutralTransition before middle)
    (second : NeutralTransition middle after) :
    NeutralTransition before after := by
  intro tail possible
  rcases second possible with
    ⟨middleValue, middlePossible, secondEquivalent⟩
  rcases first middlePossible with
    ⟨previous, previousPossible, firstEquivalent⟩
  exact ⟨previous, previousPossible,
    Line.Gaussian.Proj.equivalent_trans
      firstEquivalent secondEquivalent
      (Mode.Semantics.SemanticMode.parserTail_valid middle middleValue)
      (Mode.Semantics.SemanticMode.parserTail_valid after tail)⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Geometry.Projective in
/-- Prepend a neutral transition to a contracting transition while retaining the same safe block and tail. -/
theorem thenContracting {before middle after
  : Data.CCL.Transducer.Mode} {entry : Data.CCL.Encoding.Block.Redundant}
    (first : NeutralTransition before middle)
    (second : ContractingTransition middle after entry) :
    ContractingTransition before after entry := by
  intro tail possible
  rcases second possible with
    ⟨middleValue, middlePossible, blockTail, outputEquivalent,
      tailEquivalent⟩
  rcases first middlePossible with
    ⟨previous, previousPossible, firstEquivalent⟩
  have imageValid :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      entry.matrix_det_ne blockTail.point_valid
  exact ⟨previous, previousPossible, blockTail,
    Line.Gaussian.Proj.equivalent_trans
      firstEquivalent outputEquivalent
      (Mode.Semantics.SemanticMode.parserTail_valid middle middleValue) imageValid,
    tailEquivalent⟩

end NeutralTransition

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
/-- Classify a transition as projectively neutral or contracting through one exact retained safe block. -/
def AccountedStep (before after : Data.CCL.Transducer.Mode) :
  Prop :=
  NeutralTransition before after ∨
    ∃ entry : Data.CCL.Encoding.Block.Redundant, ContractingTransition before after entry
end Purelib.Data.CCL.Transducer.Contraction.Transition

end
