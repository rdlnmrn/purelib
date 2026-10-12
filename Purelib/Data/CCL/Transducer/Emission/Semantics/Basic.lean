module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.CCL.Transducer.Mode.Grammar
public import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.List.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax

/-!
# Exact semantics of emission chunks

Exact emission relates each possible retained next-mode tail to an old-mode tail
through the same nonsingular parser matrix and the ordered emitted chunk.
-/

public section

namespace Purelib.Data.CCL.Transducer.Emission.Semantics.Basic

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

/-! ## Local and persistent exactness -/

/-- Require every possible next-mode tail to have an equivalent old-mode parser image across the exact emitted chunk.

The comparison uses the same nonsingular incoming parser matrix and its exact folded emitted word. Its witness remains
possible at the original mode's retained process state. -/
@[expose] def ExactEmission (mode : Mode) (emission : Emission) : Prop :=
  ∀ (parser : Encoding.Parser.State),
    Matrix2.Matrix2.determinant parser.matrix ≠ 0 →
      parser.phase = Mode.Grammar.modeRawPhase mode →
      ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible emission.next tail →
        ∃ previous : Basic.Canonical,
          Mode.Semantics.SemanticMode.possible mode previous ∧
            (Line.Matrix.act
              (emission.bits.foldl Parser.State.step parser).matrix
              (Mode.Semantics.SemanticMode.parserTail emission.next tail)).Equivalent
                (Line.Matrix.act parser.matrix
                  (Mode.Semantics.SemanticMode.parserTail mode previous))

/-- Append an exact emitted chunk while preserving the same origin process, state and represented value.

The original word's semantic relation supplies an origin witness after pulling the new tail back through the exact
emission. Matrix folding then identifies the appended word with that same retained projective image. -/
theorem extend_exact
    (origin : Approximation.Gaussian.Process) (originState : origin.State)
    (mode : Mode) (word : List Bool) (emission : Emission)
    (phase : (Parser.State.parse word).phase =
      Mode.Grammar.modeRawPhase mode)
    (before : ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible mode tail →
      ∃ value : Basic.Canonical,
        origin.Possible originState value ∧
          (Line.Matrix.act (Parser.State.parse word).matrix
            (Mode.Semantics.SemanticMode.parserTail mode tail)).Equivalent
              (Line.Proj.affine value))
    (chunkExact : Emission.Semantics.Basic.ExactEmission mode emission) :
    ∀ {tail : Basic.Canonical}, Mode.Semantics.SemanticMode.possible emission.next tail →
      ∃ value : Basic.Canonical,
        origin.Possible originState value ∧
          (Line.Matrix.act
            (Parser.State.parse (word ++ emission.bits)).matrix
            (Mode.Semantics.SemanticMode.parserTail emission.next tail)).Equivalent
              (Line.Proj.affine value) := by
  intro tail possible
  rcases chunkExact (Parser.State.parse word)
      (Parser.State.parse_det_ne word) phase possible with
    ⟨previous, previousPossible, localExact⟩
  rcases before previousPossible with ⟨value, valuePossible, beforeExact⟩
  refine ⟨value, valuePossible, ?_⟩
  rw [Parser.State.parse_append]
  exact Line.Gaussian.Proj.equivalent_trans
    localExact beforeExact
    (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      (Parser.State.parse_det_ne word)
      (Mode.Semantics.SemanticMode.parserTail_valid mode previous))
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate value)

end Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
