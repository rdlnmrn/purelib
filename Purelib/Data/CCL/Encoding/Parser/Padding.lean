module
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Productive unary padding at a projective CCL terminal

An arithmetic transducer cannot in general decide that opaque nonterminating
inputs have combined to an exact Gaussian rational.  The canonical finite
encoder remains unchanged.  This module supplies a separate projective
continuation convention: after a completed sector, an unresolved zero
residual may remain at `omega`, and every further unary `1` fixes that formal
coordinate while strengthening the finite large-tail predicate.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Padding

open Purelib.Data.List in
/-- Append the requested number of true padding bits to the retained word. -/
def pad (word :
  BinaryPrefix.Basic.SourceEncodingTerminalPaddingWordAlias) (count : Nat) :
  BinaryPrefix.Basic.SourceEncodingTerminalPaddingWordAlias :=
  word ++ List.replicate count true

open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Padding a word already in a loop phase increases its exact counter while preserving the retained matrix and history.
-/
theorem parse_pad_of_loop
    {word : BinaryPrefix.Basic.SourceEncodingTerminalPaddingWordAlias} {start : Nat} {matrix :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix}
    {history : List Data.CCL.Encoding.Parser.Constraint}
    (parsed : Parser.State.parse word = ⟨.loopUnary start, matrix, history⟩)
    (count : Nat) :
    Parser.State.parse (pad word count) =
      ⟨.loopUnary (start + count), matrix, history⟩ := by
  rw [pad, Parser.State.parse_append, parsed]
  exact Parser.State.foldl_true_unary .loop count start matrix history

open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- True padding in a loop phase preserves the exact projective truncation obtained by acting on infinity. -/
theorem truncation_parse_pad_of_loop
    {word : BinaryPrefix.Basic.SourceEncodingTerminalPaddingWordAlias} {start : Nat} {matrix :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix}
    {history : List Data.CCL.Encoding.Parser.Constraint}
    (parsed : Parser.State.parse word = ⟨.loopUnary start, matrix, history⟩)
    (count : Nat) :
    (Parser.State.parse (pad word count)).truncation =
      Line.Matrix.act matrix Line.Proj.omega := by
  rw [parse_pad_of_loop parsed count]
  rfl
end Purelib.Data.CCL.Encoding.Parser.Padding

end
