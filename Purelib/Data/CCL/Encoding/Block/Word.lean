module

public import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Syntax

section
@[expose] public section

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace Purelib.Data.CCL.Encoding.Block.Redundant
section Block

open Purelib.Data.CCL.Encoding in
/-- Read the exact regular or initial-low bit word stored by a redundant block. -/
def word (entry : _root_.Purelib.Data.CCL.Encoding.Block.Redundant) : List
  Bool :=
  match entry.kind with
  | .regular => Block.Syntax.regularWord entry.exponent entry.sector
  | .initialLow => Block.Syntax.lowWord entry.exponent entry.sector
end Block
end Purelib.Data.CCL.Encoding.Block.Redundant

namespace Purelib.Data.CCL.Encoding.Block.Word

open Purelib.Data.CCL.Encoding in
/-- Concatenate the retained redundant block words in their original list order. -/
def rawWord : List Redundant → List Bool
  | [] => []
  | entry :: remaining => entry.word ++ rawWord remaining

end Purelib.Data.CCL.Encoding.Block.Word

end
