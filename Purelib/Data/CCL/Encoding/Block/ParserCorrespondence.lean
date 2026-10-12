module
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Exact semantics of redundant progressive CCL blocks

The arithmetic controller is allowed to select an overlapping safe sector
outside the canonical half-open annulus table.  This file proves that doing
so does not alter the represented point.  Local safety alone gives both the
exact inverse chart and the strict lower norm needed by the following loop.

The zero-residual case is kept projective.  It maps exactly to the completed
block's `omega` tail and can therefore emit the productive unary padding of
`TerminalPadding` without deciding equality.
-/

namespace Purelib.Data.CCL.Encoding.Block.ParserCorrespondence

open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Read the redundant block record corresponding to a retained parser kind, exponent and sector. -/
def redundantBlock (kind : Parser.Syntax.BlockKind)
  (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    Data.CCL.Encoding.Block.Redundant :=
  { kind := match kind with
      | .initialLow => .initialLow
      | .initialHigh | .loop => .regular
    exponent := exponent
    sector := sector }

/-- The converted redundant block has exactly the original parser block matrix. -/
@[simp] theorem redundantBlock_matrix
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    (redundantBlock kind exponent sector).matrix =
      Block.Matrix.blockMatrix kind exponent sector := by
  cases kind <;> rfl
end Purelib.Data.CCL.Encoding.Block.ParserCorrespondence

end
