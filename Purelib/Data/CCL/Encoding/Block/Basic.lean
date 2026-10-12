module

public import Purelib.Data.CCL.Encoding.Block.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Tactic.QuotientFreeOmega

import Mathlib.Order.Basic
meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic

/-- Distinguish a regular block from an initial low-normalization block. -/
inductive BlockKind where
  /-- A block using regular gamma-power normalization. -/ | regular
  /-- A block using the initial low-value normalization. -/ | initialLow
deriving @[expose] DecidableEq

derive_exposed_repr BlockKind
end Purelib.Data.CCL.Encoding.Block.Basic
end
end

end

section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic
open Purelib.Data.CCL.Encoding in
/-- The exact block-kind carrier retained by the encoder. -/
abbrev SourceEncodingEncoderBlockKindAlias := BlockKind
end Purelib.Data.CCL.Encoding.Block.Basic

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding

set_option genInjectivity false in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Retain a block kind, natural normalization exponent and selected sector.

These fields determine the exact encoded word and decoder matrix. The record itself does not assert semantic
admissibility of a source value. -/
structure Block where
  /-- The retained regular or initial-low branch. -/ kind : Block.Basic.BlockKind
  /-- The retained natural gamma-power exponent. -/ exponent : Nat
  /-- The retained nominal eight-sector selection. -/ sector : ComplexContinuedFraction.Encoding.Sector
deriving @[expose] DecidableEq

/- Opaque injectivity of the original retained fields. -/

constructive_injectivity Block

namespace Block

end Block
namespace Block

end Block
derive_exposed_repr Block

end Purelib.Data.CCL.Encoding
end
end

end

section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic
open Purelib.Data.CCL.Encoding in
/-- The exact block record carrier retained by the encoder. -/
abbrev SourceEncodingEncoderBlockAlias := Block
end Purelib.Data.CCL.Encoding.Block.Basic

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block
section Block

open Purelib.Data.CCL.Encoding in
/-- Read the regular or initial-low bit word determined by the retained block fields. -/
@[expose] def word (block : Block) : List Bool :=
  match block.kind with
  | .regular => Block.Syntax.regularWord block.exponent block.sector
  | .initialLow => Block.Syntax.lowWord block.exponent block.sector
end Block
end Purelib.Data.CCL.Encoding.Block
end
end

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block
section Block

open Purelib.Data.CCL.Encoding in
/-- Every retained block word has at least four bits. -/
theorem word_length_ge_four (block : Block) : 4 ≤
  block.word.length := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [word, Block.Syntax.regularWord_length]
          exact Nat.le_add_left 4 exponent
      | initialLow =>
          rw [word, Block.Syntax.lowWord_length]
          exact (by omega)

end Block
end Purelib.Data.CCL.Encoding.Block
end
end

end

section
section
public section
namespace Purelib.Data.CCL.Encoding.Block.Redundant

/-! ## Finite redundant cylinders -/

/-- Distinguish a regular block from an initial low-normalization block. -/
inductive BlockKind where
  /-- A block using regular gamma-power normalization. -/ | regular
  /-- A block using the initial low-value normalization. -/ | initialLow
deriving @[expose] DecidableEq

derive_exposed_repr BlockKind
end Purelib.Data.CCL.Encoding.Block.Redundant
end

end

section
section
public section
namespace Purelib.Data.CCL.Encoding.Block

set_option genInjectivity false in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Retain a block kind, natural normalization exponent and selected sector.

These fields determine the exact encoded word and decoder matrix. The record itself does not assert semantic
admissibility of a source value. -/
structure Redundant where
  /-- The retained regular or initial-low branch. -/ kind : Redundant.BlockKind
  /-- The retained natural gamma-power exponent. -/ exponent : Nat
  /-- The retained nominal eight-sector selection. -/ sector : ComplexContinuedFraction.Encoding.Sector
deriving @[expose] DecidableEq

constructive_injectivity Redundant

namespace Redundant

/- Opaque injectivity of the original retained fields. -/

end Redundant

derive_exposed_repr Redundant

end Purelib.Data.CCL.Encoding.Block
end

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic

open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
/-- Concatenate the exact retained block words in list order. -/
@[expose] def rawWord : List Block →
  BinaryPrefix.Basic.SourceEncodingCylinderWordAlias
  | [] => []
  | block :: remaining => block.word ++ rawWord remaining
end Purelib.Data.CCL.Encoding.Block.Basic
end
end

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic

open Purelib.Data.CCL.Encoding in
/-- The raw word of a nonempty block list starts with its head block word. -/
@[simp] theorem rawWord_cons (block : Block) (remaining : List
  Block) :
    rawWord (block :: remaining) = block.word ++ rawWord remaining := rfl

end Purelib.Data.CCL.Encoding.Block.Basic
end
end

end

section
section
section
public section
namespace Purelib.Data.CCL.Encoding.Block.Basic

open Purelib.Data.CCL.Encoding in
/-- The raw word of an empty block list is empty. -/
@[simp] theorem rawWord_nil : rawWord [] = [] := rfl
end Purelib.Data.CCL.Encoding.Block.Basic
end
end

end
