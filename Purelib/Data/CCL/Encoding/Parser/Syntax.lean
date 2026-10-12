module

public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.List.BinaryPrefix.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.CCL.Encoding.Parser.Syntax

/-- Distinguish initial-high, initial-low and subsequent loop blocks in the parser grammar. -/
inductive BlockKind where
  /-- An initial block normalized from the high branch. -/ | initialHigh
  /-- An initial block normalized from the low branch. -/ | initialLow
  /-- A subsequent block in the residual normalization loop. -/ | loop
deriving DecidableEq

derive_exposed_repr BlockKind

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
set_option genInjectivity false in
/-- Retain the unfinished parser phase, unary count and exact sector bits already read.

The initial state has no selected branch. Unary phases retain their natural count; a sector phase keeps the original
block kind and exponent alongside zero, one or two retained bits. -/
inductive Phase where
  /-- The initial phase before the high or low branch bit is read. -/ | initial
  /-- Retain the current initial-high unary count. -/ | highUnary (count : Nat)
  /-- Retain the current initial-low unary count. -/ | lowUnary (count : Nat)
  /-- Retain the current subsequent-loop unary count. -/ | loopUnary (count : Nat)
  /-- Retain the block kind, exponent and exact partial three-bit sector code. -/ | sector (kind :
    BlockKind) (exponent : Nat) (bits : Sector.Code.SectorBits)
deriving DecidableEq

constructive_injectivity Phase

derive_exposed_repr Phase

namespace Phase

section
open Purelib.Data
/-- Read the retained unary count or sector exponent, returning zero at the initial phase. -/
def counter : Phase → Nat
  | .highUnary count => count
  | .lowUnary count => count
  | .loopUnary count => count
  | .sector _ exponent _ => exponent
  | .initial => 0

/-- Consume one Boolean syntax bit and retain the resulting exact parser phase.

The first bit selects high or low normalization, unary true bits increment their count, and false starts sector reading.
The third sector bit completes the block and resets to loop-unary zero. -/
def next : Phase → Bool →
  Phase
  | .initial, bit =>
      if bit then .highUnary 1 else .lowUnary 0
  | .highUnary count, bit =>
      if bit then .highUnary (count + 1)
      else .sector .initialHigh count .zero
  | .lowUnary count, bit =>
      if bit then .lowUnary (count + 1)
      else .sector .initialLow count .zero
  | .loopUnary count, bit =>
      if bit then .loopUnary (count + 1)
      else .sector .loop count .zero
  | .sector kind exponent .zero, bit =>
      .sector kind exponent (.one bit)
  | .sector kind exponent (.one first), bit =>
      .sector kind exponent (.two first bit)
  | .sector _ _ (.two _ _), _ => .loopUnary 0

end

open Purelib.Data in
open Purelib.Data.List in
/-- Fold the retained Boolean word through the syntax transition from the supplied phase. -/
def consume (phase : Phase) (word :
  BinaryPrefix.Basic.SourceEncodingRawParserWordAlias) : Phase :=
  word.foldl next phase

end Phase
end Purelib.Data.CCL.Encoding.Parser.Syntax

end
