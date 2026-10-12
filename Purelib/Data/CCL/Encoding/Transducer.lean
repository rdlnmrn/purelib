module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.CCL.Encoding.Encoder.Cylinder
public import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.Prefix.Cursor
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Gaussian.Basic

section
public section

/-!
# Coherent finite prefix and terminal transducers

The terminating rational CCL encoder already computes a complete finite raw
word.  This module presents that word incrementally: every request appends a
finite segment to the previously emitted prefix, never retracts a bit, and
reaches a certified terminal state after the finite pending suffix is
exhausted.  The construction is structural on explicit lists and does not
parse arbitrary external prefixes.
-/

namespace Purelib.Data.CCL.Encoding.Transducer

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
set_option genInjectivity false in
/-- Retain a certified block encoding with a cursor into that exact encoding's complete bit word.

The cursor is indexed by the raw word of the stored block list. Advancing preserves that same encoding, its projective
reconstruction and the original displayed fraction. -/
structure EncodingTransducer (fraction : GaussianInt.Fraction) where
  /-- The exact certified block encoding retained for the original displayed fraction. -/ encoding :
    Encoder.Blocks.BlockEncoding fraction
  /-- The prefix cursor indexed by the raw word of that same retained block list. -/ state : Prefix.Cursor.PrefixState
    (Block.Basic.rawWord encoding.blocks)

constructive_injectivity EncodingTransducer

namespace EncodingTransducer

section
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.List in
/-- Start a prefix cursor at the empty emission of the exact retained block encoding. -/
@[expose] def initial {fraction : GaussianInt.Fraction}
  (encoding : Encoder.Blocks.BlockEncoding fraction) :
    EncodingTransducer fraction :=
  { encoding := encoding
    state := Prefix.Cursor.PrefixState.initial (Block.Basic.rawWord encoding.blocks) }

/-- Advance the retained prefix cursor by the requested bit count without recomputing its certified block encoding. -/
@[expose] def advance {fraction : GaussianInt.Fraction}
  (transducer : EncodingTransducer fraction)
    (count : Nat) : EncodingTransducer fraction :=
  { encoding := transducer.encoding
    state := transducer.state.advance count }

/-- Require the retained encoding cursor to have no pending bits. -/
@[expose] def IsTerminal {fraction :
  GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction) : Prop :=
  transducer.state.IsTerminal

/-- The exact emitted bits prefix the retained encoding's complete word. -/
theorem emitted_isPrefix {fraction :
  GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction) :
    transducer.state.emitted.IsPrefix
      (Block.Basic.rawWord transducer.encoding.blocks) :=
  transducer.state.emitted_isPrefix

open Purelib.Data.List in
/-- Advancing appends some exact bit extension to the already emitted prefix. -/
theorem advance_extends {fraction : GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction) (count : Nat) :
    ∃ extension : BinaryPrefix.Basic.SourceEncodingTransducerWordAlias,
      (transducer.advance count).state.emitted =
        transducer.state.emitted ++ extension :=
  transducer.state.advance_extends count

/-- Advancing by the retained pending length consumes the complete word and reaches terminality. -/
theorem advance_remaining_terminal {fraction :
  GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction) :
    (transducer.advance transducer.state.pending.length).IsTerminal :=
  transducer.state.advance_remaining_terminal

/-- A requested advance emits exactly that many further bits or reaches the end of the retained word. -/
theorem advance_progress_or_terminal {fraction :
  GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction) (count : Nat) :
    (transducer.advance count).state.emitted.length =
        transducer.state.emitted.length + count ∨
      (transducer.advance count).IsTerminal :=
  transducer.state.advance_progress_or_terminal count

open Purelib.Geometry.Projective in
/-- A terminal cursor has emitted its complete retained word, whose stored projective point reconstructs the original
fraction. -/
theorem terminal_spec {fraction : GaussianInt.Fraction}
    (transducer : EncodingTransducer fraction)
    (terminal : transducer.IsTerminal) :
    transducer.state.emitted = Block.Basic.rawWord transducer.encoding.blocks ∧
      transducer.encoding.point.Equivalent
        (Line.Proj.affine fraction.value) :=
  ⟨transducer.state.emitted_eq_complete_of_terminal terminal,
    transducer.encoding.reconstruct⟩

end

end EncodingTransducer

section
open Purelib.Data
open Purelib.Data.CCL.Encoding
/-- Compute the certified block encoding once and start its exact prefix cursor for a nonzero-numerator fraction. -/
@[expose] def encode (fraction : GaussianInt.Fraction) (numeratorNonzero :
  fraction.numerator ≠ 0) :
    EncodingTransducer fraction :=
  Transducer.EncodingTransducer.initial
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero)

/-- The transducer's retained complete word equals the original integral encoder output. -/
theorem encode_completeWord
    (fraction : GaussianInt.Fraction) (numeratorNonzero : fraction.numerator ≠ 0) :
    Block.Basic.rawWord (encode fraction numeratorNonzero).encoding.blocks =
      Encoder.Integral.encode fraction numeratorNonzero :=
  (Encoder.Cylinder.encode_eq_rawWord fraction numeratorNonzero).symm

end

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
/-- Advancing the newly encoded transducer preserves its exact initial emitted prefix. -/
theorem encode_advance_extends
    (fraction : GaussianInt.Fraction) (numeratorNonzero : fraction.numerator ≠ 0)
    (count : Nat) :
    ∃ extension : BinaryPrefix.Basic.SourceEncodingTransducerWordAlias,
      ((encode fraction numeratorNonzero).advance count).state.emitted =
        (encode fraction numeratorNonzero).state.emitted ++ extension :=
  (encode fraction numeratorNonzero).advance_extends count

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- Advancing the newly encoded transducer by its retained pending length reaches terminality. -/
theorem encode_reaches_terminal
    (fraction : GaussianInt.Fraction) (numeratorNonzero : fraction.numerator ≠ 0) :
    ((encode fraction numeratorNonzero).advance
      (encode fraction numeratorNonzero).state.pending.length).IsTerminal :=
  (encode fraction numeratorNonzero).advance_remaining_terminal

end Purelib.Data.CCL.Encoding.Transducer

end
