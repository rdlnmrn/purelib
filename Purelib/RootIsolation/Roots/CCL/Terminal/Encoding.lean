module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Transducer
import Purelib.Data.List.Basic
import Purelib.Data.List.Prefix.Cursor
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Roots.CCL.Terminal.Basic (NonzeroTerminal)

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.Roots.CCL.Terminal
namespace Basic.NonzeroTerminal

/-- Coherent incremental cursor through the exact terminal's complete CCL
word. -/
def transducer {p :
  CoefficientPolynomial} (data :
    NonzeroTerminal p) :
    Data.CCL.Encoding.Transducer.EncodingTransducer data.fraction :=
  Data.CCL.Encoding.Transducer.EncodingTransducer.initial data.encoding

/-- The terminal transducer's full raw encoding is exactly the retained terminal word. -/
theorem transducer_completeWord
    {p : CoefficientPolynomial} (data :
      NonzeroTerminal p) :
    Block.Basic.rawWord data.transducer.encoding.blocks = data.word :=
  data.word_eq.symm

end Basic.NonzeroTerminal

/-! ## Unified exact terminal transducer -/

set_option genInjectivity false in
/-- A distinguished zero terminal, or a coherently advancing cursor through
the complete finite encoding of an exact nonzero rational root. -/
inductive Encoding.TerminalTransducer (p :
  CoefficientPolynomial) where
  /-- A certified exact zero root, represented without a raw CCL word. -/ | zero (root : p.eval 0 = 0)
  /-- An exact nonzero root with a prefix cursor indexed by its retained complete encoding. -/ | nonzero (data :
    NonzeroTerminal p)
      (state : Data.List.Prefix.Cursor.PrefixState (Block.Basic.rawWord data.encoding.blocks))

constructive_injectivity Encoding.TerminalTransducer

namespace Encoding.TerminalTransducer

/-- Initialize a cursor from an exact root terminal, retaining the distinguished zero case. -/
def ofTerminal {p :
  CoefficientPolynomial} : RootIsolation.Roots.CCL.Terminal p →
  Roots.CCL.Terminal.Encoding.TerminalTransducer p
  | .zero root => .zero root
  | .nonzero data => .nonzero data data.transducer.state

/-- Advance the nonzero terminal's existing prefix cursor by the requested bit count; zero remains terminal. -/
def advance {p :
  CoefficientPolynomial} :
    Roots.CCL.Terminal.Encoding.TerminalTransducer p → Nat → Roots.CCL.Terminal.Encoding.TerminalTransducer p
  | .zero root, _ => .zero root
  | .nonzero data state, count => .nonzero data (state.advance count)

/-- Read the emitted raw prefix, or return no word for the distinguished zero terminal. -/
def emitted? {p :
  CoefficientPolynomial} :
    Roots.CCL.Terminal.Encoding.TerminalTransducer p → Option
  Data.List.Basic.BinaryWord
  | .zero _ => none
  | .nonzero _ state => some state.emitted

/-- Read the emitted prefix length, with length zero for the zero terminal. -/
def emittedLength {p :
  CoefficientPolynomial} :
    Roots.CCL.Terminal.Encoding.TerminalTransducer p → Nat
  | .zero _ => 0
  | .nonzero _ state => state.emitted.length

/-- The cursor has exhausted its finite encoding, or is the distinguished zero terminal. -/
def IsTerminal {p :
  CoefficientPolynomial} :
    Roots.CCL.Terminal.Encoding.TerminalTransducer p → Prop
  | .zero _ => True
  | .nonzero _ state => state.IsTerminal

/-- Read the pending encoding length, with no pending bits for the zero terminal. -/
def remaining {p :
  CoefficientPolynomial} :
    Roots.CCL.Terminal.Encoding.TerminalTransducer p → Nat
  | .zero _ => 0
  | .nonzero _ state => state.pending.length

/-- Prefix coherence also covers the distinguished zero state: it remains
the same non-word terminal under every request. -/
theorem advance_prefix {p :
  CoefficientPolynomial}
    (transducer : Roots.CCL.Terminal.Encoding.TerminalTransducer p) (count : Nat) :
    match transducer.emitted?, (transducer.advance count).emitted? with
    | none, none => True
    | some earlier, some later => earlier.IsPrefix later
    | _, _ => False := by
  cases transducer with
  | zero root => exact True.intro
  | nonzero data state =>
      rcases state.advance_extends count with
        ⟨extension, extensionIdentity⟩
      exact ⟨extension, extensionIdentity.symm⟩

/-- Every exact-root transducer reaches a certified terminal state after its
explicit finite pending length; zero is terminal immediately. -/
theorem advance_remaining_terminal {p :
  CoefficientPolynomial}
    (transducer : Roots.CCL.Terminal.Encoding.TerminalTransducer p) :
    (transducer.advance transducer.remaining).IsTerminal := by
  cases transducer with
  | zero root => exact True.intro
  | nonzero data state => exact state.advance_remaining_terminal

/-- Each exact-terminal request either appends exactly the requested number
of bits or reaches the terminal state. -/
theorem advance_progress_or_terminal {p :
  CoefficientPolynomial}
    (transducer : Roots.CCL.Terminal.Encoding.TerminalTransducer p) (count : Nat) :
    (transducer.advance count).emittedLength =
        transducer.emittedLength + count ∨
      (transducer.advance count).IsTerminal := by
  cases transducer with
  | zero root => exact Or.inr True.intro
  | nonzero data state => exact state.advance_progress_or_terminal count

/-- At a nonzero terminal state all bits have been emitted and the stored
projective realization reconstructs the exact root. -/
theorem nonzero_terminal_spec
    {p : CoefficientPolynomial} (data :
      NonzeroTerminal p)
    (state : Data.List.Prefix.Cursor.PrefixState (Block.Basic.rawWord data.encoding.blocks))
    (terminal : state.IsTerminal) :
    state.emitted = data.word ∧
      data.encoding.point.Equivalent (Geometry.Projective.Line.Proj.affine data.point) := by
  constructor
  · rw [state.emitted_eq_complete_of_terminal terminal]
    exact data.word_eq.symm
  · rw [← data.fractionValue]
    exact data.encoding.reconstruct

end Encoding.TerminalTransducer
end Purelib.RootIsolation.Roots.CCL.Terminal

end
