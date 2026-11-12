module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Emission.Semantics.Basic
import Purelib.Data.CCL.Transducer.Emission.Semantics.Step
import Purelib.Data.CCL.Transducer.Emission.Step
public import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Grammar.Step
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
public import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.Data.List.Append

open Purelib.Data.CCL.Transducer.Mode.Semantics

/-!
# Exact semantics of machine advances

The dependent cursor certificate retains its origin process state and parser image.
Returning a bit or advancing finitely carries that same semantic witness and grammar invariant.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry.Projective

/-- Each possible tail after one actual bit step has an earlier possible tail with the same cursor image.

Queued bits retain the original mode and committed parser. An actual new
emission uses its exact local semantic certificate and the original phase,
retaining the before and after parser images independently of an origin.
-/
theorem nextBit_predecessor (machine : Machine) (grammar : Grammar.Invariant machine)
    {tail : Basic.Canonical}
    (possible : SemanticMode.possible (Step.nextBit machine).2.mode tail) :
    ∃ previous : Basic.Canonical, SemanticMode.possible machine.mode previous ∧
      (Cursor.Image.Machine.image (Step.nextBit machine).2 tail).Equivalent
        (Cursor.Image.Machine.image machine previous) := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil =>
          let emission := Emission.Step.step mode
          have phase : (Parser.State.parse emitted).phase = Mode.Grammar.modeRawPhase mode := by
            change (Parser.State.parse (emitted ++ [])).phase = Mode.Grammar.modeRawPhase mode at grammar
            rewrite [Append.append_nil] at grammar
            exact grammar
          have afterPossible : SemanticMode.possible emission.next tail := by
            change SemanticMode.possible (Step.consumeEmission emitted emission).2.mode tail
              at possible
            rewrite [Committed.consumeEmission_mode] at possible
            exact possible
          rcases Emission.Semantics.Step.step_exact mode (Parser.State.parse emitted)
              (Parser.State.parse_det_ne emitted) phase afterPossible with ⟨previous, previousPossible, localExact⟩
          refine ⟨previous, previousPossible, ?_⟩
          change (Line.Matrix.act
              (Parser.State.parse (committed (Step.consumeEmission emitted emission).2)).matrix
              (SemanticMode.parserTail
                (Step.consumeEmission emitted emission).2.mode tail)).Equivalent
            (Line.Matrix.act (Parser.State.parse (emitted ++ [])).matrix
              (SemanticMode.parserTail mode previous))
          rewrite [Committed.consumeEmission_committed, Committed.consumeEmission_mode,
            Parser.State.parse_append, Append.append_nil]
          exact localExact
      | cons bit rest =>
          change SemanticMode.possible mode tail at possible
          refine ⟨tail, possible, ?_⟩
          change (Line.Matrix.act (Parser.State.parse ((emitted ++ [bit]) ++ rest)).matrix
              (SemanticMode.parserTail mode tail)).Equivalent
            (Line.Matrix.act (Parser.State.parse (emitted ++ (bit :: rest))).matrix
              (SemanticMode.parserTail mode tail))
          rewrite [Append.append_assoc]
          exact Line.Proj.Equivalent.refl _

end Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

namespace Purelib.Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry.Projective

/-- Returning one bit preserves the exact cursor certificate relative to the same original process state.

A queued bit leaves the committed word and mode intact. With an empty queue, the exact emission relation extends the
committed parser image while retaining its original-state witness and grammar certificate. -/
theorem nextBit
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine) :
    ExactCursor origin originState
      (Step.nextBit machine).2 := by
  refine
    { grammar := Grammar.Step.nextBit_invariant machine cursor.grammar
      exact := ?_ }
  intro tail possible
  rcases nextBit_predecessor machine cursor.grammar possible with
    ⟨previous, previousPossible, localExact⟩
  rcases cursor.exact previousPossible with ⟨value, originalPossible, represented⟩
  refine ⟨value, originalPossible, ?_⟩
  exact Line.Gaussian.Proj.equivalent_trans localExact represented
    (Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      (Parser.State.parse_det_ne (committed machine))
      (SemanticMode.parserTail_valid machine.mode previous))
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate value)

/-- Every finite machine advance preserves the exact cursor relation to its process and dependent state.

The recursive certificate follows the same returned machine at each bit transition. Its retained origin witness and
exact committed parser relation are carried through the specified count. -/
theorem advance
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine) : ∀ count : Nat,
    ExactCursor origin originState
      (Advance.advance machine count)
  | 0 => cursor
  | count + 1 => (cursor.nextBit.advance count)

end Purelib.Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
