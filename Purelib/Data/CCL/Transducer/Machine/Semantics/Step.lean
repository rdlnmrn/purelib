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
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Data.List.Append

/-!
# Exact semantics of machine advances

The dependent cursor certificate retains its origin process state and parser image.
Returning a bit or advancing finitely carries that same semantic witness and grammar invariant.
-/

public section

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
    {origin : Approximation.Gaussian.Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState machine) :
    Machine.Semantics.Basic.ExactCursor origin originState
      (Machine.Step.nextBit machine).2 := by
  refine
    { grammar := Machine.Grammar.Step.nextBit_invariant machine cursor.grammar
      exact := ?_ }
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil =>
          let emission := Emission.Step.step mode
          have phase := cursor.grammar
          change (Parser.State.parse (emitted ++ [])).phase =
            Mode.Grammar.modeRawPhase mode at phase
          rw [Append.append_nil] at phase
          have before : ∀ {tail : Basic.Canonical},
              Mode.Semantics.SemanticMode.possible mode tail →
                ∃ value : Basic.Canonical,
                  origin.Possible originState value ∧
                    (Line.Matrix.act
                      (Parser.State.parse emitted).matrix
                      (Mode.Semantics.SemanticMode.parserTail mode tail)).Equivalent
                        (Line.Proj.affine value) := by
            intro tail possible
            have result := cursor.exact possible
            change ∃ value : Basic.Canonical,
              origin.Possible originState value ∧
                (Line.Matrix.act
                  (Parser.State.parse (emitted ++ [])).matrix
                  (Mode.Semantics.SemanticMode.parserTail mode tail)).Equivalent
                    (Line.Proj.affine value) at result
            rw [Append.append_nil] at result
            exact result
          intro tail possible
          have afterPossible :
              Mode.Semantics.SemanticMode.possible emission.next tail := by
            change Mode.Semantics.SemanticMode.possible
              (Machine.Step.consumeEmission emitted emission).2.mode tail at possible
            rw [Machine.Committed.consumeEmission_mode] at possible
            exact possible
          have result := Emission.Semantics.Basic.extend_exact origin originState mode emitted
            emission phase before (Emission.Semantics.Step.step_exact mode) afterPossible
          rw [show (Machine.Step.nextBit
            ({ mode := mode, emitted := emitted, pending := [] } :
              Machine)).2 =
              (Machine.Step.consumeEmission emitted emission).2 by rfl,
            Machine.Committed.consumeEmission_committed, Machine.Committed.consumeEmission_mode]
          exact result
      | cons bit rest =>
          intro tail possible
          change Mode.Semantics.SemanticMode.possible mode tail at possible
          have result := cursor.exact possible
          change ∃ value : Basic.Canonical,
            origin.Possible originState value ∧
              (Line.Matrix.act
                (Parser.State.parse
                  ((emitted ++ [bit]) ++ rest)).matrix
                (Mode.Semantics.SemanticMode.parserTail mode tail)).Equivalent
                  (Line.Proj.affine value)
          rw [Append.append_assoc]
          exact result

/-- Every finite machine advance preserves the exact cursor relation to its process and dependent state.

The recursive certificate follows the same returned machine at each bit transition. Its retained origin witness and
exact committed parser relation are carried through the specified count. -/
theorem advance
    {origin : Approximation.Gaussian.Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState machine) : ∀ count : Nat,
    Machine.Semantics.Basic.ExactCursor origin originState
      (Machine.Advance.advance machine count)
  | 0 => cursor
  | count + 1 => (cursor.nextBit.advance count)

end Purelib.Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
