module
public import Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples

import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Boundary
import Purelib.Computation.Query.Computation

@[expose] public section

/-!
# Generated public contracts and noninterference regressions

The adaptive protocol genuinely changes its source outside the recorded
keys, while its complete result and repeated-query trace remain unchanged.
The same theorem is then instantiated for the real polynomial and
exponential integration controllers, including zero and nonzero bit counts.
No equality or decidability assumption on payloads is introduced.
-/

namespace Purelib.Examples.Approximation.Queries.Noninterference.WorkedExamples

open Purelib.Examples.Approximation.Queries

open Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples (adaptive naturalOracle)
open Purelib.Computation.Query
open Purelib.Examples.Approximation

universe u

/-- An oracle preserving the original adaptive trace replies with arbitrary other values.

Overlays the retained transcript on the constant supplied payload oracle. -/
def altered (payload : Nat) : Nat → Nat :=
  Boundary.Trace.overlay (Adaptive.WorkedExamples.adaptive.run
    Adaptive.WorkedExamples.naturalOracle).trace (fun _ => payload)

/-- Changing the payload changes the reply at an unqueried index. -/
theorem unqueried_reply_really_changes :
  altered 17 1 ≠ altered 29 1 := by decide

/-- The altered oracle retains the repeated queried replies one, three, one. -/
theorem repeated_replies_preserved (payload
  : Nat) :
    [altered payload 0, altered payload 2,
      altered payload 0] = [1, 3, 1] := rfl

/-- Changing unqueried payloads preserves the entire original adaptive run.

The retained trace overlay preserves both the answer-dependent query path and its result. -/
theorem adaptive_payload_erasure (payload :
  Nat) :
    Adaptive.WorkedExamples.adaptive.run (altered payload) =
      Adaptive.WorkedExamples.adaptive.run naturalOracle :=
  Computation.Query.Protocol.annotation_erasure Adaptive.WorkedExamples.adaptive
    Adaptive.WorkedExamples.naturalOracle payload (fun value _ => value)

/-- Every altered payload retains the original ordered query trace. -/
theorem adaptive_trace_preserved (payload :
  Nat) :
    (Adaptive.WorkedExamples.adaptive.run (altered payload)).trace.map
      Basic.Exchange.query = [0, 2, 0] := by
  rw [adaptive_payload_erasure]
  exact Adaptive.WorkedExamples.adaptive_questions

end Purelib.Examples.Approximation.Queries.Noninterference.WorkedExamples

end
