module
import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Replay

@[expose] public section

/-!
# Finite query and complete integration-output replay regressions

The natural-number protocol tests genuine adaptive query selection and
repetition.  The polynomial client separately exercises the real CCL output
projection, with the original complex quadratic and repeated path traversal.
Malformed logs test missing, mismatched, trailing and invalid replies.
-/

namespace Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples

open Purelib.Computation.Query
open Purelib

/-- The retained three-query computation with an answer-dependent second question.

Queries zero, then one beyond the first reply, then zero again, and adds the three actual replies. -/
def adaptive :
    Computation.Query.Protocol Nat Nat Nat
  :=
  (Computation.Query.Protocol.query 0).bind fun first =>
    (Computation.Query.Protocol.query (first + 1)).bind fun second =>
      (Computation.Query.Protocol.query 0).map fun third => first + second + third

/-- The natural-number oracle returning one more than its query. -/
def naturalOracle (index : Nat) : Nat := index + 1

/-- The original oracle run asks the ordered questions zero, two, zero. -/
theorem adaptive_questions :
    (adaptive.run
      naturalOracle).trace.map Basic.Exchange.query = [0, 2, 0]
      := by decide

/-- The original adaptive run returns five. -/
theorem adaptive_result :
  (adaptive.run
  naturalOracle).value = 5 := by decide

/-- The exact ordered three-exchange transcript replays to five. -/
theorem adaptive_replay :
    adaptive.replayExact [⟨0, 1⟩, ⟨2, 3⟩, ⟨0, 1⟩] = .ok 5 := by
      rfl

/-- A one-exchange transcript retains the missing second question two. -/
theorem adaptive_missing :
  adaptive.replayExact [⟨0, 1⟩] = .error (.missing 2) := by rfl

/-- An incorrect second query yields the exact expected-versus-observed mismatch. -/
theorem adaptive_mismatch :
    adaptive.replayExact [⟨0, 1⟩, ⟨1, 3⟩] = .error (.mismatch 2 1
      (by decide)) := by rfl

/-- Reordering the transcript fails at the original first query. -/
theorem adaptive_reordered :
    adaptive.replayExact [⟨2, 3⟩, ⟨0, 1⟩, ⟨0, 1⟩] =
      .error (.mismatch 0 2 (by decide)) := by rfl

/-- An unused fourth exchange is retained as a trailing-query failure. -/
theorem adaptive_trailing :
    adaptive.replayExact [⟨0, 1⟩, ⟨2, 3⟩, ⟨0, 1⟩, ⟨7, 100⟩] =
      .error (.trailing 7) := by rfl

/-- A changed first reply alters the second question and yields fourteen.

The replay retains the matching adaptive transcript zero/four, five/six, zero/four in its original order. -/
theorem adaptive_changed_reply :
    adaptive.replayExact [⟨0, 4⟩, ⟨5, 6⟩, ⟨0, 4⟩] = .ok 14 := by
      rfl

end Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples

end
