module
import Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Replay

/-! Regression checks for the retained approximation queries adaptive contracts. -/

namespace TestPurelib.Approximation.Queries.Adaptive

open Purelib.Examples.Approximation.Queries.Adaptive.WorkedExamples

open Purelib.Computation.Query
open Purelib

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

end TestPurelib.Approximation.Queries.Adaptive
