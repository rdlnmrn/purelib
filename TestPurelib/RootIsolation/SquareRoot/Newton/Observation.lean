module

import Purelib.RootIsolation.SquareRoot.Newton.Observation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field

/-! # Executed callback checks and finite-search payload erasure -/

namespace TestPurelib.RootIsolation.SquareRoot.Newton.Observation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.RootIsolation.SquareRoot.Newton.Search
open Purelib.Computation.Query

/-- Compare every ordered callback question and reply along with the returned numerical point. -/
private def same (left right : Basic.Execution Canonical Bool (Option Canonical)) : Bool :=
  decide (left.value = right.value) &&
    decide (left.trace.map (fun entry => (entry.query, entry.reply)) =
      right.trace.map (fun entry => (entry.query, entry.reply)))

/-- Execute rejected axis requests, imaginary selection, exhaustion and exact replay of the actual trace. -/
public def run : IO Unit := do
  let acceptable := fun point : Canonical => point = (⟨0, 1⟩ : Canonical)
  let computation := Observation.search 2 1 1 ⟨1, 1⟩
  let original := computation.run (Observation.answer acceptable)
  unless decide (original.value = some ⟨0, 1⟩) &&
      decide (original.trace.map (fun entry => (entry.query, entry.reply)) =
        [(⟨1, 0⟩, false), (⟨0, 1⟩, true)]) do
    throw (IO.userError "root search failed to display its rejected real and accepted imaginary callbacks")
  let changed := computation.run (Boundary.Trace.overlay original.trace (fun _ => true))
  unless same changed original do
    throw (IO.userError "outside predicate changes altered the complete root-search execution")
  match computation.replayExact original.trace with
  | .ok value =>
      unless decide (value = original.value) do
        throw (IO.userError "root search replay returned a different selected point")
  | .error _ => throw (IO.userError "root search rejected its exact callback transcript")
  let exhausted := (Observation.search 2 2 1 ⟨1, 1⟩).run (fun _ => false)
  unless exhausted.value.isNone && exhausted.trace.length == 6 do
    throw (IO.userError "finite root-search exhaustion lost rejected or repeated callback occurrences")
  let empty := (Observation.search 2 0 1 ⟨1, 1⟩).run (fun _ => true)
  unless empty.value.isNone && empty.trace.isEmpty do
    throw (IO.userError "zero-fuel root search invoked an acceptance callback")
  IO.print "root evaluator coverage: ordered checks, repeats, exhaustion, replay and complete erasure passed\n"

end TestPurelib.RootIsolation.SquareRoot.Newton.Observation
