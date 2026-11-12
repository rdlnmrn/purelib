module

import Purelib.Integration.Algebraic.SquareFactor.PathObservation.Expansion
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Original canonical observers with actual source construction recorded -/

namespace TestPurelib.Integration.Algebraic.SquareFactor.PathExpansion

open Purelib
open Purelib.Integration.Algebraic.SquareFactor

/-- Check a canonical observation requesting a later model, shared initial preparation and exact full-source replay. -/
private def check {polynomial : Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial}
    {request : Curves.Hyperelliptic.Differentials.SquareFactor.Request}
    {prepared : Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment}
    (safe : data.Safe) (count : Nat) : IO Unit := do
  let query : Integration.CertifiedProgram.Request := ⟨1, 1, by decide⟩
  let sheet : Fin 2 := ⟨0, by decide⟩
  let computation := PathObservation.Expansion.computation safe sheet query count
  let recorded := computation.run (PathObservation.Expansion.answer safe sheet)
  match recorded.value with
  | .error _ => throw (IO.userError "canonical path expansion rejected an actual original source reply")
  | .ok execution =>
      match execution.value with
      | .error _ => throw (IO.userError "canonical path expansion changed the original successful observation")
      | .ok observed =>
          unless observed.selected.index == 1 && decide (observed.selected.sample = 0) &&
              observed.word.length == count do
            throw (IO.userError "canonical expansion lost its later selected model, exact sample or requested word")
          unless execution.trace.all (fun entry => entry.query == 1) && !execution.trace.isEmpty do
            throw (IO.userError "canonical expansion lost its original indexed model log")
          let initial := recorded.trace.takeWhile fun entry =>
            match entry.query with | .initial _ => true | .refinement _ => false
          match initial with
          | _ :: preparedMesh :: _ =>
              match preparedMesh.reply with
              | .initial (.prepare (.mesh mesh _)) =>
                  unless initial.length == 2 + 3 * mesh.run.stepCount do
                    throw (IO.userError "canonical observer repeated initial preparation or omitted a cell request")
              | _ => throw (IO.userError "canonical observer lost its actual original prepared mesh receipt")
          | _ => throw (IO.userError "canonical observer omitted initial isolation or mesh preparation")
          let later := recorded.trace.drop initial.length
          unless !later.isEmpty && later.all (fun entry =>
              match entry.query with | .initial _ => false | .refinement _ => true) do
            throw (IO.userError "canonical observer did not reuse its initial layer for every later model query")
          match computation.replayExact recorded.trace with
          | .ok (.ok replayed) =>
              match replayed.value with
              | .ok replayedObservation =>
                  unless decide (replayedObservation.word = observed.word) &&
                      decide (replayed.trace.map
                        (fun entry => (entry.query, entry.reply.sample, entry.reply.allowance)) =
                        execution.trace.map (fun entry => (entry.query, entry.reply.sample, entry.reply.allowance))) do
                    throw (IO.userError "canonical source replay changed the original observation or ordered model log")
              | _ => throw (IO.userError "canonical source replay changed the original successful outcome")
          | _ => throw (IO.userError "canonical source replay rejected its actual initialization/refinement receipts")
          match later with
          | first :: _ =>
              let overlaid := computation.run (Computation.Query.Boundary.Trace.overlay recorded.trace
                (fun _ => first.reply))
              match overlaid.value with
              | .ok same =>
                  match same.value with
                  | .ok sameObservation =>
                      unless decide (sameObservation.word = observed.word) &&
                          decide (same.trace.map (fun entry => (entry.query, entry.reply.sample)) =
                            execution.trace.map (fun entry => (entry.query, entry.reply.sample))) &&
                          overlaid.trace.length == recorded.trace.length do
                        throw (IO.userError "outside source replies changed the complete canonical observation or logs")
                  | _ => throw (IO.userError "outside source replies changed the successful original observation")
              | _ => throw (IO.userError "outside source replies invalidated a saved canonical source request")
              let rejected := computation.run (fun _ => first.reply)
              match rejected.value with
              | .error .expectedInitial =>
                  unless rejected.trace.length == 1 do
                    throw (IO.userError "wrong initial source stage did not stop before all later callbacks")
              | _ => throw (IO.userError "canonical observer accepted a refinement reply at its initial boundary")
          | [] => throw (IO.userError "canonical observer has no actual later source reply for the rejection check")

/-- Execute the original zero-position source at zero and one requested bit with a forced later model index. -/
public def run : IO Unit := do
  match PathInput.prepare ⟨[1]⟩ (.original 0) ⟨0, 0⟩ with
  | .error _ => throw (IO.userError "canonical expansion fixture failed original coefficient preparation")
  | .ok prepared =>
      match prepared.outcome with
      | .endpointObstruction _ _ => throw (IO.userError "canonical expansion fixture has an endpoint obstruction")
      | .inconclusive _ => throw (IO.userError "canonical expansion fixture lacks original path margins")
      | .accepted safe =>
          check safe 0
          check safe 1
  IO.print "canonical path expansion: original source, later models, initial reuse, both logs and replay passed\n"

end TestPurelib.Integration.Algebraic.SquareFactor.PathExpansion
