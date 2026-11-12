module

import TestPurelib.Data.CCL.Transducer.Continuation
import TestPurelib.Data.CCL.Transducer.Transition
import TestPurelib.Data.CCL.Transducer.History
import TestPurelib.Approximation.Gaussian.Observation.Cursor
import TestPurelib.Approximation.Gaussian.Observation.Prefix
import TestPurelib.Approximation.Gaussian.Observation.Prefix.Family
import TestPurelib.Data.CCL.Encoding.Prefix.Completion
import TestPurelib.Data.CCL.Encoding.Prefix.Termination
import Purelib.System.IO
import Purelib.Data.String.Basic

/-! # Compiled productive cursor continuation regression entry point -/

open Purelib.System
open Purelib.System.IO (println)
open Purelib.Data.String (append)
open TestPurelib.Approximation.Gaussian.Observation
open TestPurelib.Data.CCL.Transducer

/-- Identify the selected regression group before executing it. -/
private def phase (name : String) (action : IO Unit) : IO Unit := do
  println (append "cursor continuation phase: " name)
  let output ← IO.getStdout
  output.flush
  action

/-- Execute one named continuation regression group. -/
private def runCase (name : String) : IO Unit := do
  match name with
  | "continuation" => phase name Continuation.run
  | "retained-refinements" => phase name Continuation.retainedRefinements
  | "source-refinement-requests" => phase name Continuation.sourceRefinementRequests
  | "handled-emissions" => phase name Continuation.handledEmissions
  | "handled-histories" => phase name Continuation.handledHistories
  | "transition" => phase name Transition.run
  | "history" => phase name History.run
  | "cursor" => phase name Cursor.run
  | "prefix" => phase name Prefix.run
  | "family" => phase name Prefix.Family.run
  | "completion" => phase name TestPurelib.Data.CCL.Encoding.Prefix.Completion.run
  | "termination" => phase name TestPurelib.Data.CCL.Encoding.Prefix.Termination.run
  | _ => throw (IO.userError (append "unknown cursor continuation case: " name))

/-- Execute every original regression group in its established order. -/
private def runAll : IO Unit := do
  for name in ["continuation", "retained-refinements", "source-refinement-requests", "handled-emissions",
      "handled-histories", "transition", "history", "cursor", "prefix", "family", "completion", "termination"] do
    runCase name

/-- Run all continuation regressions, or select one group for diagnosis. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["--case", name] => runCase name
  | [] => runAll
  | _ => throw (IO.userError "expected --case NAME or no arguments")
