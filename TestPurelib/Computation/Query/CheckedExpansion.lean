module

import Purelib.Computation.Query.Program

/-! # Checked request expansion preserves order and stops at the actual failed handler -/

namespace TestPurelib.Computation.Query.CheckedExpansion

open Purelib.Computation.Query

/-- Expand one actual query through a checked reply, retaining the failed request's identity. -/
private def handler (question : Nat) : Protocol Nat Nat (Except Nat Nat) :=
  (Protocol.query question).map fun reply => if reply = 0 then .error question else .ok reply

/-- Execute reply-dependent checked expansion, successful replay and first-handler early failure. -/
public def run : IO Unit := do
  let program : Program Nat Nat Nat := (Program.query 1).bind fun first =>
    (Program.query (first + 1)).map fun second => first + second
  let computation := program.expandChecked handler
  let success := computation.run (fun question => question + 1)
  match success.value with
  | .ok outer =>
      unless outer.value == 6 && outer.trace.map (fun entry => entry.query) == [1, 3] &&
          success.trace.map (fun entry => entry.query) == [1, 3] do
        throw (IO.userError "checked expansion lost reply-dependent ordering or either complete request log")
      match computation.replayExact success.trace with
      | .ok (.ok replayed) =>
          unless replayed.value == outer.value && replayed.trace.length == outer.trace.length do
            throw (IO.userError "checked expansion replay changed its complete outer result")
      | _ => throw (IO.userError "checked expansion rejected its successful inner transcript")
  | .error _ => throw (IO.userError "checked expansion rejected actual successful handlers")
  let failure := computation.run (fun _ => 0)
  match failure.value with
  | .error question =>
      unless question == 1 && failure.trace.map (fun entry => entry.query) == [1] do
        throw (IO.userError "checked expansion executed a later handler after the first concrete failure")
  | .ok _ => throw (IO.userError "checked expansion suppressed its actual handler failure")
  IO.print "checked composition: adaptive success, exact replay and first-handler early failure passed\n"

end TestPurelib.Computation.Query.CheckedExpansion
