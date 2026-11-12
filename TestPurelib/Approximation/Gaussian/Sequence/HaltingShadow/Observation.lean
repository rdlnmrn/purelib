module

import Purelib.Approximation.Gaussian.Sequence.HaltingShadow.Observation

/-! # Finite indexed numerical traces admit a distinct later-halting shadow with the same complete execution -/

namespace TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Observation

open Purelib
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence.HaltingShadow

/-- Compare complete indexed numerical traces, retaining all original and repeated query occurrences. -/
private def sameTrace : Basic.Trace Nat Enclosure.Ball → Basic.Trace Nat Enclosure.Ball → Bool
  | [], [] => true
  | first :: remaining, second :: later => first.query == second.query && decide (first.reply = second.reply) &&
      sameTrace remaining later
  | _, _ => false

/-- Fixed control selects a later bound from the first numerical reply and repeats its original query. -/
private def adaptive : Protocol Nat Enclosure.Ball Nat :=
  (Protocol.query 2).bind fun first =>
    (Protocol.query (if decide (first.radiusSq < 1 / 32) then 5 else 7)).bind fun second =>
      (Protocol.query 2).map fun repeated => if decide (repeated.center = second.center) then 1 else 0

/-- Compare the complete run with its actual later-halting counterpart after computing the original trace once. -/
private def check (protocol : Protocol Nat Enclosure.Ball Nat) : IO Unit := do
  let input := Machine.Value.number 7
  let original := Code.ofProgram Machine.Program.loop input
  let execution := protocol.run original.observe
  let bound := Sequence.HaltingShadow.Observation.traceBound execution.trace
  let delayed := Code.ofProgram (Machine.Program.delay bound) input
  let later := protocol.run delayed.observe
  unless execution.value == later.value && sameTrace execution.trace later.trace do
    throw (IO.userError "later-halting shadow changed the complete actual adaptive numerical execution")
  unless delayed.firstHalt bound == none && delayed.firstHalt (bound + 1) == some (bound + 1) do
    throw (IO.userError "delayed shadow did not halt strictly after every original query bound")
  for entry in execution.trace do
    unless entry.query ≤ bound && decide (delayed.observe entry.query = entry.reply) do
      throw (IO.userError "delayed shadow lost an original or repeated numerical reply")
  let point := delayed.sample (bound + 1)
  unless decide (0 < Data.Gaussian.Norm.Basic.normSq point) do
    throw (IO.userError "later-halting shadow failed its actual positive future sample")

/-- Check empty, single-query and adaptive repeated-query executions with actual later-halting counterparts. -/
public def run : IO Unit := do
  check (Protocol.pure 7)
  check ((Protocol.query 0).map fun _ => 7)
  check adaptive
  IO.print "finite-query shadows: empty, stage-zero and adaptive repeated traces agree with later-halt programs\n"

end TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow.Observation
