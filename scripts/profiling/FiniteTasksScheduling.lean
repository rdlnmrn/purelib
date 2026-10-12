module
public import Purelib.Data.UInt64.Basic
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.Range

public import Purelib.Data.Task.Parallel
import Init.Control.Id
import Init.Core
import Init.Prelude
public import Init.System.IO
import Init.System.IOError
import Init.Util

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Range

open Purelib.Data.Task

public section

/-!
Short native scheduling regression, independent of all period certificates.
The `pooled` and `dedicated` modes first warm two shared-pool workers, then
submit four traced two-second jobs.  `cold` omits the warm-up.  The production
helper must retain the ordered results; the start/end trace exposes actual
overlap without treating wall time on a shared host as a correctness gate.
`cpu ROUNDS` runs four independent integer loops for CPU-usage sampling.
Run diagnostics with an explicit SIGKILL timeout and systemd memory bound.
-/

namespace FiniteTasksSchedulingHarness

/-- Evaluate an executable thunk through IO without inlining the evaluation boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Trace the start and completion of a delayed job while returning its retained result. -/
@[noinline, expose] def sleepingJob (label : String) (delay : UInt32) (result : Nat) : Nat :=
  dbgTrace s!"START {label}" fun _ =>
    dbgSleep delay fun _ => dbgTrace s!"END {label}" fun _ => result

-- Keep the old launch strategy only as a diagnostic control, not a second
-- production implementation.  This reproduces a warmed, underfilled pool.
/-- Run four jobs through the shared task pool and retain their original result order.

This diagnostic control preserves the older launch strategy for comparison with dedicated workers. -/
@[expose] def pooledFour (first second third fourth : Unit → Nat) : Nat × Nat × Nat × Nat :=
  let one := Task.spawn first
  let two := Task.spawn second
  let three := Task.spawn third
  let four := Task.spawn fourth
  (one.bind (fun a => two.bind (fun b => three.bind (fun c =>
    four.map (fun d => (a, b, c, d)) (sync := true)) (sync := true))
    (sync := true)) (sync := true)).get

/-- Warm two shared-pool workers and verify their result order. -/
@[expose] def warm : IO Unit := do
  let result ← evaluate fun _ =>
    let one := Task.spawn fun _ => sleepingJob "warm-left" 100 1
    let two := Task.spawn fun _ => sleepingJob "warm-right" 100 2
    (one.bind (fun a => two.map (fun b => (a, b)) (sync := true)) (sync := true)).get
  unless result == (1, 2) do throw (IO.userError "warm-up results reordered")
  IO.sleep 20

/-- Run the selected four-job scheduling diagnostic and check its exact ordered results. -/
@[expose] def sleeping (mode : String) : IO Unit := do
  if mode != "cold" then warm
  let group := if mode == "dedicated" then Parallel.four else pooledFour
  let started ← IO.monoMsNow
  let result ← evaluate fun _ => group
    (fun _ => sleepingJob s!"{mode}-first" 2000 1)
    (fun _ => sleepingJob s!"{mode}-second" 2000 2)
    (fun _ => sleepingJob s!"{mode}-third" 2000 3)
    (fun _ => sleepingJob s!"{mode}-fourth" 2000 4)
  unless result == (1, 2, 3, 4) do throw (IO.userError "four-job results reordered")
  Purelib.System.IO.println s!"ordered results {result}; elapsed={(← IO.monoMsNow) - started}ms"

/-- Iterate the deterministic UInt64 workload from the supplied seed. -/
@[noinline, expose] def integerWork (rounds : Nat) (seed : UInt64) : UInt64 := Id.run do
  let mut state := seed
  for _ in [:rounds] do
    state := (Purelib.Data.UInt64.xor state (Purelib.Data.UInt64.shiftRight state 17)) * 6364136223846793005 +
      1442695040888963407
  return state

/-- Trace one deterministic integer workload and return its final state. -/
@[noinline, expose] def cpuJob (rounds : Nat) (seed : UInt64) : UInt64 :=
  dbgTrace s!"START cpu-{seed}" fun _ =>
    let result := integerWork rounds seed
    dbgTrace s!"END cpu-{seed}: {result}" fun _ => result

/-- Run four independent seeded integer workloads and report their ordered results and elapsed time. -/
@[expose] def cpu (rounds : Nat) : IO Unit := do
  warm
  let started ← IO.monoMsNow
  let result ← evaluate fun _ => Parallel.four
    (fun _ => cpuJob rounds 1) (fun _ => cpuJob rounds 2)
    (fun _ => cpuJob rounds 3) (fun _ => cpuJob rounds 4)
  Purelib.System.IO.println s!"CPU diagnostic results {result}; elapsed={(← IO.monoMsNow) - started}ms"

end FiniteTasksSchedulingHarness

/-- Parse the scheduling mode or CPU round count and run the selected diagnostic. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | [mode] =>
      if mode == "cold" || mode == "pooled" || mode == "dedicated" then
        FiniteTasksSchedulingHarness.sleeping mode
      else throw (IO.userError "mode must be cold, pooled or dedicated")
  | ["cpu", count] =>
      let some rounds := Purelib.Data.String.toNat? count | throw (IO.userError "rounds must be a natural number")
      FiniteTasksSchedulingHarness.cpu rounds
  | _ => throw (IO.userError "usage: finite_tasks_scheduling_harness cold|pooled|dedicated | cpu ROUNDS")
