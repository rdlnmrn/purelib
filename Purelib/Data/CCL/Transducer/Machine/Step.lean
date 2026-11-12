module
import Purelib.Data.CCL.Transducer.Emission.Basic
public import Purelib.Data.CCL.Transducer.Emission.Step
public import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.List.Basic
import Purelib.Data.List.Append

import Purelib.Tactic.QuotientFreeOmega

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Machine.Step

open Purelib.Data.List

section
open Purelib.Data.CCL.Transducer
open Purelib.Data.List
/-- Return the first bit of a certified nonempty emission and retain its exact next mode and remaining queue.

Append that same bit to the supplied emitted prefix. The retained nonempty certificate eliminates the empty branch
without adding a new decision or recomputing an emission. -/
@[expose] public def consumeEmission (emitted : Basic.BinaryWord) (emission : Emission) : Bool ×
  Machine :=
  match bitsEqual : emission.bits with
  | bit :: rest =>
      (bit,
        { mode := emission.next
          emitted := emitted ++ [bit]
          pending := rest })
  | [] => False.elim (emission.nonempty bitsEqual)

/-- Consuming a certified emission appends exactly the returned first bit to the retained emitted prefix.

The original nonempty chunk has a displayed first bit. Eliminating the
empty case leaves that exact bit and retained tail, so the emitted word
is the supplied prefix with the returned bit appended. -/
public theorem consumeEmission_emitted (emitted : Basic.BinaryWord) (emission : Emission) :
    (Machine.Step.consumeEmission emitted emission).2.emitted =
      emitted ++ [(Machine.Step.consumeEmission emitted emission).1] := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | cons bit rest => rfl
      | nil => exact (nonempty rfl).elim

/-- The returned first bit and retained pending queue reconstruct the exact original emitted chunk. -/
public theorem consumeEmission_chunk (emitted : Basic.BinaryWord) (emission : Emission) :
    (consumeEmission emitted emission).1 :: (consumeEmission emitted emission).2.pending = emission.bits := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | cons bit rest => rfl
      | nil => exact (nonempty rfl).elim

end

open Purelib.Data.CCL.Transducer
/-- Return the original queued head and next machine when a pending bit is available. -/
@[expose] public def pendingResult (machine : Machine) : Option (Bool × Machine) :=
  match machine.pending with
  | bit :: rest => some (bit,
      { mode := machine.mode
        emitted := machine.emitted ++ [bit]
        pending := rest })
  | [] => none

/-- Returning a retained queued bit leaves the original quantitative mode unchanged. -/
public theorem pendingResult_mode (machine : Machine) (result : Bool × Machine)
    (same : pendingResult machine = some result) : result.2.mode = machine.mode := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil => nomatch same
      | cons bit rest => cases same; rfl

/-- Return one pending bit, or compute and consume one exact emission when the retained queue is empty.

Both raw and cached execution use the same pending-result selector. An empty
queue advances through the original emission procedure once.
-/
@[expose] public def nextBit (machine : Machine) : Bool × Machine :=
  match pendingResult machine with
  | some result => result
  | none => consumeEmission machine.emitted (Emission.Step.step machine.mode)

/-- A machine step appends exactly its returned bit to the retained emitted prefix.

A nonempty retained queue returns its original head. An empty queue
consumes the exact selected emission; each case appends that same returned
bit to the original emitted prefix. -/
public theorem nextBit_emitted (machine : Machine) :
    (Machine.Step.nextBit machine).2.emitted =
      machine.emitted ++ [(Machine.Step.nextBit machine).1] := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | cons bit rest => rfl
      | nil =>
          exact Machine.Step.consumeEmission_emitted emitted (Emission.Step.step mode)

/-- A machine step increases the emitted prefix length by exactly one.

The returned bit is appended as a singleton to the same retained emitted
prefix. The structural length law therefore adds exactly one entry. -/
public theorem nextBit_length (machine : Machine) :
    (Machine.Step.nextBit machine).2.emitted.length = machine.emitted.length + 1 := by
  rw [Machine.Step.nextBit_emitted, Append.length_append]
  rfl

/-- Consuming a retained pending bit leaves the original quantitative mode unchanged. -/
public theorem nextBit_mode_of_pending (machine : Machine) (nonempty : machine.pending ≠ []) :
    (nextBit machine).2.mode = machine.mode := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil => exact (nonempty rfl).elim
      | cons bit rest => rfl

end Purelib.Data.CCL.Transducer.Machine.Step
