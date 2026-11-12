module

import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Data.Rat.Fraction.Cast

/-! # One final cursor witness realizes every original chronological enclosure -/

namespace TestPurelib.Data.CCL.Transducer.History

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Every actual finite history producer retains the exact requested numerical action path. -/
theorem requested_actions (initial : Machine.Snapshot) (actions : List Machine.Action) :
    ((Machine.History.start initial).execute actions).actions = actions :=
  ((Machine.History.start initial).execute_actions actions).trans
    (congrArg (fun earlier => earlier ++ actions) (Machine.History.start_actions initial))

/-- The computed realization at every retained occurrence satisfies that same original numerical ball. -/
theorem original_ball {initial : Machine.Snapshot} (history : Machine.History initial)
    (snapshot : Machine.Snapshot) (member : snapshot ∈ history.snapshots) :
    let survivor := history.survive
    snapshot.ball.Contains
      (history.realize snapshot member survivor.tail survivor.possible survivor.image survivor.imageEq).value :=
  (history.realize snapshot member history.survive.tail history.survive.possible
    history.survive.image history.survive.imageEq).inside

/-- The common rational history reading belongs to the exact original Gaussian source state for every action path. -/
theorem original_reading {initial : Machine.Snapshot} (history : Machine.History initial)
    {origin : Process} {originState : origin.State}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState initial.machine) :
    origin.Possible originState (history.survive.read cursor).value := (history.survive.read cursor).originalPossible

/-- Every finite later advance of an old snapshot's numerical code retains the common Gaussian reading exactly. -/
theorem future_reading {initial : Machine.Snapshot} {history : Machine.History initial}
    {survivor : Machine.History.Survivor history} {origin : Process} {originState : origin.State}
    (reading : Machine.History.Survivor.Reading survivor origin originState)
    {snapshot : Machine.Snapshot} (realization : Machine.History.Realization snapshot survivor.image) (count : Nat) :
    let continuation := realization.continueCursor
    Machine.Semantics.Basic.ExactCursor (Process.exact reading.value) ()
      (Machine.Advance.advance (continuation.description.code.interpret continuation.description.valid) count) :=
  (realization.continueCursor.exactCursor reading.value (reading.snapshot_represented realization)).advance count

/-- A strictly positive finite numerical target with its direct integer denominator. -/
private def target : Fraction.Rational := 1 / Fraction.Cast.fromInt 16

/-- Check the exact ordered history and every cached earlier numerical realization against one final image. -/
private def check (value : Basic.Canonical) (actions : List Machine.Action) : IO Unit := do
  let machine := Machine.initial (Process.exact value) ()
  let originalCursor := Machine.Semantics.Basic.ExactCursor.initial (Process.exact value) ()
  let frame := Cursor.Image.Machine.Frame.ofMachine machine
  let initial := Machine.Snapshot.ofFrame frame (Machine.Grammar.initial_invariant _ _)
  let history := (Machine.History.start initial).execute actions
  let survivor := history.survive
  let reading := survivor.read originalCursor
  unless decide (reading.value = value) && decide (survivor.image.q ≠ 0) do
    throw (IO.userError "shared history image lost its original Gaussian rational reading")
  unless history.actions.length == actions.length && history.snapshots.length == actions.length + 1 &&
      survivor.realizations.length == history.snapshots.length do
    throw (IO.userError "history or survivor lost an original chronological occurrence")
  unless decide (history.current.machine.emitted =
      (Machine.Action.run initial.machine actions).emitted) do
    throw (IO.userError "cached history producer changed the actual requested bit execution")
  for entry in survivor.realizations do
    unless decide (entry.1.ball.Contains entry.2.value) && decide (entry.2.pulled.q ≠ 0) do
      throw (IO.userError "final witness did not realize an original cached numerical ball")
    let image := entry.1.frame.image entry.2.value
    unless decide (survivor.image.p * image.q = image.p * survivor.image.q) do
      throw (IO.userError "an earlier retained chart changed the shared final projective reading")
    let continuation := entry.2.continueCursor
    let description := continuation.description
    let code := description.code
    let valid := description.valid
    unless decide (code.emitted = entry.1.machine.emitted) && decide (code.pending = entry.1.machine.pending) &&
        decide (code.parser = entry.1.frame.parser) && decide (code.matrix = entry.1.frame.matrix) &&
        decide (code.adjugate = entry.1.frame.adjugate) do
      throw (IO.userError "finite cursor description changed a saved word or original chart cache")
    let fresh := Machine.Snapshot.ofFrame (code.frame valid) (code.grammar valid)
    let future := (Machine.History.start fresh).execute (List.replicate 7 .bit)
    let futureImage := future.survive.image
    unless future.current.machine.emitted.length == code.emitted.length + 7 &&
        decide (future.current.machine.emitted.take code.emitted.length = code.emitted) &&
        decide (futureImage.p * survivor.image.q = survivor.image.p * futureImage.q) do
      throw (IO.userError "finite-data cursor continuation changed its earlier prefix or common reading")

/-- Run empty, singleton and mixed chronological bit/refinement histories for zero, one and two sources. -/
public def run : IO Unit := do
  check 0 []
  check 1 [.refine target (by decide)]
  let actions : List Machine.Action :=
    [.bit, .bit, .refine target (by decide), .bit, .bit, .bit, .refine target (by decide),
      .bit, .bit, .bit, .bit, .bit, .refine target (by decide)]
  check 0 actions
  check 1 actions
  check 2 actions
  IO.print "chronological cursor history: five histories realized every original ball from one final witness\n"

end TestPurelib.Data.CCL.Transducer.History
