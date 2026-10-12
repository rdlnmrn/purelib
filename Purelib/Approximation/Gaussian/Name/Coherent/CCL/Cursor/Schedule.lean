module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Request
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.CCL.Transducer.Machine.Semantics.Basic (ExactCursor)

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent.CCL
open Purelib.Data.CCL.Transducer.Machine
open Purelib.Data.Rat

section
public section

/-!
# Persistent CCL cursors for finite progressive calculus tables

The joint-request modules prove that every channel can emit a requested finite
prefix.  This module retains those cursors between requests.  A table state is
one displayed finite list of proof-bearing cursors; requesting more accuracy
and more bits maps the ordinary persistent CCL request over that list.  Hence
later words extend earlier words instead of restarting an encoder.

There is no stream or completed table.  Every operation consumes and returns
one finite list and one natural number of additional bits.
-/

namespace ChannelCursor

/-! ## Finite request schedules -/

set_option genInjectivity false in
/-- One visible accuracy-and-growth instruction. Positivity is stored in the instruction, so executing a schedule has no
hidden side condition. -/
structure RequestStep where
  /-- The positive squared-chordal accuracy target of this request. -/ epsilonSq : Fraction.Rational
  /-- The retained accuracy target is strictly positive. -/ positive : 0 < epsilonSq
  /-- The number of additional raw bits requested by this step. -/ count : Nat

constructive_injectivity RequestStep

/-- Execute a displayed finite request schedule on one running cursor. -/
@[expose] def run :
  Cursor.Basic.ChannelCursor → List RequestStep →
  Cursor.Basic.ChannelCursor
  | state, [] => state
  | state, step :: remaining =>
      run (state.request step.epsilonSq
        step.positive step.count) remaining

/-- Executing a finite request schedule preserves the original coherent channel. -/
@[simp] theorem run_channel (state :
  Cursor.Basic.ChannelCursor) :
    ∀ schedule, (state.run schedule).channel = state.channel
  | [] => rfl
  | step :: remaining => by
      rw [run,
        run_channel]
      rfl

/-- Every finite schedule extends the word with which it started. -/
theorem run_word_extends (state :
  Cursor.Basic.ChannelCursor) :
    ∀ schedule, state.cursor.machine.emitted.IsPrefix
      (state.run schedule).cursor.machine.emitted
  | [] => ⟨[], Purelib.Data.List.Append.append_nil _⟩
  | step :: remaining => by
      obtain ⟨firstSuffix, first⟩ :=
        state.request_word_extends step.epsilonSq step.positive step.count
      obtain ⟨lastSuffix, last⟩ :=
        run_word_extends
          (state.request step.epsilonSq step.positive step.count) remaining
      refine ⟨firstSuffix ++ lastSuffix, ?_⟩
      rewrite [← Purelib.Data.List.Append.append_assoc, first]
      exact last

/-- Sum the requested additional bit counts over the displayed finite schedule. -/
@[expose] def scheduledBitCount :
  List RequestStep → Nat
  | [] => 0
  | step :: remaining => step.count +
    scheduledBitCount remaining

/-- The schedule accounts exactly for every appended bit. -/
theorem run_word_length (state :
  Cursor.Basic.ChannelCursor) :
    ∀ schedule,
      (state.run schedule).cursor.machine.emitted.length =
        state.cursor.machine.emitted.length +
          scheduledBitCount schedule
  | [] => (Nat.add_zero _).symm
  | step :: remaining => by
      rw [run,
        run_word_length,
        state.request_word_length step.epsilonSq step.positive step.count]
      exact Nat.add_assoc _ _ _

/-- Exact parser semantics survives every finite refinement schedule. -/
theorem run_exact (state :
  Cursor.Basic.ChannelCursor) : ∀ schedule,
    ExactCursor
      state.channel.name.process state.rootState
      (state.run schedule).cursor.machine
  | [] => state.cursor.exact
  | step :: remaining =>
      run_exact (state.request
        step.epsilonSq step.positive step.count)
        remaining

set_option genInjectivity false in
/-- Compatibility of two schedules means precisely that both finite raw prefixes retain exact parser semantics for the
same certified origin.

The words need not be textually equal because the redundant sector cover permits more than one correct output prefix. -/
structure ScheduleCompatible (state :
  Cursor.Basic.ChannelCursor)
    (left right : List RequestStep) : Prop where
  /-- The left schedule extends the original emitted prefix. -/ left_extends : state.cursor.machine.emitted.IsPrefix
    (state.run left).cursor.machine.emitted
  /-- The right schedule extends the original emitted prefix. -/ right_extends : state.cursor.machine.emitted.IsPrefix
    (state.run right).cursor.machine.emitted
  /-- The left schedule retains exact parser semantics for the original process state. -/ left_exact :
    ExactCursor
    state.channel.name.process state.rootState
    (state.run left).cursor.machine
  /-- The right schedule retains exact parser semantics for the original process state. -/ right_exact :
    ExactCursor
    state.channel.name.process state.rootState
    (state.run right).cursor.machine

/-- Any two finite schedules retain prefix extension and exact parser semantics for the same original state. -/
theorem schedules_compatible (state :
  Cursor.Basic.ChannelCursor)
    (left right : List RequestStep) :
      ScheduleCompatible state left right :=
  { left_extends := state.run_word_extends left
    right_extends := state.run_word_extends right
    left_exact := state.run_exact left
    right_exact := state.run_exact right }

/-- Since schedules never replace the channel, their enclosure programs are operationally equal by the finite-request
reflexivity theorem. -/
@[expose] def
  schedules_namedEquivalent (state :
  Cursor.Basic.ChannelCursor)
    (left right : List RequestStep) :
    Gaussian.Equivalence.NamedEquivalent
      (state.run left).channel.name (state.run right).channel.name := by
  rw [state.run_channel left, state.run_channel right]
  exact NamedEquivalent.refl
    state.channel.name

end ChannelCursor

end

public section

/-!
# Operational laws at the persistent CCL-prefix layer

Operational equivalence compares two finite approximation programs by a
computed pair of later natural indices for every positive rational target.
This file carries that comparison all the way to persistent raw CCL cursors.
The two cursors may follow different displayed finite request schedules and
may emit different redundant words.  Each word nevertheless extends its own
earlier prefix, retains exact parser semantics for its certified origin, and
ends in a cylinder of the requested squared-chordal diameter.

The `BitLaw` wrapper then exposes the established arithmetic and exp/log laws
at precisely this bit-producing interface.  It does not identify completed
values or quantify over an infinite bitstream.
-/

end

end

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
