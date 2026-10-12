module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Schedule
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Request
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.CCL.Transducer.Machine.Semantics.Basic (ExactCursor)
open Purelib.Data.Gaussian.Basic (Canonical)

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
open Purelib.Data.CCL.Progressive.Cursor.Image
open Purelib.Data.CCL.Transducer.Machine
open Purelib.Data.CCL.Transducer.Mode.Semantics
open Purelib.Data.Rat
open Purelib.Geometry.Projective

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

section

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Request.ChannelCursor

/-- Run an arbitrary finite schedule and then make one common accuracy and bit-growth request.

The last request gives both schedules a directly comparable displayed cylinder bound. -/
@[expose] def scheduledRequest (cursor : ChannelCursor) (schedule : List
  ChannelCursor.RequestStep)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    ChannelCursor :=
  (cursor.run schedule).request target positive count

/-- A finite schedule followed by the common final request extends the original raw prefix. -/
theorem scheduledRequest_extends (cursor : ChannelCursor)
    (schedule : List ChannelCursor.RequestStep) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    cursor.cursor.machine.emitted.IsPrefix
      (scheduledRequest cursor schedule target positive
        count).cursor.machine.emitted :=
  by
    obtain ⟨firstSuffix, first⟩ := cursor.run_word_extends schedule
    obtain ⟨lastSuffix, last⟩ :=
      (cursor.run schedule).request_word_extends target positive count
    refine ⟨firstSuffix ++ lastSuffix, ?_⟩
    rewrite [← Purelib.Data.List.Append.append_assoc, first]
    exact last

/-- The scheduled request appends exactly the schedule's total bit count and the final requested count. -/
theorem scheduledRequest_length (cursor : ChannelCursor)
    (schedule : List ChannelCursor.RequestStep) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    (scheduledRequest cursor schedule target
      positive count).cursor.machine.emitted.length =
      cursor.cursor.machine.emitted.length +
        ChannelCursor.scheduledBitCount
          schedule + count := by
  unfold scheduledRequest
  rw [(cursor.run schedule).request_word_length target positive count,
    cursor.run_word_length schedule]

/-- The scheduled request retains exact parser semantics for the original process and root state. -/
theorem scheduledRequest_exact (cursor : ChannelCursor)
    (schedule : List ChannelCursor.RequestStep) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    ExactCursor cursor.channel.name.process cursor.rootState
      (scheduledRequest cursor schedule target
        positive count).cursor.machine := by
  induction schedule generalizing cursor with
  | nil => exact cursor.request_exact target positive count
  | cons step remaining induction =>
      unfold scheduledRequest
      change ExactCursor cursor.channel.name.process cursor.rootState
        (((cursor.request step.epsilonSq step.positive step.count).run
          remaining).request target positive count).cursor.machine
      exact induction (cursor := cursor.request step.epsilonSq step.positive
        step.count)

/-- Any two readings admitted by the final scheduled cursor have squared-chordal separation bounded by the requested
target. -/
theorem scheduledRequest_pair_chordalSq_le (cursor : ChannelCursor)
    (schedule : List ChannelCursor.RequestStep) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) {left right : Canonical}
    (leftPossible : SemanticMode.possible
      (scheduledRequest cursor schedule target
        positive count).cursor.machine.mode
        left)
    (rightPossible : SemanticMode.possible
      (scheduledRequest cursor schedule target
        positive count).cursor.machine.mode
        right) :
    Chordal.Basic.chordalSq
        (Machine.image (scheduledRequest cursor
          schedule target positive count).cursor.machine left)
        (Machine.image (scheduledRequest cursor
          schedule target positive count).cursor.machine right) ≤ target := by
  unfold scheduledRequest at leftPossible rightPossible ⊢
  exact (cursor.run schedule).request_pair_chordalSq_le target positive count
    leftPossible rightPossible

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Request.ChannelCursor

end

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Request

set_option genInjectivity false in
/-- Compatibility of persistent computations rooted in two operationally equivalent channels.

Redundant output words need not be textually equal; the exact-parser fields say what each finite word denotes, while
`comparison` computes a common later rational comparison below the requested target. -/
structure CompatibleRequests (left right : ChannelCursor)
    (leftSchedule rightSchedule : List ChannelCursor.RequestStep)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) : Type where
  /-- The left scheduled request extends its original raw prefix. -/ left_extends : left.cursor.machine.emitted.IsPrefix
    (ChannelCursor.scheduledRequest left leftSchedule target positive
      count).cursor.machine.emitted
  /-- The right scheduled request extends its original raw prefix. -/ right_extends :
    right.cursor.machine.emitted.IsPrefix
    (ChannelCursor.scheduledRequest right rightSchedule target positive
      count).cursor.machine.emitted
  /-- The left cursor retains the exact sum of its original, scheduled and final bit counts. -/ left_length :
    (ChannelCursor.scheduledRequest left leftSchedule target positive
      count).cursor.machine.emitted.length =
      left.cursor.machine.emitted.length +
        ChannelCursor.scheduledBitCount
          leftSchedule + count
  /-- The right cursor retains the exact sum of its original, scheduled and final bit counts. -/ right_length :
    (ChannelCursor.scheduledRequest right rightSchedule target positive
      count).cursor.machine.emitted.length =
      right.cursor.machine.emitted.length +
        ChannelCursor.scheduledBitCount
          rightSchedule + count
  /-- The left final cursor has exact parser semantics for its original process and root state. -/ left_exact :
    ExactCursor left.channel.name.process left.rootState
    (ChannelCursor.scheduledRequest left leftSchedule target positive
      count).cursor.machine
  /-- The right final cursor has exact parser semantics for its original process and root state. -/ right_exact :
    ExactCursor right.channel.name.process right.rootState
    (ChannelCursor.scheduledRequest right rightSchedule target positive
      count).cursor.machine
  /-- All pairs of readings admitted by the left final cursor satisfy the requested squared-chordal bound. -/
    left_cylinder : ∀ {first second : Canonical},
    SemanticMode.possible
        (ChannelCursor.scheduledRequest left leftSchedule target
          positive count).cursor.machine.mode
          first →
      SemanticMode.possible
        (ChannelCursor.scheduledRequest left leftSchedule target
          positive count).cursor.machine.mode
          second →
      Chordal.Basic.chordalSq
          (Machine.image (ChannelCursor.scheduledRequest left
            leftSchedule target positive count).cursor.machine first)
          (Machine.image (ChannelCursor.scheduledRequest left
            leftSchedule target positive count).cursor.machine second) ≤ target
  /-- All pairs of readings admitted by the right final cursor satisfy the requested squared-chordal bound. -/
    right_cylinder : ∀ {first second : Canonical},
    SemanticMode.possible
        (ChannelCursor.scheduledRequest right rightSchedule target
          positive count).cursor.machine.mode
          first →
      SemanticMode.possible
        (ChannelCursor.scheduledRequest right rightSchedule target
          positive count).cursor.machine.mode
          second →
      Chordal.Basic.chordalSq
          (Machine.image (ChannelCursor.scheduledRequest right
            rightSchedule target positive count).cursor.machine first)
          (Machine.image (ChannelCursor.scheduledRequest right
            rightSchedule target positive count).cursor.machine second) ≤ target
  /-- A finite operational comparison of the two original sampled channels beyond their schedule-index floors and below
    the common target. -/ comparison : Gaussian.Equivalence.Comparison
    (Sampling.approximation left.channel.name)
    (Sampling.approximation right.channel.name)
    (ChannelCursor.scheduledBitCount
      leftSchedule)
    (ChannelCursor.scheduledBitCount
      rightSchedule)
    target

constructive_injectivity CompatibleRequests

/-- Operationally equivalent origins remain compatible after independently chosen finite schedules and one common final
request. -/
@[expose] def compatibleRequests_of_equivalent (left right : ChannelCursor)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.channel.name right.channel.name)
    (leftSchedule rightSchedule : List ChannelCursor.RequestStep)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    CompatibleRequests left right leftSchedule rightSchedule target
      positive
      count :=
  { left_extends := ChannelCursor.scheduledRequest_extends left
      leftSchedule target positive count
    right_extends := ChannelCursor.scheduledRequest_extends right
      rightSchedule target positive count
    left_length := ChannelCursor.scheduledRequest_length left
      leftSchedule target positive count
    right_length := ChannelCursor.scheduledRequest_length right
      rightSchedule target positive count
    left_exact := ChannelCursor.scheduledRequest_exact left
      leftSchedule target positive count
    right_exact := ChannelCursor.scheduledRequest_exact right
      rightSchedule target positive count
    left_cylinder := by
      intro first second firstPossible secondPossible
      exact ChannelCursor.scheduledRequest_pair_chordalSq_le left
        leftSchedule target positive
        count firstPossible secondPossible
    right_cylinder := by
      intro first second firstPossible secondPossible
      exact ChannelCursor.scheduledRequest_pair_chordalSq_le right
        rightSchedule target positive
        count firstPossible secondPossible
    comparison := equivalent.compare
      (ChannelCursor.scheduledBitCount
        leftSchedule)
      (ChannelCursor.scheduledBitCount
        rightSchedule)
      target positive }

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Request

section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic.BitLaw

open Purelib.Approximation.Gaussian.Name.Coherent.CCL

/-- Every law can be executed under different finite schedules. -/
@[expose] def request {left right :
  CoherentNamed} (law : Law.Basic.BitLaw left right)
    (leftSchedule rightSchedule : List ChannelCursor.RequestStep)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    Request.CompatibleRequests
      (ChannelCursor.initial left)
      (ChannelCursor.initial right)
      leftSchedule rightSchedule target positive count :=
  Request.compatibleRequests_of_equivalent _ _ law.equivalent leftSchedule
    rightSchedule target positive count

end Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic.BitLaw

end

end

end
