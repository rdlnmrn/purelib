module

public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Schedule
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent persistent schedules at operationally compared channels

Each original cursor executes its own finite schedule once and keeps its own
prefix and parser origin. A supplied bit law compares the retained output
channels; the two independently emitted raw words remain separate.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor

open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Data.CCL.Transducer.Machine.Semantics.Basic (ExactCursor)

set_option genInjectivity false in
/-- Two cached independent schedule outputs, with their original bit law, prefix growth and exact parser origins. -/
structure ScheduleComparison (left right : ChannelCursor) (leftSchedule rightSchedule : List RequestStep) where
  /-- The entire first original cursor and its existing prefix. -/
  sourceLeft : ChannelCursor
  /-- The retained first cursor is the supplied original input. -/
  sourceLeft_eq : sourceLeft = left
  /-- The entire second original cursor and its existing prefix. -/
  sourceRight : ChannelCursor
  /-- The retained second cursor is the supplied original input. -/
  sourceRight_eq : sourceRight = right
  /-- The supplied operational law between these same original cursor channels. -/
  originalLaw : BitLaw left.channel right.channel
  /-- The actual first finite schedule retained with its requested tolerances and bit counts. -/
  requestsLeft : List RequestStep
  /-- The retained first schedule is the supplied original request. -/
  requestsLeft_eq : requestsLeft = leftSchedule
  /-- The actual second finite schedule retained with its requested tolerances and bit counts. -/
  requestsRight : List RequestStep
  /-- The retained second schedule is the supplied original request. -/
  requestsRight_eq : requestsRight = rightSchedule
  /-- The first actually executed finite schedule output. -/
  outputLeft : ChannelCursor
  /-- The first output consumes the first original cursor and its actual schedule. -/
  outputLeft_eq : outputLeft = left.run leftSchedule
  /-- The second actually executed finite schedule output. -/
  outputRight : ChannelCursor
  /-- The second output consumes the second original cursor and its actual schedule. -/
  outputRight_eq : outputRight = right.run rightSchedule
  /-- The comparison of the two actual output channels. -/
  law : BitLaw outputLeft.channel outputRight.channel
  /-- The first result extends its own original raw prefix. -/
  left_extends : left.cursor.machine.emitted.IsPrefix outputLeft.cursor.machine.emitted
  /-- The second result extends its own original raw prefix. -/
  right_extends : right.cursor.machine.emitted.IsPrefix outputRight.cursor.machine.emitted
  /-- The first schedule adds exactly its original requested bit count. -/
  left_length : outputLeft.cursor.machine.emitted.length =
    left.cursor.machine.emitted.length + scheduledBitCount leftSchedule
  /-- The second schedule adds exactly its original requested bit count. -/
  right_length : outputRight.cursor.machine.emitted.length =
    right.cursor.machine.emitted.length + scheduledBitCount rightSchedule
  /-- The first result retains exact parser semantics at its own original dependent state. -/
  left_exact : ExactCursor left.channel.name.process left.rootState outputLeft.cursor.machine
  /-- The second result retains exact parser semantics at its own original dependent state. -/
  right_exact : ExactCursor right.channel.name.process right.rootState outputRight.cursor.machine

constructive_injectivity ScheduleComparison

/-- Execute both original finite schedules once and retain their law, independent prefixes and parser certificates. -/
@[noinline, nospecialize] def compareSchedules (left right : ChannelCursor)
    (law : BitLaw left.channel right.channel) (leftSchedule rightSchedule : List RequestStep) :
    ScheduleComparison left right leftSchedule rightSchedule := by
  let outputLeft := left.run leftSchedule
  let outputRight := right.run rightSchedule
  have compared := law.equivalent
  rewrite [← left.run_channel leftSchedule, ← right.run_channel rightSchedule] at compared
  exact
    { sourceLeft := left
      sourceLeft_eq := rfl
      sourceRight := right
      sourceRight_eq := rfl
      originalLaw := law
      requestsLeft := leftSchedule
      requestsLeft_eq := rfl
      requestsRight := rightSchedule
      requestsRight_eq := rfl
      outputLeft := outputLeft
      outputLeft_eq := rfl
      outputRight := outputRight
      outputRight_eq := rfl
      law := BitLaw.ofEquivalent compared
      left_extends := left.run_word_extends leftSchedule
      right_extends := right.run_word_extends rightSchedule
      left_length := left.run_word_length leftSchedule
      right_length := right.run_word_length rightSchedule
      left_exact := left.run_exact leftSchedule
      right_exact := right.run_exact rightSchedule }

end Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic.ChannelCursor

end
