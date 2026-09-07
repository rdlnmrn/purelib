import mathlib.Data.ConstructiveList
import CCL.Persistent.Progressive
import CCL.Progressive.HigherJet

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

namespace CCL.ProgressivePersistentTable

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Cursor := CCL.PersistentProgressive.Cursor

open CCL.ProgressiveMachineSemantics

/-- One coherent channel together with the running raw CCL cursor rooted at
that channel's certified initial process state. -/
structure ChannelCursor where
  channel : CoherentNamed
  rootState : channel.name.process.State
  cursor : Cursor channel.name.process rootState

namespace ChannelCursor

def initial (channel : CoherentNamed) : ChannelCursor :=
  { channel := channel
    rootState := channel.name.state
    cursor := CCL.PersistentProgressive.Cursor.initial
      channel.name.process channel.name.state }

/-- Start a persistent cursor at an explicitly displayed state of the same
coherent process.  This is used by synchronized traces to start all channels
at one common natural refinement index. -/
def atState (channel : CoherentNamed) (state : channel.name.process.State) :
    ChannelCursor :=
  { channel := channel
    rootState := state
    cursor := CCL.PersistentProgressive.Cursor.initial
      channel.name.process state }

/-- Append `count` bits to the existing word, then refine the same live
quantitative sidecar to the displayed squared-chordal target. -/
def request (state : ChannelCursor) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) : ChannelCursor :=
  { channel := state.channel
    rootState := state.rootState
    cursor := state.cursor.request epsilonSq positive count }

@[simp] theorem request_channel (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).channel = state.channel := rfl

theorem request_word_extends (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    state.cursor.machine.emitted.IsPrefix
      (state.request epsilonSq positive count).cursor.machine.emitted :=
  state.cursor.request_extends epsilonSq positive count

theorem request_word_length (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).cursor.machine.emitted.length =
      state.cursor.machine.emitted.length + count :=
  state.cursor.request_length epsilonSq positive count

/-- The refined raw prefix still has exact parser semantics for the original
certified channel state. -/
theorem request_exact (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      state.channel.name.process state.rootState
      (state.request epsilonSq positive count).cursor.machine :=
  (state.request epsilonSq positive count).cursor.exact

/-- Thus every tail admitted by the later prefix reconstructs an explicitly
possible reading of the original coherent channel. -/
theorem request_represents_origin (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat)
    {tail : Gaussian}
    (possible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode tail) :
    ∃ value : Gaussian,
      state.channel.name.process.Possible state.rootState value ∧
        (CCL.Mat2.act
          (CCL.RawParser.parse
            (CCL.ProgressiveTransducerGrammar.Machine.committed
              (state.request epsilonSq positive count).cursor.machine)).matrix
          (SemanticMode.parserTail
            (state.request epsilonSq positive count).cursor.machine.mode tail)).Equivalent
          (CCL.Proj.affine value) :=
  (state.request_exact epsilonSq positive count).exact possible

/-- Every two readings still admitted by the later prefix lie in a
squared-chordal cylinder of the requested diameter. -/
theorem request_pair_chordalSq_le (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat)
    {left right : Gaussian}
    (leftPossible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode left)
    (rightPossible : SemanticMode.possible
      (state.request epsilonSq positive count).cursor.machine.mode right) :
    CCL.Chordal.chordalSq
        ((state.request epsilonSq positive count).cursor.machine.image left)
        ((state.request epsilonSq positive count).cursor.machine.image right) ≤
      epsilonSq :=
  state.cursor.request_pair_chordalSq_le epsilonSq positive count
    leftPossible rightPossible

/-- A one-bit request is always another finite productive step. -/
theorem request_one_grows (state : ChannelCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) :
    (state.request epsilonSq positive 1).cursor.machine.emitted.length =
      state.cursor.machine.emitted.length + 1 :=
  state.request_word_length epsilonSq positive 1

/-! ## Finite request schedules -/

/-- One visible accuracy-and-growth instruction.  Positivity is stored in the
instruction, so executing a schedule has no hidden side condition. -/
structure RequestStep where
  epsilonSq : Coordinate
  positive : 0 < epsilonSq
  count : Nat

/-- Execute a displayed finite request schedule on one running cursor. -/
def run : ChannelCursor → List RequestStep → ChannelCursor
  | state, [] => state
  | state, step :: remaining =>
      run (state.request step.epsilonSq step.positive step.count) remaining

@[simp] theorem run_channel (state : ChannelCursor) :
    ∀ schedule, (state.run schedule).channel = state.channel
  | [] => rfl
  | step :: remaining => by
      rw [run, run_channel]
      rfl

/-- Every finite schedule extends the word with which it started. -/
theorem run_word_extends (state : ChannelCursor) :
    ∀ schedule, state.cursor.machine.emitted.IsPrefix
      (state.run schedule).cursor.machine.emitted
  | [] => List.prefix_refl _
  | step :: remaining =>
      (state.request_word_extends step.epsilonSq step.positive step.count).trans
        (run_word_extends
          (state.request step.epsilonSq step.positive step.count) remaining)

def scheduledBitCount : List RequestStep → Nat
  | [] => 0
  | step :: remaining => step.count + scheduledBitCount remaining

/-- The schedule accounts exactly for every appended bit. -/
theorem run_word_length (state : ChannelCursor) :
    ∀ schedule,
      (state.run schedule).cursor.machine.emitted.length =
        state.cursor.machine.emitted.length + scheduledBitCount schedule
  | [] => by simp only [run, scheduledBitCount, Nat.add_zero]
  | step :: remaining => by
      rw [run, run_word_length,
        state.request_word_length step.epsilonSq step.positive step.count]
      simp only [scheduledBitCount, Nat.add_assoc]

/-- Exact parser semantics survives every finite refinement schedule. -/
theorem run_exact (state : ChannelCursor) : ∀ schedule,
    CCL.ProgressiveMachineSemantics.ExactCursor
      state.channel.name.process state.rootState
      (state.run schedule).cursor.machine
  | [] => state.cursor.exact
  | step :: remaining =>
      run_exact (state.request step.epsilonSq step.positive step.count)
        remaining

/-- Compatibility of two schedules means precisely that both finite raw
prefixes retain exact parser semantics for the same certified origin.  The
words need not be textually equal because the redundant sector cover permits
more than one correct output prefix. -/
structure ScheduleCompatible (state : ChannelCursor)
    (left right : List RequestStep) : Prop where
  left_extends : state.cursor.machine.emitted.IsPrefix
    (state.run left).cursor.machine.emitted
  right_extends : state.cursor.machine.emitted.IsPrefix
    (state.run right).cursor.machine.emitted
  left_exact : CCL.ProgressiveMachineSemantics.ExactCursor
    state.channel.name.process state.rootState
    (state.run left).cursor.machine
  right_exact : CCL.ProgressiveMachineSemantics.ExactCursor
    state.channel.name.process state.rootState
    (state.run right).cursor.machine

theorem schedules_compatible (state : ChannelCursor)
    (left right : List RequestStep) : ScheduleCompatible state left right :=
  { left_extends := state.run_word_extends left
    right_extends := state.run_word_extends right
    left_exact := state.run_exact left
    right_exact := state.run_exact right }

/-- Since schedules never replace the channel, their enclosure programs are
operationally equal by the finite-request reflexivity theorem. -/
def schedules_namedEquivalent (state : ChannelCursor)
    (left right : List RequestStep) :
    CCL.OperationalEquivalence.NamedEquivalent
      (state.run left).channel.name (state.run right).channel.name := by
  rw [state.run_channel left, state.run_channel right]
  exact CCL.OperationalEquivalence.NamedEquivalent.refl
    state.channel.name

end ChannelCursor

/-- Running cursors for one explicitly displayed finite channel table. -/
structure TableCursor where
  entries : List ChannelCursor

namespace TableCursor

def channels (state : TableCursor) : List CoherentNamed :=
  state.entries.map ChannelCursor.channel

def initial (channels : List CoherentNamed) : TableCursor :=
  ⟨channels.map ChannelCursor.initial⟩

/-- Make the same finite accuracy and bit-growth request of every displayed
table entry. -/
def request (state : TableCursor) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) : TableCursor :=
  ⟨state.entries.map
    (fun entry => entry.request epsilonSq positive count)⟩

@[simp] theorem initial_channels (source : List CoherentNamed) :
    (initial source).channels = source := by
  simp only [initial, channels, List.map_map, Function.comp_def,
    ChannelCursor.initial]
  induction source with
  | nil => rfl
  | cons channel channels inductionHypothesis =>
      rw [List.map_cons, inductionHypothesis]

@[simp] theorem request_channels (state : TableCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).channels = state.channels := by
  unfold request channels
  simp only [List.map_map, Function.comp_def, ChannelCursor.request]

@[simp] theorem request_length (state : TableCursor)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (state.request epsilonSq positive count).entries.length =
      state.entries.length := by
  simp only [request, List.length_map]

/-- The exact updated entry corresponding to every old displayed member is
present in the returned finite table. -/
theorem requested_entry_mem (state : TableCursor) {entry : ChannelCursor}
    (member : entry ∈ state.entries) (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    entry.request epsilonSq positive count ∈
      (state.request epsilonSq positive count).entries := by
  exact QuotientFreeList.mem_map.mpr ⟨entry, member, rfl⟩

/-- Per-entry persistent output contract for a finite table request. -/
theorem member_word_extends_and_grows (state : TableCursor)
    {entry : ChannelCursor} (member : entry ∈ state.entries)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    entry.request epsilonSq positive count ∈
        (state.request epsilonSq positive count).entries ∧
      entry.cursor.machine.emitted.IsPrefix
        (entry.request epsilonSq positive count).cursor.machine.emitted ∧
      (entry.request epsilonSq positive count).cursor.machine.emitted.length =
        entry.cursor.machine.emitted.length + count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        entry.channel.name.process entry.rootState
        (entry.request epsilonSq positive count).cursor.machine :=
  ⟨state.requested_entry_mem member epsilonSq positive count,
    entry.request_word_extends epsilonSq positive count,
    entry.request_word_length epsilonSq positive count,
    entry.request_exact epsilonSq positive count⟩

/-- Successive table requests preserve all old channels and extend the
already-emitted word of every current entry. -/
theorem successive_member_extends (state : TableCursor)
    {entry : ChannelCursor} (member : entry ∈ state.entries)
    (firstTarget : Coordinate) (firstPositive : 0 < firstTarget)
    (firstCount : Nat) (secondTarget : Coordinate)
    (secondPositive : 0 < secondTarget) (secondCount : Nat) :
    let first := entry.request firstTarget firstPositive firstCount
    first ∈ (state.request firstTarget firstPositive firstCount).entries ∧
      first.cursor.machine.emitted.IsPrefix
        (first.request secondTarget secondPositive secondCount).cursor.machine.emitted :=
  ⟨state.requested_entry_mem member firstTarget firstPositive firstCount,
    (entry.request firstTarget firstPositive firstCount).request_word_extends
      secondTarget secondPositive secondCount⟩

end TableCursor

/-! ## Calculus-facing initial states -/

/-- Persistent value and slope emitters for one first jet. -/
def firstJetCursor
    (jet : CCL.ProgressiveFirstJet.FirstJet) : TableCursor :=
  TableCursor.initial [jet.value, jet.slope]

@[simp] theorem firstJetCursor_channels
    (jet : CCL.ProgressiveFirstJet.FirstJet) :
    (firstJetCursor jet).channels = [jet.value, jet.slope] :=
  TableCursor.initial_channels _

/-- Persistent increment, base, value, slope, and remainder emitters for one
displayed quadratic certificate. -/
def quadraticCursor {increment : Gaussian}
    (calculation :
      CCL.ProgressiveQuadraticJet.CertifiedCalculation increment) :
    TableCursor :=
  TableCursor.initial
    [calculation.incrementChannel, calculation.baseChannel,
      calculation.valueChannel, calculation.slopeChannel,
      calculation.remainderChannel]

@[simp] theorem quadraticCursor_channels {increment : Gaussian}
    (calculation :
      CCL.ProgressiveQuadraticJet.CertifiedCalculation increment) :
    (quadraticCursor calculation).channels =
      [calculation.incrementChannel, calculation.baseChannel,
        calculation.valueChannel, calculation.slopeChannel,
        calculation.remainderChannel] :=
  TableCursor.initial_channels _

/-- Persistent emitters for every coefficient of one finite Taylor jet. -/
def taylorCursor
    (jet : CCL.ProgressiveHigherJet.TaylorJet) : TableCursor :=
  TableCursor.initial jet.coefficients

@[simp] theorem taylorCursor_channels
    (jet : CCL.ProgressiveHigherJet.TaylorJet) :
    (taylorCursor jet).channels = jet.coefficients :=
  TableCursor.initial_channels _

/-- Persistent value and partial-coefficient emitters for one displayed
finite-dimensional first jet. -/
def multivariableCursor
    (jet : CCL.ProgressiveHigherJet.MultivariableFirstJet) :
    TableCursor :=
  TableCursor.initial (jet.value :: jet.partials)

@[simp] theorem multivariableCursor_channels
    (jet : CCL.ProgressiveHigherJet.MultivariableFirstJet) :
    (multivariableCursor jet).channels = jet.value :: jet.partials :=
  TableCursor.initial_channels _

end CCL.ProgressivePersistentTable
