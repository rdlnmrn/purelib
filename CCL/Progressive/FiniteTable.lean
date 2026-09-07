import mathlib.Data.ConstructiveList
import CCL.Progressive.QuadraticJet

/-!
# Joint finite requests for coherent CCL tables

Higher jets, local polynomial models, and finite-dimensional directional data
all consist of a displayed finite list of coherent CCL channels.  This module
computes one rational request shared by every list entry.  Membership in the
finite list is enough to recover strict enclosure and semantic-allowance
bounds, persistent prefix growth, and exact parser semantics for that entry.

The recursion is over the displayed list.  There is no unbounded coordinate
space, infimum, completed vector, or quantified family of all coefficients.
-/

namespace CCL.ProgressiveFiniteTable

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed

/-- Fold a visible target through the finitely many semantic-coherence
moduli. -/
def requestTarget : List CoherentNamed → Coordinate → Coordinate
  | [], target => target
  | channel :: remaining, target =>
      CCL.ProgressiveCoherence.Coherent.commonRequest
        (requestTarget remaining target)
        (channel.coherent.accuracyRequest target)

theorem requestTarget_pos : ∀ (channels : List CoherentNamed)
    {target : Coordinate}, 0 < target → 0 < requestTarget channels target
  | [], _target, positive => positive
  | channel :: remaining, _target, positive =>
      CCL.ProgressiveCoherence.Coherent.commonRequest_pos
        (requestTarget_pos remaining positive)
        (channel.coherent.accuracyRequest_pos positive)

theorem requestTarget_le_target : ∀ (channels : List CoherentNamed)
    {target : Coordinate}, 0 < target → requestTarget channels target ≤ target
  | [], _target, _positive => le_rfl
  | channel :: remaining, _target, positive =>
      (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
        (requestTarget_pos remaining positive)
        (channel.coherent.accuracyRequest_pos positive)).le.trans
          (requestTarget_le_target remaining positive)

theorem requestTarget_lt_accuracy_of_mem :
    ∀ (channels : List CoherentNamed) {channel : CoherentNamed}
      (_member : channel ∈ channels) {target : Coordinate}, 0 < target →
        requestTarget channels target <
          channel.coherent.accuracyRequest target
  | [], _channel, member, _target, _positive => by
      simp only [List.not_mem_nil] at member
  | head :: remaining, channel, member, target, positive => by
      rcases List.mem_cons.mp member with equal | tailMember
      · subst head
        exact
          CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
            (requestTarget_pos remaining positive)
            (channel.coherent.accuracyRequest_pos positive)
      · exact
          (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
            (requestTarget_pos remaining positive)
            (head.coherent.accuracyRequest_pos positive)).trans
              (requestTarget_lt_accuracy_of_mem remaining tailMember positive)

/-- Rebase one member at the request shared by its whole finite table. -/
def sharedName (channels : List CoherentNamed) (channel : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : Named :=
  CCL.TranscendentalOutput.refined channel.name
    (requestTarget channels target) (requestTarget_pos channels positive)

theorem sharedName_radius_lt (channels : List CoherentNamed)
    (channel : CoherentNamed) {target : Coordinate} (positive : 0 < target) :
    ((sharedName channels channel target positive).process.ball
      (sharedName channels channel target positive).state).radiusSq < target :=
  (CCL.TranscendentalOutput.refined_error channel.name
    (requestTarget channels target)
    (requestTarget_pos channels positive)).trans_le
      (requestTarget_le_target channels positive)

theorem sharedName_allowance_lt (channels : List CoherentNamed)
    {channel : CoherentNamed} (member : channel ∈ channels)
    {target : Coordinate} (positive : 0 < target) :
    channel.coherent.allowance
        (sharedName channels channel target positive).state < target :=
  channel.coherent.refine_accurate channel.name.state target positive
    (requestTarget channels target) (requestTarget_pos channels positive)
    (requestTarget_lt_accuracy_of_mem channels member positive)

/-- The complete enclosure-and-CCL-output proposition for one channel at a
table's shared request. -/
def RequestContract (channels : List CoherentNamed) (channel : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) (count : Nat) : Prop :=
    let named := sharedName channels channel target positive
    (named.process.ball named.state).radiusSq < target ∧
      channel.coherent.allowance named.state < target ∧
      named.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          named.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        named.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        named.process named.state
        (CCL.ProgressiveTransducer.advance named.machine count)

/-- One finite member receives the complete enclosure-and-CCL-output
contract at the table's shared request. -/
theorem sharedName_bitstream_and_allowance (channels : List CoherentNamed)
    {channel : CoherentNamed} (member : channel ∈ channels)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract channels channel target positive count := by
  let named := sharedName channels channel target positive
  exact
    ⟨sharedName_radius_lt channels channel positive,
      sharedName_allowance_lt channels member positive,
      (named.productive count).1, (named.productive count).2,
      CCL.ProgressiveMachineSemantics.Named.advance_exact
        named count⟩

/-- A displayed finite coefficient or coordinate table. -/
structure Table where
  channels : List CoherentNamed

namespace Table

def length (table : Table) : Nat := table.channels.length

def sharedTarget (table : Table) (target : Coordinate) : Coordinate :=
  requestTarget table.channels target

theorem sharedTarget_pos (table : Table) {target : Coordinate}
    (positive : 0 < target) : 0 < table.sharedTarget target :=
  requestTarget_pos table.channels positive

/-- The actual list of same-budget CCL names returned by one table request. -/
def requestNames (table : Table) (target : Coordinate)
    (positive : 0 < target) : List Named :=
  table.channels.map
    (fun channel => sharedName table.channels channel target positive)

@[simp] theorem requestNames_length (table : Table) (target : Coordinate)
    (positive : 0 < target) :
    (table.requestNames target positive).length = table.length := by
  simp only [requestNames, length, List.length_map]

/-- Every displayed table member satisfies the complete same-budget finite
contract. -/
theorem member_bitstream_and_allowance (table : Table)
    {channel : CoherentNamed} (member : channel ∈ table.channels)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    RequestContract table.channels channel target positive count :=
  sharedName_bitstream_and_allowance table.channels member target positive count

/-- Embed a finite displayed Gaussian-rational table as terminating coherent
CCL channels. -/
def exact (values : List Gaussian) : Table :=
  ⟨values.map CCL.ProgressiveCoherence.CoherentNamed.exact⟩

@[simp] theorem exact_length (values : List Gaussian) :
    (exact values).length = values.length := by
  simp only [exact, length, List.length_map]

/-- Centres of all channels after the table's one shared request. -/
def requestCenters (table : Table) (target : Coordinate)
    (positive : 0 < target) : List Gaussian :=
  table.channels.map fun channel =>
    ((sharedName table.channels channel target positive).process.ball
      (sharedName table.channels channel target positive).state).center

@[simp] theorem sharedName_exact_center (channels : List CoherentNamed)
    (value : Gaussian) (target : Coordinate) (positive : 0 < target) :
    ((sharedName channels
        (CCL.ProgressiveCoherence.CoherentNamed.exact value)
        target positive).process.ball
      (sharedName channels
        (CCL.ProgressiveCoherence.CoherentNamed.exact value)
        target positive).state).center = value := by
  rfl

/-- Terminating exact tables specialize literally to their displayed input
list after any positive shared request. -/
theorem exact_requestCenters (values : List Gaussian) (target : Coordinate)
    (positive : 0 < target) :
    (exact values).requestCenters target positive = values := by
  simp only [exact, requestCenters, List.map_map]
  calc
    _ = List.map id values := by
      apply QuotientFreeList.map_congr_left
      intro value _member
      exact sharedName_exact_center
        (List.map
          CCL.ProgressiveCoherence.CoherentNamed.exact values)
        value target positive
    _ = values := by
      induction values with
      | nil => rfl
      | cons value values inductionHypothesis =>
          rw [List.map_cons, inductionHypothesis]
          rfl

end Table

end CCL.ProgressiveFiniteTable
