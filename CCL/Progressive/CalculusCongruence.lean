import CCL.Progressive.PersistentTable
import CCL.Transcendental.LogExpInverse

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

namespace CCL.ProgressiveCalculusCongruence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev Comparison := CCL.OperationalEquivalence.Comparison
abbrev ChannelCursor :=
  CCL.ProgressivePersistentTable.ChannelCursor
abbrev RequestStep :=
  CCL.ProgressivePersistentTable.ChannelCursor.RequestStep

open CCL.ProgressiveMachineSemantics

namespace ChannelCursor

/-- Run an arbitrary finite schedule and then make one common accuracy and
bit-growth request.  The last request gives both schedules a directly
comparable displayed cylinder bound. -/
def scheduledRequest (cursor : ChannelCursor) (schedule : List RequestStep)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    ChannelCursor :=
  (cursor.run schedule).request target positive count

theorem scheduledRequest_extends (cursor : ChannelCursor)
    (schedule : List RequestStep) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    cursor.cursor.machine.emitted.IsPrefix
      (cursor.scheduledRequest schedule target positive count).cursor.machine.emitted :=
  (cursor.run_word_extends schedule).trans
    ((cursor.run schedule).request_word_extends target positive count)

theorem scheduledRequest_length (cursor : ChannelCursor)
    (schedule : List RequestStep) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    (cursor.scheduledRequest schedule target positive count).cursor.machine.emitted.length =
      cursor.cursor.machine.emitted.length +
        CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
          schedule + count := by
  unfold scheduledRequest
  rw [(cursor.run schedule).request_word_length target positive count,
    cursor.run_word_length schedule]

theorem scheduledRequest_exact (cursor : ChannelCursor)
    (schedule : List RequestStep) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    ExactCursor cursor.channel.name.process cursor.rootState
      (cursor.scheduledRequest schedule target positive count).cursor.machine := by
  induction schedule generalizing cursor with
  | nil => exact cursor.request_exact target positive count
  | cons step remaining induction =>
      unfold scheduledRequest
      change ExactCursor cursor.channel.name.process cursor.rootState
        (((cursor.request step.epsilonSq step.positive step.count).run
          remaining).request target positive count).cursor.machine
      exact induction (cursor := cursor.request step.epsilonSq step.positive
        step.count)

theorem scheduledRequest_pair_chordalSq_le (cursor : ChannelCursor)
    (schedule : List RequestStep) (target : Coordinate)
    (positive : 0 < target) (count : Nat) {left right : Gaussian}
    (leftPossible : SemanticMode.possible
      (cursor.scheduledRequest schedule target positive count).cursor.machine.mode
        left)
    (rightPossible : SemanticMode.possible
      (cursor.scheduledRequest schedule target positive count).cursor.machine.mode
        right) :
    CCL.Chordal.chordalSq
        ((cursor.scheduledRequest schedule target positive count).cursor.machine.image
          left)
        ((cursor.scheduledRequest schedule target positive count).cursor.machine.image
          right) ≤ target := by
  unfold scheduledRequest at leftPossible rightPossible ⊢
  exact (cursor.run schedule).request_pair_chordalSq_le target positive count
    leftPossible rightPossible

end ChannelCursor

/-- Compatibility of persistent computations rooted in two operationally
equivalent channels.  Redundant output words need not be textually equal;
the exact-parser fields say what each finite word denotes, while `comparison`
computes a common later rational comparison below the requested target. -/
structure CompatibleRequests (left right : ChannelCursor)
    (leftSchedule rightSchedule : List RequestStep)
    (target : Coordinate) (positive : 0 < target) (count : Nat) : Type where
  left_extends : left.cursor.machine.emitted.IsPrefix
    (left.scheduledRequest leftSchedule target positive count).cursor.machine.emitted
  right_extends : right.cursor.machine.emitted.IsPrefix
    (right.scheduledRequest rightSchedule target positive count).cursor.machine.emitted
  left_length :
    (left.scheduledRequest leftSchedule target positive count).cursor.machine.emitted.length =
      left.cursor.machine.emitted.length +
        CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
          leftSchedule + count
  right_length :
    (right.scheduledRequest rightSchedule target positive count).cursor.machine.emitted.length =
      right.cursor.machine.emitted.length +
        CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
          rightSchedule + count
  left_exact : ExactCursor left.channel.name.process left.rootState
    (left.scheduledRequest leftSchedule target positive count).cursor.machine
  right_exact : ExactCursor right.channel.name.process right.rootState
    (right.scheduledRequest rightSchedule target positive count).cursor.machine
  left_cylinder : ∀ {first second : Gaussian},
    SemanticMode.possible
        (left.scheduledRequest leftSchedule target positive count).cursor.machine.mode
          first →
      SemanticMode.possible
        (left.scheduledRequest leftSchedule target positive count).cursor.machine.mode
          second →
      CCL.Chordal.chordalSq
          ((left.scheduledRequest leftSchedule target positive count).cursor.machine.image
            first)
          ((left.scheduledRequest leftSchedule target positive count).cursor.machine.image
            second) ≤ target
  right_cylinder : ∀ {first second : Gaussian},
    SemanticMode.possible
        (right.scheduledRequest rightSchedule target positive count).cursor.machine.mode
          first →
      SemanticMode.possible
        (right.scheduledRequest rightSchedule target positive count).cursor.machine.mode
          second →
      CCL.Chordal.chordalSq
          ((right.scheduledRequest rightSchedule target positive count).cursor.machine.image
            first)
          ((right.scheduledRequest rightSchedule target positive count).cursor.machine.image
            second) ≤ target
  comparison : Comparison
    (CCL.ProgressiveSampling.approximation left.channel.name)
    (CCL.ProgressiveSampling.approximation right.channel.name)
    (CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
      leftSchedule)
    (CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
      rightSchedule)
    target

/-- Operationally equivalent origins remain compatible after independently
chosen finite schedules and one common final request. -/
def compatibleRequests_of_equivalent (left right : ChannelCursor)
    (equivalent : NamedEquivalent left.channel.name right.channel.name)
    (leftSchedule rightSchedule : List RequestStep)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    CompatibleRequests left right leftSchedule rightSchedule target positive
      count :=
  { left_extends := left.scheduledRequest_extends leftSchedule target positive count
    right_extends := right.scheduledRequest_extends rightSchedule target positive count
    left_length := left.scheduledRequest_length leftSchedule target positive count
    right_length := right.scheduledRequest_length rightSchedule target positive count
    left_exact := left.scheduledRequest_exact leftSchedule target positive count
    right_exact := right.scheduledRequest_exact rightSchedule target positive count
    left_cylinder := by
      intro first second firstPossible secondPossible
      exact left.scheduledRequest_pair_chordalSq_le leftSchedule target positive
        count firstPossible secondPossible
    right_cylinder := by
      intro first second firstPossible secondPossible
      exact right.scheduledRequest_pair_chordalSq_le rightSchedule target positive
        count firstPossible secondPossible
    comparison := equivalent.compare
      (CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
        leftSchedule)
      (CCL.ProgressivePersistentTable.ChannelCursor.scheduledBitCount
        rightSchedule)
      target positive }

/-- A progressive law is an operational equivalence equipped, by
`request`, with the complete persistent-prefix contract above. -/
structure BitLaw (left right : CoherentNamed) : Type where
  equivalent : NamedEquivalent left.name right.name

namespace BitLaw

def ofEquivalent {left right : CoherentNamed}
    (equivalent : NamedEquivalent left.name right.name) : BitLaw left right :=
  ⟨equivalent⟩

/-- Every law can be executed under different finite schedules. -/
def request {left right : CoherentNamed} (law : BitLaw left right)
    (leftSchedule rightSchedule : List RequestStep)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    CompatibleRequests
      (CCL.ProgressivePersistentTable.ChannelCursor.initial left)
      (CCL.ProgressivePersistentTable.ChannelCursor.initial right)
      leftSchedule rightSchedule target positive count :=
  compatibleRequests_of_equivalent _ _ law.equivalent leftSchedule
    rightSchedule target positive count

end BitLaw

/-! ## Congruence of progressive constructors -/

def addition_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : NamedEquivalent rightOne.name rightTwo.name) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.add leftOne rightOne)
      (CCL.ProgressiveCoherence.CoherentNamed.add leftTwo rightTwo) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.coherentAdd_respects
      leftOne leftTwo rightOne rightTwo leftEquivalent rightEquivalent)

/-- Negation respects operational equality.  The proof uses only the already
proved finite CCL additive laws: add the opposite input, cancel it to the
exact rational zero, and reassociate. -/
def negation_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.neg left)
      (CCL.ProgressiveCoherence.CoherentNamed.neg right) := by
  let leftNeg :=
    CCL.ProgressiveCoherence.CoherentNamed.neg left
  let rightNeg :=
    CCL.ProgressiveCoherence.CoherentNamed.neg right
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let leftCross :=
    CCL.ProgressiveCoherence.CoherentNamed.add leftNeg right
  have replaceRight : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftNeg left).name leftCross.name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftNeg leftNeg left right
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        leftNeg.name) equivalent
  have cancelLeft : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftNeg left).name zero.name := by
    simpa only [leftNeg, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.OperationalFieldLaws.coherentAdd_neg_left left
  have crossZero : NamedEquivalent leftCross.name zero.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        replaceRight) cancelLeft
  have begin : NamedEquivalent leftNeg.name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftNeg zero).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentAdd_zero_right leftNeg)
  have insertCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftNeg zero).name
      (CCL.ProgressiveCoherence.CoherentNamed.add leftNeg
        (CCL.ProgressiveCoherence.CoherentNamed.add
          right rightNeg)).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftNeg leftNeg zero
      (CCL.ProgressiveCoherence.CoherentNamed.add right rightNeg)
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        leftNeg.name)
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (by
          simpa only [rightNeg, zero,
            CCL.ProgressiveCoherence.CoherentNamed.add,
            CCL.ProgressiveCoherence.CoherentNamed.neg,
            CCL.ProgressiveCoherence.CoherentNamed.exact] using
            CCL.OperationalFieldLaws.coherentAdd_neg_right right))
  have reassociate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add leftNeg
        (CCL.ProgressiveCoherence.CoherentNamed.add
          right rightNeg)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftCross rightNeg).name := by
    exact CCL.OperationalEquivalence.NamedEquivalent.symm
      (by
        simpa only [leftCross,
          CCL.ProgressiveCoherence.CoherentNamed.add] using
          CCL.OperationalFieldLaws.coherentAdd_assoc
            leftNeg right rightNeg)
  have replaceCross : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftCross rightNeg).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        zero rightNeg).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftCross zero rightNeg rightNeg crossZero
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        rightNeg.name)
  have finish : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        zero rightNeg).name rightNeg.name := by
    simpa only [zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.OperationalFieldLaws.coherentAdd_zero_left rightNeg
  exact BitLaw.ofEquivalent
    (CCL.OperationalEquivalence.NamedEquivalent.trans begin
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        insertCancellation
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          reassociate
          (CCL.OperationalEquivalence.NamedEquivalent.trans
            replaceCross finish))))

def subtraction_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : NamedEquivalent rightOne.name rightTwo.name) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.sub leftOne rightOne)
      (CCL.ProgressiveCoherence.CoherentNamed.sub leftTwo rightTwo) := by
  let negativeLaw := negation_respects rightOne rightTwo rightEquivalent
  let additiveLaw := addition_respects leftOne leftTwo
    (CCL.ProgressiveCoherence.CoherentNamed.neg rightOne)
    (CCL.ProgressiveCoherence.CoherentNamed.neg rightTwo)
    leftEquivalent negativeLaw.equivalent
  exact additiveLaw

def multiplication_respects (leftOne leftTwo rightOne rightTwo : CoherentNamed)
    (leftEquivalent : NamedEquivalent leftOne.name leftTwo.name)
    (rightEquivalent : NamedEquivalent rightOne.name rightTwo.name) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul leftOne rightOne)
      (CCL.ProgressiveCoherence.CoherentNamed.mul leftTwo rightTwo) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.coherentMul_respects
      leftOne leftTwo rightOne rightTwo leftEquivalent rightEquivalent)

def exponential_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    BitLaw (CCL.TranscendentalCoherence.exp left.name)
      (CCL.TranscendentalCoherence.exp right.name) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.automaticExp_respects
      left right equivalent)

/-! ## Principal arithmetic laws on emitted CCL prefixes -/

open CCL.OperationalFieldLaws

def addition_commutative (left right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.add left right)
      (CCL.ProgressiveCoherence.CoherentNamed.add right left) :=
  BitLaw.ofEquivalent (coherentAdd_comm left right)

def addition_associative (left middle right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add left middle)
        right)
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.add middle right)) :=
  BitLaw.ofEquivalent (coherentAdd_assoc left middle right)

def multiplication_commutative (left right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul left right)
      (CCL.ProgressiveCoherence.CoherentNamed.mul right left) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.coherentMul_comm left right)

def multiplication_associative (left middle right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.mul left middle)
        right)
      (CCL.ProgressiveCoherence.CoherentNamed.mul left
        (CCL.ProgressiveCoherence.CoherentNamed.mul middle right)) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.coherentMul_assoc
      left middle right)

def multiplication_distributive (left middle right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul left
        (CCL.ProgressiveCoherence.CoherentNamed.add middle right))
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.mul left middle)
        (CCL.ProgressiveCoherence.CoherentNamed.mul left right)) :=
  BitLaw.ofEquivalent (coherentMul_add_left left middle right)

def additive_zero (input : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.add input
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0)) input :=
  BitLaw.ofEquivalent (coherentAdd_zero_right input)

def additive_inverse (input : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.add input
        (CCL.ProgressiveCoherence.CoherentNamed.neg input))
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0) :=
  BitLaw.ofEquivalent (coherentAdd_neg_right input)

def multiplicative_unit (input : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul input
        (CCL.ProgressiveCoherence.CoherentNamed.exact 1)) input :=
  BitLaw.ofEquivalent (coherentMul_one_right input)

def exponential_addition (left right : CoherentNamed) :
    BitLaw
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.TranscendentalCoherence.exp left.name)
        (CCL.TranscendentalCoherence.exp right.name))
      (CCL.TranscendentalCoherence.exp
        (CCL.ProgressiveCoherence.CoherentNamed.add left right).name) :=
  BitLaw.ofEquivalent
    (CCL.TranscendentalCoherence.automaticExp_add left right)

/-- Every explicitly anchored logarithm branch satisfies
`exp(log(y)) = y` at the persistent-prefix layer. -/
def exponential_logarithm {input : CoherentNamed}
    (branch : CCL.LogBranchCalculus.AnchoredChart input) :
    BitLaw (CCL.TranscendentalCoherence.exp branch.output.name)
      input :=
  BitLaw.ofEquivalent branch.exponential_inverse

/-- The reverse direction is necessarily local: the finite zero-alignment
certificate selects the intended preimage branch. -/
def logarithm_exponential (input : CoherentNamed)
    (branch : CCL.LogBranchCalculus.AnchoredChart
      (CCL.LogExpInverse.exponentialInput input))
    (alignment : CCL.LogExpInverse.LocalAlignment
      input branch.output) :
    BitLaw branch.output input :=
  BitLaw.ofEquivalent
    (CCL.LogExpInverse.logarithm_exponential_inverse
      input branch alignment)

end CCL.ProgressiveCalculusCongruence
