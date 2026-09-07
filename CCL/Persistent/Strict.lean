import CCL.Boundary.FormulaBoxSign
import CCL.Persistent.CCL

/-!
# Strict-sign steps for the persistent CCL controller

This module implements the part of the one-bit controller where every atom
of the selected child formula is separated from its Hermitian boundary on the
current box.  The same displayed input remains a compatible sample after the
bit is appended, and formula stability proves this uniformly for every later
supplied winding-one refinement.

Boundary equality is intentionally not guessed here.  `stableNext?` returns
`none` when an atom margin is unresolved; the curve-count/equality-owner layer
must handle precisely those cases.
-/

namespace CCL.PersistentCCLStrict

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Word := List Bool
abbrev Formula := CCL.CCLFormula.Formula
abbrev Atom := CCL.CCLFormula.Atom
abbrev State := CCL.PersistentCCL.State

open CCL.RawParser
open CCL.RawParserSemantics
open CCL.PersistentCCL

namespace CompatibleSample

/-- The input-coordinate formula at a compatible sample is the same decision
as the affine formula at its explicitly computed inverse tail. -/
theorem inputAdvanceFormula_iff_nextTail
    {word : Word} {box : Box}
    (sample : CCL.PersistentCCL.CompatibleSample word box)
    (bit : Bool) :
    (CCL.CCLNextBit.inputAdvanceFormula
        (parse word) bit).Holds sample.point ↔
      (CCL.CCLNextBit.advanceFormula
        (parse word) bit).Holds sample.nextDecision.tail := by
  let next := sample.nextDecision
  exact
    (CCL.CCLNextBit.inputAdvanceFormula_canStep_iff
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents bit).trans
    ((CCL.ParserStep.canStep_iff_canAdvanceAt
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents bit).trans
    (CCL.CCLNextBit.advanceFormula_iff
      (parse word) bit next.tail).symm)

/-- A full local child decision supplies the history-free input-coordinate
obligation used by the persistent controller. -/
theorem inputIncrementalAdvanceFormula_holds_of_advance
    {word : Word} {box : Box}
    (sample : CCL.PersistentCCL.CompatibleSample word box)
    (bit : Bool)
    (advance : (CCL.CCLNextBit.advanceFormula
      (parse word) bit).Holds sample.nextDecision.tail) :
    (CCL.CCLNextBit.inputIncrementalAdvanceFormula
      (parse word) bit).Holds sample.point := by
  let next := sample.nextDecision
  have inverseDenominator :=
    CCL.CCLNextBit.inverseDenominator_of_represents
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents
  rw [CCL.CCLNextBit.inputIncrementalAdvanceFormula,
    CCL.CCLFormula.Formula.pullback_iff
      (CCL.CCLPullback.adjugate (parse word).matrix)
      (CCL.CCLNextBit.incrementalAdvanceFormula
        (parse word) bit) sample.point inverseDenominator,
    CCL.CCLNextBit.inverseTail_eq
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents]
  exact CCL.CCLNextBit.incrementalAdvanceFormula_holds_of_advance
    (parse word) bit next.tail advance

/-- Preserve the displayed rational input while appending a semantically
admissible bit.  Only the propositional representation witness changes. -/
def extend
    {word : Word} {box : Box}
    (sample : CCL.PersistentCCL.CompatibleSample word box)
    (bit : Bool)
    (holds : (CCL.CCLNextBit.inputAdvanceFormula
      (parse word) bit).Holds sample.point) :
    CCL.PersistentCCL.CompatibleSample (word ++ [bit]) box := by
  let next := sample.nextDecision
  have possible : CanStep (parse word) sample.point bit :=
    (CCL.CCLNextBit.inputAdvanceFormula_canStep_iff
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents bit).1 holds
  exact
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented := by
        rcases possible with ⟨tail, represented⟩
        exact ⟨tail, by
          simpa only [parse_append_singleton] using represented⟩ }

/-- Append a bit from only its history-free formula.  Current representability
supplies all retained constraints before the incremental predicate is folded
back into the complete child formula. -/
def extendIncremental
    {word : Word} {box : Box}
    (sample : CCL.PersistentCCL.CompatibleSample word box)
    (bit : Bool)
    (holds : (CCL.CCLNextBit.inputIncrementalAdvanceFormula
      (parse word) bit).Holds sample.point) :
    CCL.PersistentCCL.CompatibleSample (word ++ [bit]) box := by
  let next := sample.nextDecision
  have inverseDenominator :=
    CCL.CCLNextBit.inverseDenominator_of_represents
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents
  have tailIncremental :
      (CCL.CCLNextBit.incrementalAdvanceFormula
        (parse word) bit).Holds next.tail := by
    have pulled :=
      (CCL.CCLFormula.Formula.pullback_iff
        (CCL.CCLPullback.adjugate (parse word).matrix)
        (CCL.CCLNextBit.incrementalAdvanceFormula
          (parse word) bit) sample.point inverseDenominator).1 holds
    rw [CCL.CCLNextBit.inverseTail_eq
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents] at pulled
    exact pulled
  have currentHolds :
      (CCL.CCLFormula.stateFormula (parse word)).Holds
        next.tail :=
    (CCL.CCLFormula.stateFormula_iff
      (parse word) next.tail).2 next.represents.2.2
  have advance :=
    CCL.CCLNextBit.advanceFormula_holds_of_current_incremental
      (parse word) bit next.tail currentHolds tailIncremental
  have canAdvance :=
    (CCL.CCLNextBit.advanceFormula_iff
      (parse word) bit next.tail).1 advance
  have possible : CanStep (parse word) sample.point bit :=
    (CCL.ParserStep.canStep_iff_canAdvanceAt
      (parse word) sample.point next.tail (parse_det_ne word)
      next.represents bit).2 canAdvance
  exact
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented := by
        rcases possible with ⟨tail, represented⟩
        exact ⟨tail, by
          simpa only [parse_append_singleton] using represented⟩ }

end CompatibleSample

/-- All finite evidence needed for a strict-sign one-bit persistent step. -/
structure StableNext
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  bit : Bool
  stable : CCL.CCLFormulaBoxSign.Stable
    ambient current.numerical.box
    (CCL.CCLNextBit.inputIncrementalAdvanceFormula
      (parse current.word) bit)
  currentHolds : (CCL.CCLNextBit.inputIncrementalAdvanceFormula
    (parse current.word) bit).Holds current.currentSample.point

/-- Inspect the local sample's finite next-bit decision, then execute every
strict atom-margin comparison for that child formula. -/
def stableNext?
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) : Option (StableNext current) :=
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal _ => none
  | .next bit tailHolds _ =>
      let formula := CCL.CCLNextBit.inputIncrementalAdvanceFormula
        (parse current.word) bit
      match CCL.CCLFormulaBoxSign.stable? formula ambient
          current.numerical.box current.numerical.refinesAmbient
          sample.point sample.inside with
      | none => none
      | some stable =>
          some
            { bit := bit
              stable := stable
              currentHolds :=
                CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
                  sample bit tailHolds }

/-- The displayed current sample is locally terminal. -/
structure LocalTerminal
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  none : ∀ bit, ¬CCL.RawParserSemantics.CanStep
    (parse current.word) current.currentSample.point bit

/-- A nonterminal child whose structural box inspection stopped at one
concrete unresolved Hermitian atom. -/
structure BoundaryNext
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  bit : Bool
  atom : Atom
  member : atom ∈
    (CCL.CCLNextBit.inputIncrementalAdvanceFormula
      (parse current.word) bit).atoms
  failure : CCL.CCLBoxSign.certificate?
    atom.form ambient current.numerical.box current.numerical.refinesAmbient
      current.currentSample.point current.currentSample.inside = none
  currentHolds : (CCL.CCLNextBit.inputIncrementalAdvanceFormula
    (parse current.word) bit).Holds current.currentSample.point

/-- Total structural decomposition of one displayed next-bit decision. -/
inductive NextInspection
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  | terminal (result : LocalTerminal current)
  | stable (result : StableNext current)
  | boundary (result : BoundaryNext current)

/-- Decide the current sample's next bit and retain the first unresolved atom
when the full child formula is not yet box-stable. -/
def inspectNext
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) : NextInspection current := by
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal terminalNone =>
      exact .terminal
        { none := by
            intro bit possible
            apply terminalNone bit
            apply (CCL.CCLNextBit.advanceFormula_iff
              (parse current.word) bit next.tail).2
            exact (CCL.ParserStep.canStep_iff_canAdvanceAt
              (parse current.word) sample.point next.tail
              (CCL.RawParser.parse_det_ne current.word)
              next.represents bit).1 possible }
  | .next bit tailHolds _unique =>
      let formula := CCL.CCLNextBit.inputIncrementalAdvanceFormula
        (parse current.word) bit
      have currentHolds : formula.Holds sample.point := by
        exact CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
          sample bit tailHolds
      match CCL.CCLFormulaBoxSign.inspect formula ambient
          current.numerical.box current.numerical.refinesAmbient sample.point
          sample.inside with
      | .stable stable =>
          exact .stable
            { bit := bit
              stable := stable
              currentHolds := currentHolds }
      | .unresolved atom member failure =>
          exact .boundary
            { bit := bit
              atom := atom
              member := by simpa only [formula] using member
              failure := by simpa only [sample, formula] using failure
              currentHolds := by simpa only [sample, formula] using currentHolds }

namespace StableNext

/-- A box-stable child formula extends the persistent sample provider over
all later supplied subboxes. -/
def state
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (next : StableNext current) :
    State p ambient where
  numerical := current.numerical
  word := current.word ++ [next.bit]
  samples :=
    { sample := fun later laterRefines =>
        let prior := current.samples.sample later laterRefines
        have priorInsideCurrent : current.numerical.box.Contains prior.point :=
          laterRefines.contains prior.inside
        have priorHolds :
            (CCL.CCLNextBit.inputIncrementalAdvanceFormula
              (parse current.word) next.bit).Holds prior.point :=
          (next.stable.holds_iff current.currentSample.inside
            priorInsideCurrent).1 next.currentHolds
        CompatibleSample.extendIncremental prior next.bit priorHolds }

@[simp] theorem state_word
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (next : StableNext current) :
    next.state.word = current.word ++ [next.bit] := rfl

@[simp] theorem state_box
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (next : StableNext current) :
    next.state.numerical.box = current.numerical.box := rfl

/-- Package the implemented strict-sign case in the abstract controller's
one-step output contract. -/
def stepResult
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (next : StableNext current) :
    CCL.PersistentCCL.StepResult current :=
  .next next.bit next.state
    (RFAP.Boxes.Box.refines_refl current.numerical.box) rfl

end StableNext

end CCL.PersistentCCLStrict
