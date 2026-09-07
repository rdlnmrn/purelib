import FTA.CCLCanonicalEvent
import FTA.CCLCompleteOwnerShapes

/-!
# A selected owner event with the complete parser history

The ordinary two-child event classifier deliberately classifies only the two
proposed child formulas.  At a later owner intersection, however, weak faces
from the already represented prefix may become equalities again.  This module
follows the selected event to the constructive count-one descendant already
classified against the complete current-state formula.

There is no need to rebuild the source-provenance payload around that dependent
cell.  The descendant itself supplies the common canonical oracle.  Its old
predicate is true by the reachability invariant, and its selected child remains
true by the same-track sign theorem.
-/

namespace FTA
namespace CCLHistoricalEventOwner

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchEventOwner
open FTA.CCLBranchController
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteOwnerShapes
open FTA.CCLFormulaPullback
open FTA.CCLFormulaStability
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.LocalExtraction
open FTA.CCLOwnerDirection
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The selected event cell after every atom of the complete current parser
predicate has also been classified. -/
def historicalInputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  currentFormulaInputCell selected.candidate.inputCell

/-- Refining against the current parser history preserves the executable
owner bit selected by the original event cell. -/
theorem historicalInputCell_ownerChecks
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (historicalInputCell selected).ownerChecks = ownerPair selected.bit := by
  exact (currentFormulaInputCell_ownerChecks_eq
    selected.candidate.inputCell squarefree degreeNonzero
      elimination).symm.trans selected.checks

/-- The common canonical Hermitian-form oracle at the history-classified
descendant of the selected event. -/
def historicalCanonicalValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : HermitianForm → ℚ :=
  inputEventCanonicalValue (historicalInputCell selected)

/-- Exact reachability premise consumed by one selected historical owner.
The finite controller chooses this event before the geometric construction,
so no theorem below needs canonical truth at unrelated paths or candidates. -/
def SelectedCurrentFormulaCanonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Prop :=
  currentFormulaCanonicalCheck selected.candidate.inputCell = true

/-- The finite controller invariant supplies the exact local premise for a
selected global event, using the membership certificate returned by the
executable owner traversal. -/
theorem SelectedCurrentFormulaCanonical.ofSelectedEventCount
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (canonical : ControllerCanonicalOnInputEvents current.numerical
      current.word)
    (selected : SelectedEventCount output) :
    SelectedCurrentFormulaCanonical selected.toPayload := by
  exact (canonical output).1 selected.candidate selected.member

/-- Terminal-guard owners obtain the same selected-event premise from the
guard half of the finite controller invariant. -/
theorem SelectedCurrentFormulaCanonical.ofSelectedGuardEventCount
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLCoupledTrack.State p ambient}
    {output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (canonical : ControllerCanonicalOnInputEvents current.numerical
      current.word)
    (selected : SelectedGuardEventCount output) :
    SelectedCurrentFormulaCanonical selected.toPayload := by
  exact (canonical output).2 selected.candidate selected.member

/-- The selected child remains canonically true after the event factor is
refined against the complete parser history. -/
theorem historicalCanonicalValue_child_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    formulaEvalWith (inputAdvanceFormula state selected.bit)
      (historicalCanonicalValue selected) = true := by
  have pair := inputEventPair_eq_canonical (historicalInputCell selected)
  have checks := historicalInputCell_ownerChecks selected squarefree
    degreeNonzero elimination
  cases bitEq : selected.bit with
  | false =>
      have component := congrArg Prod.fst pair
      have check : (historicalInputCell selected).ownerChecks.1 = true := by
        simp only [checks, bitEq, ownerPair]
      simpa only [historicalCanonicalValue, bitEq] using
        component.symm.trans check
  | true =>
      have component := congrArg Prod.snd pair
      have check : (historicalInputCell selected).ownerChecks.2 = true := by
        simp only [checks, bitEq, ownerPair]
      simpa only [historicalCanonicalValue, bitEq] using
        component.symm.trans check

/-- The selected child and complete old parser predicate, evaluated in one
history-refined algebraic event oracle. -/
def historicalOwnerFormula
    (state : RawParser.State) (bit : Bool) : Formula :=
  .and (inputStateFormula state) (inputAdvanceFormula state bit)

/-- The active faces selected from a true conjunction are exactly the active
faces selected independently from its two conjuncts. -/
theorem activeOwnerForms_and
    (left right : Formula) (value : HermitianForm → ℚ) :
    activeOwnerForms (.and left right) value =
      activeOwnerForms left value ++ activeOwnerForms right value := by
  simp [activeOwnerForms, activeSatisfyingAtoms, satisfyingAtoms]

/-- The analogous decomposition for canonically strict prior faces. -/
theorem strictPriorForms_and
    (left right : Formula) (value : HermitianForm → ℚ) :
    strictPriorForms (.and left right) value =
      strictPriorForms left value ++ strictPriorForms right value := by
  simp [strictPriorForms, strictSatisfyingAtoms, satisfyingAtoms]

/-- Weak owner faces of the old predicate and selected child which meet at
the history-classified event. -/
def historicalActiveOwnerForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List HermitianForm :=
  activeOwnerForms (historicalOwnerFormula state selected.bit)
    (historicalCanonicalValue selected)

/-- Strict prior faces of that same conjunction. -/
def historicalStrictPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List HermitianForm :=
  strictPriorForms (historicalOwnerFormula state selected.bit)
    (historicalCanonicalValue selected)

theorem historicalActiveOwnerForms_eq_append
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    historicalActiveOwnerForms selected =
      activeOwnerForms (inputStateFormula state)
          (historicalCanonicalValue selected) ++
        activeOwnerForms (inputAdvanceFormula state selected.bit)
          (historicalCanonicalValue selected) := by
  exact activeOwnerForms_and _ _ _

theorem historicalStrictPriorForms_eq_append
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    historicalStrictPriorForms selected =
      strictPriorForms (inputStateFormula state)
          (historicalCanonicalValue selected) ++
        strictPriorForms (inputAdvanceFormula state selected.bit)
          (historicalCanonicalValue selected) := by
  exact strictPriorForms_and _ _ _

/-- Under the phase-indexed reachability invariant, the history-refined
oracle satisfies the conjunction of the old predicate and selected child.
This is the algebraic compatibility premise needed by the enlarged
simultaneous tangent cone. -/
theorem historicalOwnerFormula_canonical_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    formulaEvalWith
      (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
      (historicalCanonicalValue selected) = true := by
  have currentHolds := valid
  have currentHolds' : formulaEvalWith
      (inputStateFormula (RawParser.parse current.word))
      (historicalCanonicalValue selected) = true := by
    simpa only [SelectedCurrentFormulaCanonical, currentFormulaCanonicalCheck,
      historicalCanonicalValue, historicalInputCell] using currentHolds
  have childHolds := historicalCanonicalValue_child_holds selected squarefree
    degreeNonzero elimination
  simpa only [historicalOwnerFormula, formulaEvalWith, Bool.and_eq_true] using
    And.intro currentHolds' childHolds

/-- Every face in the simultaneous historical/child owner list is a genuine
circle or line.  Parsed-state decoder and history invertibility are discharged
internally. -/
theorem historicalActiveOwner_boundaryDiscriminant_ne
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    boundaryDiscriminant form ≠ 0 := by
  let state := RawParser.parse current.word
  have determinantNonzero : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have historyValid : HistoryMatricesInvertible state := by
    simpa only [state] using parse_historyMatricesInvertible current.word
  have currentHolds := valid
  have currentHolds' : formulaEvalWith (inputStateFormula state)
      (historicalCanonicalValue selected) = true := by
    simpa only [state, SelectedCurrentFormulaCanonical,
      currentFormulaCanonicalCheck, historicalCanonicalValue,
      historicalInputCell] using currentHolds
  have childHolds := historicalCanonicalValue_child_holds selected squarefree
    degreeNonzero elimination
  rw [historicalActiveOwnerForms_eq_append] at member
  rcases List.mem_append.mp member with currentMember | childMember
  · exact inputStateActiveOwner_boundaryDiscriminant_ne state
      determinantNonzero historyValid (historicalCanonicalValue selected)
      currentHolds' currentMember
  · exact inputAdvanceActiveOwner_boundaryDiscriminant_ne state selected.bit
      determinantNonzero historyValid (historicalCanonicalValue selected)
      childHolds childMember

end CCLHistoricalEventOwner
end FTA
