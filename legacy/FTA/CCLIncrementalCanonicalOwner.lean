import FTA.CCLCanonicalEvent
import FTA.CCLIncrementalEventOwner

/-!
# Reattaching canonical current-state truth to a direct event owner

The history-free event traversal intentionally classifies only the genuinely
new predicate introduced by the next raw bit.  Once reachability supplies
canonical truth of the current parser predicate, this module reconstructs the
complete selected-event payload consumed by the established localization and
tangent-grid machinery.
-/

namespace FTA
namespace CCLIncrementalCanonicalOwner

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLCanonicalEvent
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIncrementalEventOwner
open FTA.CCLPositiveEventSemantics
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial CCL.GaussianRat

/-- Refining an isolated event against the current parser formula lets its
history-free owner table be completed with that formula's canonical truth.
The result is exactly the legacy complete owner pair, with no represented
rational sample involved. -/
theorem ownerChecks_eq_ownerPair_of_current_incremental
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (bit : Bool)
    (currentCanonical : currentFormulaCanonicalCheck cell = true)
    (checks : inputEventIncrementalChecks cell = ownerPair bit) :
    cell.ownerChecks = ownerPair bit := by
  let localOutput : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) output.state (adjugate state.matrix) :=
    { state := output.state
      refines := RatBox.refines_refl output.state.box
      margin := output.margin
      margin_pos := output.margin_pos
      lower := output.lower }
  let refined := currentFormulaInputCell cell
  have incrementalEquality (candidateBit : Bool) :
      formulaEvalWith (inputIncrementalAdvanceFormula state candidateBit)
          (inputEventCanonicalValue cell) =
        formulaEvalWith (inputIncrementalAdvanceFormula state candidateBit)
          (inputEventCanonicalValue refined) := by
    apply formulaEvalWith_inputEvents_eq_of_refinement
      (firstOutput := output) (secondOutput := localOutput)
      cell refined squarefree degreeNonzero elimination
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        candidateBit atom
          (inputIncrementalAdvanceFormula_atoms_subset state candidateBit atom
            member)
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        candidateBit atom
          (inputIncrementalAdvanceFormula_atoms_subset state candidateBit atom
            member)
  have refinedChecks : inputEventIncrementalChecks refined = ownerPair bit := by
    unfold inputEventIncrementalChecks
    rw [← incrementalEquality false, ← incrementalEquality true]
    exact checks
  have currentAtRefined : formulaEvalWith (inputStateFormula state)
      (inputEventCanonicalValue refined) = true := by
    simpa only [currentFormulaCanonicalCheck, refined] using currentCanonical
  rw [currentFormulaInputCell_ownerChecks_eq cell squarefree degreeNonzero
    elimination, inputEventPair_eq_canonical]
  cases bitEq : bit with
  | false =>
      apply Prod.ext
      · apply
          formulaEvalWith_inputAdvance_true_of_current_incremental_true
            state false _ currentAtRefined
        have component := congrArg Prod.fst refinedChecks
        simpa only [inputEventIncrementalChecks, bitEq, ownerPair, refined]
          using component
      · apply formulaEvalWith_inputAdvance_false_of_incremental_false
        have component := congrArg Prod.snd refinedChecks
        simpa only [inputEventIncrementalChecks, bitEq, ownerPair, refined]
          using component
  | true =>
      apply Prod.ext
      · apply formulaEvalWith_inputAdvance_false_of_incremental_false
        have component := congrArg Prod.fst refinedChecks
        simpa only [inputEventIncrementalChecks, bitEq, ownerPair, refined]
          using component
      · apply
          formulaEvalWith_inputAdvance_true_of_current_incremental_true
            state true _ currentAtRefined
        have component := congrArg Prod.snd refinedChecks
        simpa only [inputEventIncrementalChecks, bitEq, ownerPair, refined]
          using component

/-- Reattach current-state reachability to the geometry-facing incremental
payload.  Every geometric field is preserved definitionally; only the
complete owner-table proof is reconstructed. -/
def toCompletePayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (currentCanonical : currentFormulaCanonicalCheck
      selected.candidate.inputCell = true) : SelectedEventPayload output where
  candidate := selected.candidate
  bit := selected.bit
  checks := ownerChecks_eq_ownerPair_of_current_incremental
    selected.candidate.inputCell squarefree degreeNonzero elimination
      selected.bit currentCanonical selected.checks
  decision := selected.decision
  sourceMember := selected.sourceMember

/-- Reachability-indexed form of `toCompletePayload`. -/
def toCompletePayloadOfValid
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedPayload output)
    (valid : FormulaCanonicalOnInputEvents current word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    SelectedEventPayload output :=
  toCompletePayload selected squarefree degreeNonzero elimination
    (valid output selected.candidate.inputCell)

end CCLIncrementalCanonicalOwner
end FTA
