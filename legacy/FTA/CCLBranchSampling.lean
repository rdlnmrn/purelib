import FTA.CCLBranchEvidence
import FTA.CCLCompatibleCandidates

/-!
# Feeding CCL branch evidence into bounded compatible sampling

The geometric branch controller works in the original winding-box
coordinate, while raw-parser representability carries an existential affine
tail.  Adjugate inversion identifies that tail with the explicit pulled-back
coordinate.  Consequently, a selected input-coordinate child formula extends
the represented word by one bit.  The finite height-bounded encoder search can
then verify and return a compatible sample for the longer word.
-/

namespace FTA
namespace CCLBranchSampling

open CCL CCL.GaussianRat
open CCL.RawParserSemantics
open FTA.CCLGeometry
open FTA.CCLFormulaPullback
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.CCLBranchEvidence
open FTA.CCLCompatibleCandidates
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The explicit inverse-decoder tail agrees with any existential affine tail
representing the same input. -/
theorem inverse_tail_eq_of_represents
    (state : RawParser.State) (input tail : QI)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (represented : Represents state input tail) :
    RatBox.homographic (adjugate state.matrix) input = tail := by
  have parserDeterminant : state.matrix.det ≠ 0 := by
    simpa only [determinant, Mat2.det] using determinantNonzero
  have inverseTailDenominator := denominator_inverse_tail_ne
    state.matrix input determinantNonzero inverseDenominator
  apply RawParserSemantics.homographic_injective state.matrix
    parserDeterminant inverseTailDenominator represented.1
  exact (homographic_adjugate_inverse state.matrix input
    determinantNonzero inverseDenominator).trans represented.2.1

/-- Turn existential raw-parser semantics into the explicit cell witness used
to rule out two simultaneously true child formulas. -/
def cellWitnessOfRepresents
    (state : RawParser.State) (box : RatBox) (input tail : QI)
    (inside : box.Contains input)
    (determinantNonzero : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (represented : Represents state input tail) : CellWitness state box where
  input := input
  contains := inside
  inverseDenominator := inverseDenominator
  holds := by
    rw [inverse_tail_eq_of_represents state input tail determinantNonzero
      inverseDenominator represented]
    exact represented.2.2

/-- A selected pulled-back child formula extends affine representability by
one raw bit. -/
theorem represented_append_of_inputFormula
    (word : Prefix.Word) (input : QI) (bit : Bool)
    (inverseDenominator :
      (adjugate (RawParser.parse word).matrix).c * input +
        (adjugate (RawParser.parse word).matrix).d ≠ 0)
    (represented : RawParserSemantics.Represented word input)
    (selected :
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input) :
    RawParserSemantics.Represented (word ++ [bit]) input := by
  rcases represented with ⟨tail, represents⟩
  have determinantNonzero :
      determinant (RawParser.parse word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  have inverseTail := inverse_tail_eq_of_represents
    (RawParser.parse word) input tail determinantNonzero
      inverseDenominator represents
  have currentHolds : (RawParser.parse word).Holds
      (RatBox.homographic
        (adjugate (RawParser.parse word).matrix) input) := by
    rw [inverseTail]
    exact represents.2.2
  have possible : RawParserSemantics.CanStep
      (RawParser.parse word) input bit :=
    (inputAdvanceFormula_canStep_iff (RawParser.parse word) input bit
      determinantNonzero inverseDenominator currentHolds).1 selected
  rcases possible with ⟨nextTail, nextRepresents⟩
  exact ⟨nextTail, by
    simpa [RawParser.parse, List.foldl_append] using nextRepresents⟩

/-- The stable old-prefix neighbourhood lets the geometric layer verify only
the genuinely new phase predicate.  The represented old word supplies every
unchanged historical constraint, after which the ordinary one-bit bridge
applies unchanged. -/
theorem represented_append_of_inputIncrementalFormula
    (word : Prefix.Word) (input : QI) (bit : Bool)
    (inverseDenominator :
      (adjugate (RawParser.parse word).matrix).c * input +
        (adjugate (RawParser.parse word).matrix).d ≠ 0)
    (represented : RawParserSemantics.Represented word input)
    (selected :
      (inputIncrementalAdvanceFormula (RawParser.parse word) bit).Holds
        input) :
    RawParserSemantics.Represented (word ++ [bit]) input := by
  rcases represented with ⟨tail, represents⟩
  have determinantNonzero :
      determinant (RawParser.parse word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  have inverseTail := inverse_tail_eq_of_represents
    (RawParser.parse word) input tail determinantNonzero inverseDenominator
      represents
  have currentFormula :
      (stateFormula (RawParser.parse word)).Holds
        (RatBox.homographic
          (adjugate (RawParser.parse word).matrix) input) := by
    apply (stateFormula_iff (RawParser.parse word) _).2
    rw [inverseTail]
    exact represents.2.2
  have incrementalFormula :
      (incrementalAdvanceFormula (RawParser.parse word) bit).Holds
        (RatBox.homographic
          (adjugate (RawParser.parse word).matrix) input) :=
    (inputIncrementalAdvanceFormula_iff (RawParser.parse word) bit input
      inverseDenominator).1 selected
  have completeFormula := advanceFormula_holds_of_current_incremental
    (RawParser.parse word) bit
    (RatBox.homographic (adjugate (RawParser.parse word).matrix) input)
    currentFormula incrementalFormula
  apply represented_append_of_inputFormula word input bit inverseDenominator
    ⟨tail, represents⟩
  apply (inputAdvanceFormula_iff (RawParser.parse word) bit input
    inverseDenominator).2
  exact (advanceFormula_iff (RawParser.parse word) bit _).1 completeFormula

/-- Lemma 10.4's finite verification step after one selected branch bit.  The
supplied geometric point bounds the exhaustive Gaussian-rational grid by its
explicit height. -/
def searchAfterBit
    (word : Prefix.Word) (box : RatBox) (input : QI) (bit : Bool)
    (inside : box.Contains input) (nonzero : input ≠ 0)
    (inverseDenominator :
      (adjugate (RawParser.parse word).matrix).c * input +
        (adjugate (RawParser.parse word).matrix).d ≠ 0)
    (represented : RawParserSemantics.Represented word input)
    (selected :
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input) :
    RepresentedOutcome (word ++ [bit]) box :=
  searchRepresentedAtHeight (word ++ [bit]) box input inside nonzero
    (represented_append_of_inputFormula word input bit inverseDenominator
      represented selected)

/-- Denominator-separated specialization: the uniform lower bound supplies
the inverse denominator needed by the one-bit sampling bridge. -/
def searchAfterSeparatedBit
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    (word : Prefix.Word)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix))
    (input : QI) (bit : Bool) (inside : output.state.box.Contains input)
    (nonzero : input ≠ 0)
    (represented : RawParserSemantics.Represented word input)
    (selected :
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input) :
    RepresentedOutcome (word ++ [bit]) output.state.box :=
  searchAfterBit word output.state.box input bit inside nonzero
    (separation_denominator_ne output inside) represented selected

/-- A resolved strict-cell next-bit result supplies the selected formula at
every point, so any represented nonzero sample in the separated box feeds the
bounded verifier directly. -/
def searchAfterResolvedCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    (word : Prefix.Word)
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input)
    (input : QI) (inside : output.state.box.Contains input)
    (nonzero : input ≠ 0)
    (represented : RawParserSemantics.Represented word input) :
    RepresentedOutcome (word ++ [bit]) output.state.box :=
  searchAfterSeparatedBit word output input bit inside nonzero represented
    (selected inside)

/-! ## Finite lists of selected branch bits -/

/-- Executable verification that one rational point follows every selected
input-coordinate formula along a finite suffix. -/
def traceBool (input : QI) : Prefix.Word → List Bool → Bool
  | _, [] => true
  | word, bit :: bits =>
      decide ((adjugate (RawParser.parse word).matrix).c * input +
        (adjugate (RawParser.parse word).matrix).d ≠ 0) &&
      (inputAdvanceFormula (RawParser.parse word) bit).evalBool input &&
      traceBool input (word ++ [bit]) bits

theorem traceBool_cons_eq_true_iff
    (input : QI) (word : Prefix.Word) (bit : Bool) (bits : List Bool) :
    traceBool input word (bit :: bits) = true ↔
      ((adjugate (RawParser.parse word).matrix).c * input +
          (adjugate (RawParser.parse word).matrix).d ≠ 0) ∧
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input ∧
      traceBool input (word ++ [bit]) bits = true := by
  simp only [traceBool, Bool.and_eq_true, decide_eq_true_eq,
    CCLParserGeometry.Formula.evalBool_eq_true]
  tauto

/-- Iterating the one-bit bridge proves affine representability for the
entire finite verified suffix. -/
theorem represented_append_of_traceBool
    (input : QI) (word : Prefix.Word) (bits : List Bool)
    (represented : RawParserSemantics.Represented word input)
    (trace : traceBool input word bits = true) :
    RawParserSemantics.Represented (word ++ bits) input := by
  induction bits generalizing word with
  | nil => simpa using represented
  | cons bit bits inductionHypothesis =>
      rcases (traceBool_cons_eq_true_iff input word bit bits).mp trace with
        ⟨inverseDenominator, selected, tailTrace⟩
      have nextRepresented := represented_append_of_inputFormula
        word input bit inverseDenominator represented selected
      have finalRepresented := inductionHypothesis
        (word ++ [bit]) nextRepresented tailTrace
      simpa [List.append_assoc] using finalRepresented

/-- Lemma 10.4's bounded final search after any finite formula-verified branch
suffix. -/
def searchAfterTrace
    (word : Prefix.Word) (bits : List Bool) (box : RatBox) (input : QI)
    (inside : box.Contains input) (nonzero : input ≠ 0)
    (represented : RawParserSemantics.Represented word input)
    (trace : traceBool input word bits = true) :
    RepresentedOutcome (word ++ bits) box :=
  searchRepresentedAtHeight (word ++ bits) box input inside nonzero
    (represented_append_of_traceBool input word bits represented trace)

end CCLBranchSampling
end FTA
