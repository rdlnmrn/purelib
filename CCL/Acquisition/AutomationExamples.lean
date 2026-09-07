import CCL.Acquisition.Automation
import CCL.Progressive.GapDivisionExamples
import CCL.Riemann.LegendreSeparatedExamples

/-! # Automatic-route regressions, including symbolic and opaque inputs -/

namespace CCL.AcquisitionAutomationExamples

open CCL.AcquisitionAutomation
open CCL.FiniteAcquisition (Q Gaussian CoherentNamed)
open CCL.ProgressiveBoundedDivisionExamples (oneInput tinyInput zeroInput delayed)

def atomEnvironment (input : CoherentNamed) : Fin 1 → Annotated := fun _ => Annotated.opaque input

def cancellation (input : CoherentNamed) :=
  (Expr.sub (.atom 0) (.atom 0)).compile (atomEnvironment input)

/-- No identity sidecar is supplied, even when the atom is opaque. -/
theorem cancellation_value (input : CoherentNamed) : (cancellation input).rationalValue = some 0 :=
  Expr.compile_cancel (atomEnvironment input) (.atom 0)

theorem cancellation_zero (input : CoherentNamed) :
    (Division.acquire oneInput (Division.start (cancellation input)) 1 (by decide)).2.status = .zero := rfl

theorem cancellation_symbolic (input : CoherentNamed) :
    (Division.acquire oneInput (Division.start (cancellation input)) 1 (by decide)).1.route = .symbolic := rfl

theorem cancellation_original_channel (input : CoherentNamed) :
    (cancellation input).channel =
      CCL.ProgressiveCoherence.CoherentNamed.add input (CCL.ProgressiveCoherence.CoherentNamed.neg input) := rfl

def two : Gaussian := ⟨2, 0⟩

def squaredRoot : Expr 0 := .mul (.root two 0) (.root two 0)
def emptyEnvironment : Fin 0 → Annotated := Fin.elim0

/-- This uses the proved root specification, without recomputing isolation
or requiring an exact rational square-root reading. -/
theorem squaredRoot_value : (squaredRoot.compile emptyEnvironment).rationalValue = some two := by
  unfold squaredRoot
  simp only [Expr.compile]
  exact Annotated.root_square_value two 0

def rootEquation := (Expr.sub squaredRoot (.rational two)).compile emptyEnvironment

theorem rootEquation_value : rootEquation.rationalValue = some 0 := by
  change some ((CCL.Riemann.SquareRootProvenance.isolated two 0).2.parameter + -two) = some 0
  rw [CCL.Riemann.SquareRootProvenance.isolated_parameter]
  rfl

theorem rootEquation_automatically_zero :
    (Division.acquire oneInput (Division.start rootEquation) 1 (by decide)).2.status = .zero :=
  Division.start_rational_zero oneInput rootEquation 1 (by decide) rootEquation_value

theorem neutral_root_provenance (sheet : Fin 2) :
    (((Annotated.rational 0).add (Annotated.root two sheet)).mul (Annotated.rational 1)).square.rationalValue =
      some two := congrArg some (CCL.Riemann.SquareRootProvenance.isolated_parameter two sheet)

theorem distinct_opaque_atoms_not_identified (input : CoherentNamed) :
    ((Expr.sub (.atom (0 : Fin 2)) (.atom 1)).compile (fun _ => Annotated.opaque input)).provenance = none := rfl

theorem unsupported_root_sum :
    ((Annotated.root two 0).add (Annotated.root ⟨3, 0⟩ 0)).provenance = none := rfl

theorem zero_times_opaque (input : CoherentNamed) :
    ((Annotated.rational 0).mul (Annotated.opaque input)).rationalValue = some 0 := rfl

theorem opaque_times_zero (input : CoherentNamed) :
    ((Annotated.opaque input).mul (Annotated.rational 0)).rationalValue = some 0 := rfl

def opaqueTiny := Division.start (Annotated.opaque tinyInput)
def symbolicTiny := Division.start (Annotated.rational CCL.ProgressiveBoundedDivisionExamples.tinyValue)

theorem tiny_numerical_small : (Division.acquire oneInput opaqueTiny 1 (by decide)).2.status = .small := rfl
theorem tiny_symbolic_ready : (Division.acquire oneInput symbolicTiny 1 (by decide)).2.status = .ready := rfl

theorem opaque_zero_only_small :
    (Division.acquire oneInput (Division.start (Annotated.opaque zeroInput)) 1 (by decide)).2.status = .small := rfl

def gapZero : Division.Input zeroInput :=
  { Division.start (Annotated.opaque zeroInput) with
    gap := some ⟨1, by decide, CCL.ProgressiveGapDivisionExamples.zero_gap⟩ }

theorem gap_zero_is_branch_zero : (Division.acquire oneInput gapZero 1 (by decide)).2.status = .branchZero := rfl
theorem gap_zero_route : (Division.acquire oneInput gapZero 1 (by decide)).1.route = .gap := rfl

def delayedDivision := Division.acquire oneInput (Division.start (Annotated.opaque delayed)) 1 (by decide)
theorem delayed_ready : delayedDivision.2.status = .ready := rfl
theorem delayed_state_retained : delayedDivision.1.next.state.source = true := rfl
theorem delayed_index_unchanged : delayedDivision.1.next.state.nextIndex = 0 := rfl
theorem delayed_resume_uses_cache : (delayedDivision.resume tinyInput 1 (by decide)).1.route = .cached := rfl

theorem tiny_resume_finer_ready :
    ((Division.acquire oneInput opaqueTiny 1 (by decide)).resume oneInput
      CCL.ProgressiveGapDivisionExamples.tinyGap
      CCL.ProgressiveGapDivisionExamples.tinyGap_positive).2.status = .ready := rfl

theorem zero_resume_uses_cache (input : CoherentNamed) :
    ((Division.acquire oneInput (Division.start (cancellation input)) 1 (by decide)).resume
      tinyInput 1 (by decide)).1.route = .cached := rfl

def opaqueWord (height : Q) := Words.start
  (Annotated.opaque (CCL.Riemann.LegendreSignedAcquisitionExamples.input height))

theorem negative_word_ready (word : Words.Word) :
    ∃ ready, (Words.acquire (opaqueWord (-1)) word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
theorem positive_word_ready (word : Words.Word) :
    ∃ ready, (Words.acquire (opaqueWord 1) word 1 (by decide)).2 = .ready ready := ⟨_, rfl⟩
theorem zero_word_near (word : Words.Word) :
    ∃ near, (Words.acquire (opaqueWord 0) word 1 (by decide)).2 = .near near := ⟨_, rfl⟩
theorem tiny_word_near (word : Words.Word) :
    ∃ near, (Words.acquire (opaqueWord (1 / 10)) word 1 (by decide)).2 = .near near := ⟨_, rfl⟩

def tinySymbolicWord := Words.start (Annotated.rational ⟨0, 1 / 10⟩)

def symbolicWordExpression := (Expr.add (.rational ⟨1, 1⟩) (.neg (.rational 1))).compile emptyEnvironment

theorem arithmetic_word_symbolic (word : Words.Word) :
    (Words.acquire (Words.start symbolicWordExpression) word 1 (by decide)).1.route = .rational := rfl

/-- The inferred exact route succeeds where the chosen numerical margin is
too coarse, without replacing the original arithmetic expression. -/
theorem tiny_word_symbolic (word : Words.Word) :
    (Words.acquire tinySymbolicWord word 1 (by decide)).1.route = .rational := rfl

theorem word_resume_uses_cache (first second : Words.Word) :
    ((Words.acquire (opaqueWord (-1)) first 1 (by decide)).resume second 1 (by decide)).1.route = .cached := rfl

theorem tiny_word_resume_finer_ready (word : Words.Word) :
    ∃ ready, ((Words.acquire (opaqueWord (1 / 10)) word 1 (by decide)).resume
      word (1 / 10) (by decide)).2 = .ready ready := ⟨_, rfl⟩

def delayedWord := Words.acquire
  (Words.start (Annotated.opaque CCL.Riemann.LegendreSignedAcquisitionExamples.delayed)) [] 1 (by decide)

theorem delayed_word_refined : delayedWord.1.next.state.retained.source = true := rfl
theorem delayed_word_index : delayedWord.1.next.state.retained.nextIndex = 0 := rfl

theorem continuation_uses_final_provider {tau : CoherentNamed} {first : Words.Word}
    (ready : CCL.Riemann.LegendreSeparatedWords.Report tau first) (next : Words.Word) :
    (Words.acquire (Words.continueFrom ready) next 1 (by decide)).1.route = .cached := rfl

end CCL.AcquisitionAutomationExamples
