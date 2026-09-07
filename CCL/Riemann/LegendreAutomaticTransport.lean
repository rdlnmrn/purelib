import CCL.Riemann.LegendreAutomaticPreparation

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace CCL.Riemann.LegendreAutomaticTransport

open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreFractionalWords
open CCL.Riemann.LegendreAutomaticPreparation

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Word := CCL.Knot.FiniteBraid.Word 3
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev DenominatorPreparation := CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation

/-- Retained data for one already folded finite word. -/
structure StatePayload (specification : IntegralMatrix → Prop)
    (searchType : IntegralMatrix → Type) where
  matrix : IntegralMatrix
  matrix_eq : specification matrix
  search : searchType matrix

def State (tau : CoherentNamed) (word : Word) :=
  StatePayload (fun matrix => matrix = CCL.Riemann.LegendrePicardLefschetz.periodMatrix word)
    (fun matrix => CCL.Riemann.LegendreDenominatorAcquisition.State matrix tau)

def initial (tau : CoherentNamed) (word : Word) : State tau word :=
  let matrix := CCL.Riemann.LegendrePicardLefschetz.periodMatrix word
  { matrix := matrix
    matrix_eq := rfl
    search := CCL.Riemann.LegendreDenominatorAcquisition.initial matrix tau }

/-- The public successful result. The executable fields retain the expensive
matrix and output; equalities tie them to their exact specifications. -/
structure ReadyPayload (specification : IntegralMatrix → Prop)
    (preparationType : IntegralMatrix → Type 1)
    (evaluate : (matrix : IntegralMatrix) → preparationType matrix → CoherentNamed) where
  matrix : IntegralMatrix
  matrix_eq : specification matrix
  preparation : preparationType matrix
  output : CoherentNamed
  output_eq : output = evaluate matrix preparation

def Ready (tau : CoherentNamed) (word : Word) :=
  ReadyPayload (fun matrix => matrix = CCL.Riemann.LegendrePicardLefschetz.periodMatrix word)
    (fun matrix => DenominatorPreparation (fractionalDenominator matrix tau))
    (fun matrix preparation => fractionalLinear matrix tau preparation)

def ready (tau : CoherentNamed) (word : Word) (state : State tau word)
    (preparation : DenominatorPreparation (fractionalDenominator state.matrix tau)) :
    Ready tau word :=
  { matrix := state.matrix
    matrix_eq := state.matrix_eq
    preparation := preparation
    output := fractionalLinear state.matrix tau preparation
    output_eq := rfl }

/-- Total construction from the single reusable positive enclosure. -/
def guaranteed {tau : CoherentNamed} (certificate : PositiveEnclosure tau)
    (word : Word) : Ready tau word :=
  let matrix := CCL.Riemann.LegendrePicardLefschetz.periodMatrix word
  let preparation := CCL.Riemann.LegendreAutomaticPreparation.prepare certificate matrix
    (row_nonzero_of_inverse _ _
      (CCL.Riemann.LegendrePicardLefschetz.periodMatrix_inverse_identities word).1)
  { matrix := matrix
    matrix_eq := rfl
    preparation := preparation
    output := fractionalLinear matrix tau preparation
    output_eq := rfl }

/-- The finite period positivity theorem supplies the one reusable enclosure;
callers of this adapter need neither an enclosure nor denominator witnesses. -/
def guaranteedOfPeriodPositivity {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (positivity : CCL.Riemann.PeriodMatrix.PointwisePositivity data.normalized)
    (word : Word) : Ready data.ratio word :=
  guaranteed (enclosureOfPeriodPositivity data positivity) word

inductive ResultPayload.{u, v} (readyType : Type u) (stateType : Type v) : Type (max u v)
  | ready (result : readyType)
  | exhausted (state : stateType)

/-- The finite scheduling loop operates only on abstract payload types. -/
def runPayload {readyType : Type u} {stateType : Type v}
    (inspect : stateType → Sum readyType stateType) (state : stateType) :
    Nat → ResultPayload readyType stateType
  | 0 => .exhausted state
  | fuel + 1 => match inspect state with
      | .inl result => .ready result
      | .inr next => runPayload inspect next fuel

theorem runPayload_add {readyType : Type u} {stateType : Type v}
    (inspect : stateType → Sum readyType stateType) (state : stateType)
    (first second : Nat) :
    runPayload inspect state (first + second) =
      match runPayload inspect state first with
      | .ready result => .ready result
      | .exhausted retained => runPayload inspect retained second := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, runPayload]
  | succ first inductionHypothesis =>
      rw [Nat.succ_add, runPayload, runPayload]
      cases inspect state with
      | inl result => rfl
      | inr next => exact inductionHypothesis next

def Result (tau : CoherentNamed) (word : Word) : Type 1 :=
  ResultPayload.{1, 0} (Ready tau word) (State tau word)

/-- One denominator inspection returns either the final output or its next
retained state. The small sum keeps runner proofs independent of the large
dependent denominator-process type. -/
def inspect (tau : CoherentNamed) (word : Word) (state : State tau word) :
    Sum (Ready tau word) (State tau word) :=
  match CCL.Riemann.LegendreDenominatorAcquisition.step state.matrix tau state.search with
  | .ready preparation => .inl (ready tau word state preparation)
  | .progressed next _ => .inr { state with search := next }

/-- Bounded automatic acquisition using only the one folded denominator.
Exhaustion retains its matrix and refined state for an exact resumption. -/
def attempt (tau : CoherentNamed) (word : Word)
    (state : State tau word) (fuel : Nat) : Result tau word :=
  runPayload (inspect tau word) state fuel

@[simp] theorem attempt_zero (tau : CoherentNamed) (word : Word)
    (state : State tau word) : attempt tau word state 0 = .exhausted state := rfl

/-- Splitting the single-matrix budget and resuming its exact retained state
is exactly the same result as one combined-budget run. -/
theorem attempt_add (tau : CoherentNamed) (word : Word)
    (state : State tau word) (first second : Nat) :
    attempt tau word state (first + second) =
      match attempt tau word state first with
      | .ready result => .ready result
      | .exhausted retained => attempt tau word retained second := by
  unfold Result
  have law := runPayload_add (inspect tau word) state first second
  cases firstRun : runPayload (inspect tau word) state first <;>
    simpa only [attempt, firstRun] using law

/-- Manual evidence remains indexed by the exact denominator and retained
search state, even though the public interface is indexed by a braid word. -/
abbrev Requirement {tau : CoherentNamed} {word : Word} (state : State tau word) :=
  CCL.Riemann.LegendreDenominatorAcquisition.Requirement state.search

abbrev Evidence {tau : CoherentNamed} {word : Word} {state : State tau word}
    (requirement : Requirement state) :=
  CCL.Riemann.LegendreDenominatorAcquisition.Evidence requirement

def currentRequirement {tau : CoherentNamed} {word : Word}
    (state : State tau word) : Requirement state :=
  CCL.Riemann.LegendreDenominatorAcquisition.currentRequirement state.search

/-- Satisfying the exact retained requirement returns an ordinary certified
output immediately, with no further automatic denominator search. -/
def resume {tau : CoherentNamed} {word : Word}
    (state : State tau word) (requirement : Requirement state)
    (evidence : Evidence requirement) : Ready tau word :=
  match requirement with
  | .candidateApartness => ready tau word state
      (CCL.Riemann.LegendreDenominatorAcquisition.preparationAt
        state.matrix tau state.search evidence)

@[simp] theorem resume_eq_ready {tau : CoherentNamed} {word : Word}
    (state : State tau word) (evidence : Evidence (currentRequirement state)) :
    resume state (currentRequirement state) evidence =
      ready tau word state (CCL.Riemann.LegendreDenominatorAcquisition.preparationAt
        state.matrix tau state.search evidence) := rfl

namespace Ready

/-- Independently acquired outputs agree whenever their finite words have
the same period matrix, even when the words and preparations differ. -/
def respects_matrix {tau : CoherentNamed} {firstWord secondWord : Word}
    (first : Ready tau firstWord) (second : Ready tau secondWord)
    (equal : CCL.Riemann.LegendrePicardLefschetz.periodMatrix firstWord =
      CCL.Riemann.LegendrePicardLefschetz.periodMatrix secondWord) :
    NamedEquivalent first.output.name second.output.name := by
  rw [first.output_eq, second.output_eq]
  exact CCL.Riemann.LegendreFractionalAction.fractionalLinear_of_matrix_eq
    (first.matrix_eq.trans (equal.trans second.matrix_eq.symm)) tau
    first.preparation second.preparation

/-- Certified Artin rewrites preserve automatically acquired outputs. -/
def respects_braid {tau : CoherentNamed} {firstWord secondWord : Word}
    (first : Ready tau firstWord) (second : Ready tau secondWord)
    (relation : CCL.Knot.ArtinRelations.Equivalent firstWord secondWord) :
    NamedEquivalent first.output.name second.output.name :=
  first.respects_matrix second
    (CCL.Riemann.LegendrePicardLefschetz.equivalent_periodMatrix_eq relation)

/-- Successful results do not depend on budgets, resumptions, or the choice
between quantitative preparation and bounded acquisition. -/
def respects {tau : CoherentNamed} {word : Word}
    (first second : Ready tau word) :
    NamedEquivalent first.output.name second.output.name :=
  first.respects_matrix second rfl

/-- Reindex the retained preparation without recomputing the matrix. -/
def periodPreparation {tau : CoherentNamed} {word : Word}
    (result : Ready tau word) :
    DenominatorPreparation (fractionalDenominator
      (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau) := by
  rw [← result.matrix_eq]
  exact result.preparation

def output_equation {tau : CoherentNamed} {word : Word}
    (result : Ready tau word) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (fractionalDenominator
          (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau)
        result.output).name
      (fractionalNumerator
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau).name := by
  have denominatorEq := congrArg (fun matrix => fractionalDenominator matrix tau)
    result.matrix_eq
  have numeratorEq := congrArg (fun matrix => fractionalNumerator matrix tau)
    result.matrix_eq
  rw [result.output_eq, ← denominatorEq, ← numeratorEq]
  exact denominator_mul_fractionalLinear _ _ result.preparation

/-- Any automatically constructed final output agrees with any fully
prepared stepwise execution of the same dual word. -/
def equivalent_fold {tau : CoherentNamed} {word : Word}
    (result : Ready tau word) (preparations : PeriodFoldPreparations word tau) :
    NamedEquivalent result.output.name
      (foldAction tau (periodBraidMatrices word) preparations).name := by
  rw [result.output_eq]
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.LegendreFractionalAction.fractionalLinear_of_matrix_eq
      result.matrix_eq tau result.preparation
      (preparations.periodPreparation word tau))
    (periodOutput_equivalent_foldAction word tau preparations)

/-- The automatic result is the transported period ratio, expressed by its
fraction-free equation on the actual closed-path period coordinates. -/
def transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (path : CCL.Riemann.LegendrePaths.Path frame frame)
    (result : Ready data.ratio path.word) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.periods path 0) result.output).name
      (data.periods path 1).name :=
  CCL.Riemann.LegendrePeriodMonodromy.productiveRatio_ofHomogeneous
    (data.periods path) data.aPeriod _ _ result.output
    (data.periods_normalized path 0) (data.periods_normalized path 1)
    result.output_equation

end Ready

/-- Evidence-driven resumption agrees with any automatically acquired output
for the same word, regardless of its budget or retained search state. -/
def resume_respects {tau : CoherentNamed} {word : Word}
    (state : State tau word) (requirement : Requirement state)
    (evidence : Evidence requirement) (other : Ready tau word) :
    NamedEquivalent (resume state requirement evidence).output.name other.output.name :=
  (resume state requirement evidence).respects other

/-- No caller-supplied denominator preparations: the single positive
enclosure constructs the output and its arbitrary-loop transport witness. -/
def guaranteed_transport {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (positivity : PositiveEnclosure data.ratio)
    (path : CCL.Riemann.LegendrePaths.Path frame frame) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul (data.periods path 0)
        (guaranteed positivity path.word).output).name
      (data.periods path 1).name :=
  (guaranteed positivity path.word).transport data path

end CCL.Riemann.LegendreAutomaticTransport
