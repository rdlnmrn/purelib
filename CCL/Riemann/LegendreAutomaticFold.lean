import CCL.Riemann.LegendreAutomaticTransport

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace CCL.Riemann.LegendreAutomaticFold

open CCL.Riemann.LegendreFractionalWords
open CCL.Riemann.LegendreModularMonodromy

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev DenominatorPreparation := CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation
abbrev Search := CCL.Riemann.LegendreDenominatorAcquisition.State

def CachedSearch (tau : CoherentNamed) (specification : IntegralMatrix) :=
  CCL.Riemann.LegendreAutomaticTransport.StatePayload
    (fun matrix => matrix = specification) (fun matrix => Search matrix tau)

def cachedInitial (tau : CoherentNamed) (matrix : IntegralMatrix) : CachedSearch tau matrix :=
  { matrix := matrix
    matrix_eq := rfl
    search := CCL.Riemann.LegendreDenominatorAcquisition.initial matrix tau }

def cachedPreparation {tau : CoherentNamed} {matrix : IntegralMatrix}
    (state : CachedSearch tau matrix)
    (preparation : DenominatorPreparation (fractionalDenominator state.matrix tau)) :
    DenominatorPreparation (fractionalDenominator matrix tau) := by
  rw [← state.matrix_eq]
  exact preparation

inductive CursorPayload (headType : Type) (tailType combinedType readyType : Type 1) : Type 1
  | head (state : headType)
  | tail (state : tailType)
  | combined (state : combinedType)
  | ready (preparations : readyType)

/-- Finite dependent acquisition cursor; every preparation is indexed by the
literal intermediate name at which division will execute. -/
def Cursor (tau : CoherentNamed) : List IntegralMatrix → Type 1
  | [] => Sum (Search RFAP.ConstructiveFiniteMatrix.identity tau)
      (FoldPreparations tau [])
  | matrix :: remaining => CursorPayload
      (Search matrix tau)
      (Sigma fun head : DenominatorPreparation (fractionalDenominator matrix tau) =>
        Cursor (fractionalLinear matrix tau head) remaining)
      (Sigma fun head : DenominatorPreparation (fractionalDenominator matrix tau) =>
        Sigma fun _tail : FoldPreparations (fractionalLinear matrix tau head) remaining =>
          CachedSearch tau (matrixProduct (matrix :: remaining)))
      (FoldPreparations tau (matrix :: remaining))

def initial (tau : CoherentNamed) : (matrices : List IntegralMatrix) → Cursor tau matrices
  | [] => .inl (CCL.Riemann.LegendreDenominatorAcquisition.initial _ tau)
  | _ :: _ => .head (CCL.Riemann.LegendreDenominatorAcquisition.initial _ tau)

def finished? (tau : CoherentNamed) : (matrices : List IntegralMatrix) →
    Cursor tau matrices → Option (FoldPreparations tau matrices)
  | [], .inl _ => none
  | [], .inr preparations => some preparations
  | _ :: _, .ready preparations => some preparations
  | _ :: _, .head _ => none
  | _ :: _, .tail _ => none
  | _ :: _, .combined _ => none

/-- One bounded work unit, possibly descending into the retained suffix.
Only one denominator inspection occurs during a unit. -/
def step (tau : CoherentNamed) : (matrices : List IntegralMatrix) →
    Cursor tau matrices → Cursor tau matrices
  | [], .inr preparations => .inr preparations
  | [], .inl state =>
      match CCL.Riemann.LegendreDenominatorAcquisition.step _ tau state with
      | .ready preparation => .inr preparation
      | .progressed next _ => .inl next
  | _ :: _, .ready preparations => .ready preparations
  | matrix :: remaining, .head state =>
      match CCL.Riemann.LegendreDenominatorAcquisition.step matrix tau state with
      | .ready preparation => .tail ⟨preparation,
          initial (fractionalLinear matrix tau preparation) remaining⟩
      | .progressed next _ => .head next
  | matrix :: remaining, .tail ⟨head, cursor⟩ =>
      match finished? (fractionalLinear matrix tau head) remaining cursor with
      | some tail => .combined ⟨head, tail,
          cachedInitial tau (matrixProduct (matrix :: remaining))⟩
      | none => .tail ⟨head, step (fractionalLinear matrix tau head) remaining cursor⟩
  | _ :: _, .combined ⟨head, tail, state⟩ =>
      match CCL.Riemann.LegendreDenominatorAcquisition.step state.matrix tau state.search with
      | .ready preparation => .ready ⟨head, tail, cachedPreparation state preparation⟩
      | .progressed next _ => .combined ⟨head, tail, { state with search := next }⟩

inductive ResultPayload (readyType stateType : Type 1) : Type 1
  | ready (preparations : readyType)
  | exhausted (cursor : stateType)

def Result (tau : CoherentNamed) (matrices : List IntegralMatrix) :=
  ResultPayload (FoldPreparations tau matrices) (Cursor tau matrices)

/-- Fuel bounds the total work across the entire dependent word, not a
separate unbounded search at each intermediate denominator. -/
def attempt (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : Cursor tau matrices) : Nat → Result tau matrices
  | 0 => match finished? tau matrices cursor with
      | some preparations => .ready preparations
      | none => .exhausted cursor
  | fuel + 1 => match finished? tau matrices cursor with
      | some preparations => .ready preparations
      | none => attempt tau matrices (step tau matrices cursor) fuel

theorem attempt_of_finished (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : Cursor tau matrices) (preparations : FoldPreparations tau matrices)
    (finished : finished? tau matrices cursor = some preparations) (fuel : Nat) :
    attempt tau matrices cursor fuel = .ready preparations := by
  cases fuel <;> simp only [attempt, finished]

/-- Splitting a budget and resuming the retained cursor is exactly the same
finite computation as running the combined budget in one call. -/
theorem attempt_add (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : Cursor tau matrices) (first second : Nat) :
    attempt tau matrices cursor (first + second) =
      match attempt tau matrices cursor first with
      | .ready preparations => .ready preparations
      | .exhausted retained => attempt tau matrices retained second := by
  induction first generalizing cursor with
  | zero =>
      cases finished : finished? tau matrices cursor with
      | none => simp only [Nat.zero_add, attempt, finished]
      | some preparations =>
          simp only [Nat.zero_add, attempt, finished]
          exact attempt_of_finished tau matrices cursor preparations finished second
  | succ first inductionHypothesis =>
      cases finished : finished? tau matrices cursor with
      | none =>
          simp only [Nat.succ_add, attempt, finished]
          exact inductionHypothesis (step tau matrices cursor)
      | some preparations => simp only [Nat.succ_add, attempt, finished]

/-- Starting the acquisition needs only an input ratio, finite word, and
budget. Its exhausted cursor can be passed straight back to `attempt`. -/
def attemptWord (tau : CoherentNamed) (word : CCL.Knot.FiniteBraid.Word 3)
    (fuel : Nat) : Result tau (periodBraidMatrices word) :=
  attempt tau (periodBraidMatrices word) (initial tau (periodBraidMatrices word)) fuel

end CCL.Riemann.LegendreAutomaticFold
