module

public import scripts.checkpoint.RawSubdivision
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
public import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
public import Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching.Preparation
import scripts.checkpoint.RawRefinement
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
import Purelib.RootIsolation.Power.Unit.Source.Preparation
import Purelib.Polynomial.Power.Gaussian.Progressive.Coefficients
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.System.FilePath
import Purelib.Data.String.Basic
import Purelib.Data.Json.Codec
import Purelib.System.IO

/-! # Checked incremental replay of original coherent-root payments -/

public section

namespace CoherentRootCheckpoint

open Purelib
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open Purelib.Data.Rat.Bounds.AccuracyRadius
open IntegrationCheckpoint
open Purelib.System.FilePath (join)
open scoped Purelib.Data.String

variable {polynomial : GaussianPolynomial} {ambient : Box}
  {track : WindingOneTrack polynomial ambient}

variable {m : Type → Type} [Monad m] [MonadLiftT IO m]

/-- A retained complete original cache state at its original natural index. -/
abbrev State (root : CertifiedName track) (index : Nat) :=
  { value : WindingOneState polynomial ambient // value = root.stateAt index }

/-- Restore one exact original cache successor through a supplied same-track refinement reader.

The original step target determines the same positive accuracy radius. The
reader consumes the actual predecessor and returns the complete original
track refinement; the successor retains its unchanged numerical state index. -/
@[expose] def nextStateUsing (root : CertifiedName track)
    (refine : (directory : System.FilePath) → (current : WindingOneState polynomial ambient) →
      (epsilon : Coordinate) → (positive : 0 < epsilon) →
      IO {value : WindingOneState polynomial ambient // value = track.refine current epsilon positive})
    (directory : System.FilePath) (index : Nat) (current : State root index) :
    IO (State root (index + 1)) := do
  let epsilon := accuracyRadius (stepTarget track index)
  let positive := accuracyRadius_pos (stepTarget_positive track index)
  let saved ← refine (join directory s!"state-{index + 1}") current.val epsilon positive
  return ⟨saved.val, by
    have step : saved.val = CoherentRoot.state track (index + 1) :=
      saved.property.trans (congrArg (fun state => track.refine state epsilon positive)
        (current.property.trans (root.stateAt_eq index)))
    exact step.trans (root.stateAt_eq (index + 1)).symm⟩

/-- Restore the next original cache state from checked atomic Newton-refinement artifacts.

The supplied track law identifies the unchanged original canonical refinement.
The exact predecessor, quarter-geometric target and positive accuracy radius
are retained; complete readback identifies the next original cache state.
The supplied shared thunk retains the original elimination certificate and
forces its construction only when an actual successor is requested.
-/
@[expose] def nextState (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Nat) (current : State root index) :
    IO (State root (index + 1)) :=
  nextStateUsing root (fun directory current epsilon positive => do
    let retained := elimination.get
    let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns polynomial input.nonzero
      input.degreePositive
    let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.cast retained.original_eq.symm loader
    RawSubdivisionCheckpoint.refineTrack input retained.original retained.original_eq cachedLoader columns
      winding directory track canonical current epsilon positive) directory index current

/-- Restore an original cache prefix in order, consuming each retained predecessor once. -/
@[expose] def stateAt (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : (index : Nat) → IO (State root index)
  | 0 => pure ⟨track.initial, (root.stateAt_eq 0).symm⟩
  | index + 1 => do
      let previous ← stateAt root input elimination canonical columns winding directory index
      nextState root input elimination canonical columns winding directory index previous

/-- Replay the original bounded ordered search with supplied exact successor-state actions.

An inaccurate state retains its diagonal, target, index and remaining original
budget before the next unchanged refinement is restored. The first accurate
state supplies the original complete paid result; the original sufficient
upper-stage law certifies the terminal branch without a new accuracy assumption.
-/
@[expose] def searchWithStates (root : CertifiedName track)
    (successor : (index : Nat) → State root index → m (State root (index + 1)))
    (directory : System.FilePath) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq)
    (maxIndex : Nat) (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive) :
    (remaining index : Nat) → (indexGe : start ≤ index) → (balance : index + remaining = maxIndex) →
    (current : State root index) →
    m { value : Refinement root start // value =
      Refinement.search root start targetSq positive maxIndex maxIndexEq remaining index indexGe balance }
  | 0, index, indexGe, balance, current => do
      have indexEq : index = root.approximation.refineIndex start targetSq positive := balance.trans maxIndexEq
      have accurate : current.val.box.diagonalSq < targetSq := by
        rewrite [current.property, indexEq]
        exact root.stateAt_refineIndex_diagonal_lt start targetSq positive
      return ⟨Refinement.atState root start targetSq positive maxIndex maxIndexEq index indexGe balance.le
        current.val current.property accurate,
        Refinement.atState_eq_search root start targetSq positive maxIndex maxIndexEq 0 index indexGe balance
          current.val current.property accurate⟩
  | remaining + 1, index, indexGe, balance, current => do
      if accurate : current.val.box.diagonalSq < targetSq then
        return ⟨Refinement.atState root start targetSq positive maxIndex maxIndexEq index indexGe
          ((Nat.le_add_right index (remaining + 1)).trans_eq balance) current.val current.property accurate,
          Refinement.atState_eq_search root start targetSq positive maxIndex maxIndexEq (remaining + 1) index
            indexGe balance current.val current.property accurate⟩
      else
        saveJson (join directory s!"state-{index}-inaccurate.json")
          (Json.mkObj [("kind", toJson "original cache state does not yet meet this request"),
            ("index", toJson index), ("remaining", toJson (remaining + 1)), ("maximum", toJson maxIndex),
            ("target", toJson (fractionData targetSq)),
            ("diagonal", toJson (fractionData current.val.box.diagonalSq))])
        let next ← successor index current
        let rest ← searchWithStates root successor directory start targetSq positive maxIndex maxIndexEq
          remaining (index + 1) (indexGe.trans (Nat.le_succ index))
          ((Nat.add_right_comm index 1 remaining).trans balance) next
        return ⟨rest.val, by
          have inaccurate : ¬(root.stateAt index).box.diagonalSq < targetSq := by
            rewrite [← current.property]
            exact accurate
          dsimp only [Refinement.search]
          rewrite [dif_neg inaccurate]
          exact rest.property⟩

/-- Replay the original ordered search using its original next-state loader and diagnostic directory. -/
@[expose] def search (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq)
    (maxIndex : Nat) (maxIndexEq : maxIndex = root.approximation.refineIndex start targetSq positive)
    (remaining index : Nat) (indexGe : start ≤ index) (balance : index + remaining = maxIndex)
    (current : State root index) :
    IO { value : Refinement root start // value =
      Refinement.search root start targetSq positive maxIndex maxIndexEq remaining index indexGe balance } :=
  searchWithStates root (nextState root input elimination canonical columns winding directory) directory
    start targetSq positive maxIndex maxIndexEq remaining index indexGe balance current

/-- Restore the complete original paid result through one retained indexed state reader.

The reader supplies original states at the unchanged start and successor
indices. Diagnostic writes retain their separate request directory and the
same ordered-search branch, budget and stopping rules as the original payment.
-/
@[expose] def ofTargetWithStates (root : CertifiedName track)
    (states : (index : Nat) → m (State root index)) (directory : System.FilePath)
    (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    m { value : Refinement root start // value = Refinement.ofTarget root start targetSq positive } := do
  let maxIndex := root.approximation.refineIndex start targetSq positive
  have order := root.approximation.refineIndex_ge start targetSq positive
  let current ← states start
  searchWithStates root (fun index _ => states (index + 1)) directory start targetSq positive maxIndex rfl
    (maxIndex - start) start (Nat.le_refl start) (Nat.add_sub_of_le order) current

/-- Restore the complete original paid request through checked original state refinements. -/
@[expose] def ofTarget (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq) :
    IO { value : Refinement root start // value = Refinement.ofTarget root start targetSq positive } := do
  let maxIndex := root.approximation.refineIndex start targetSq positive
  have order := root.approximation.refineIndex_ge start targetSq positive
  let current ← stateAt root input elimination canonical columns winding directory start
  search root input elimination canonical columns winding directory start targetSq positive maxIndex rfl
    (maxIndex - start) start (Nat.le_refl start) (Nat.add_sub_of_le order) current

/-- Restore an original restart while retaining its actual ambient and exact complete paid result.

The cached ambient reading is consumed by all replay calls. The original
positive search floor, numerical request, states and restart construction are
unchanged, and the callback receives their complete original-result equality.
-/
@[expose] def withReconditioning {α : Type} (cachedAmbient : Box) (sameAmbient : cachedAmbient = ambient)
    (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (start : Nat) (targetSq : Coordinate) (positive : 0 < targetSq)
    (use : (prepared : Reconditioning root start) →
      prepared = Reconditioning.ofTarget root start targetSq positive → IO α) : IO α := by
  subst ambient
  exact do
    let paid ← ofTarget root input elimination canonical columns winding directory (start + 1) targetSq positive
    let prepared := Reconditioning.ofRefinement root start targetSq positive paid.val paid.property
    use prepared (Reconditioning.ofRefinement_eq root start targetSq positive paid.val paid.property)

/-- Restore one exact successor of a track following the total dyadic policy.

The supplied pointwise law permits a retained refinement-cache view of the
same policy. The returned state is the root's complete same-index state;
no identity with the old Newton program is asserted.
-/
@[expose] def nextDyadicState (root : CertifiedName track) (input : Input polynomial)
    (elimination : Input.Elimination input)
    (policy : ∀ current epsilon positive, track.refine current epsilon positive =
      (Track.Accelerated.dyadicRefinement elimination.certificate
        (Subdivision.WindingOne.ofInitial input elimination.certificate current) current epsilon positive).state)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) (index : Nat) (current : State root index) :
    IO (State root (index + 1)) := do
  let epsilon := accuracyRadius (stepTarget track index)
  let positive := accuracyRadius_pos (stepTarget_positive track index)
  let loader : RootRefinementCheckpoint.ClearanceLoader elimination.certificate
      (.canonical elimination.certificate) IO := by
    rcases elimination with ⟨degree, degreeEq, certificate, same⟩
    cases degreeEq
    cases same
    exact .separated columns polynomial input.nonzero input.degreePositive
  let saved ← RawSubdivisionCheckpoint.dyadicResult input elimination.certificate loader winding requireSavedHeader
    (join directory s!"state-{index + 1}") current.val epsilon positive
  return ⟨saved.val.state, by
    have restored := congrArg (fun result : Purelib.RootIsolation.Refinement current.val.raw epsilon => result.state)
      saved.property
    have step : saved.val.state = CoherentRoot.state track (index + 1) :=
      restored.trans ((policy current.val epsilon positive).symm.trans
        (congrArg (fun value => track.refine value epsilon positive)
          (current.property.trans (root.stateAt_eq index))))
    exact step.trans (root.stateAt_eq (index + 1)).symm⟩

/-- Load a consecutive loaded of complete dyadic refinements and their exact original request coverage.

Each actual loaded successor becomes the next current state. Cheap proposal
arithmetic is recomputed, while expensive columns and winding divisions obey
the supplied checkpoint controls. There is no fixed state-index capacity.
-/
@[expose] def dyadicRefinements (input : Input polynomial)
    (elimination : Input.Elimination input)
    (initial : WindingOneState polynomial ambient)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) :
    (remaining index : Nat) →
    (current : { value : WindingOneState polynomial ambient //
      value = CoherentRoot.state (Accelerated.dyadicTrack input elimination.certificate initial) index }) →
    IO (Accelerated.RefinementPrefix (Accelerated.dyadicTrack input elimination.certificate initial) index remaining)
  | 0, index, current => pure ⟨[], rfl, by
      intro requested order bound
      rewrite [Nat.add_zero] at bound
      exact (Nat.not_lt_of_ge order bound).elim, ⟨current.val, by simpa only [Nat.add_zero] using current.property⟩⟩
  | remaining + 1, index, current => do
      let track := Accelerated.dyadicTrack input elimination.certificate initial
      let epsilon := accuracyRadius (stepTarget track index)
      let positive := accuracyRadius_pos (stepTarget_positive track index)
      let loader : RootRefinementCheckpoint.ClearanceLoader elimination.certificate
          (.canonical elimination.certificate) IO := by
        rcases elimination with ⟨degree, degreeEq, certificate, same⟩
        cases degreeEq
        cases same
        exact .separated columns polynomial input.nonzero input.degreePositive
      let saved ← RawSubdivisionCheckpoint.dyadicResult input elimination.certificate loader winding requireSavedHeader
        (join directory s!"state-{index + 1}") current.val epsilon positive
      let entry : Track.Observation.CachedRefinement track :=
        ⟨current.val, epsilon, positive, saved.val, saved.property⟩
      have nextEq : saved.val.state = CoherentRoot.state track (index + 1) :=
        (congrArg (fun result : Purelib.RootIsolation.Refinement current.val.raw epsilon => result.state)
          saved.property).trans
          (congrArg (fun value => track.refine value epsilon positive) current.property)
      let rest ← dyadicRefinements input elimination initial columns winding requireSavedHeader directory
        remaining (index + 1) ⟨saved.val.state, nextEq⟩
      return ⟨entry :: rest.entries, congrArg Nat.succ rest.length_eq, by
        intro requested order bound
        if first : requested = index then
          subst requested
          exact ⟨entry, List.mem_cons_self, current.property, rfl⟩
        else
          have later : index + 1 ≤ requested := by omega0
          have before : requested < (index + 1) + remaining := by omega0
          obtain ⟨retained, member, stateEq, epsilonEq⟩ := rest.covers requested later before
          exact ⟨retained, List.mem_cons_of_mem entry member, stateEq, epsilonEq⟩, ⟨rest.current.val, by
          have indices : (index + 1) + remaining = index + (remaining + 1) := by omega0
          exact rest.current.property.trans (congrArg (CoherentRoot.state track) indices)⟩⟩

/-- Restore only a missing suffix from the retained exact terminal state.

Previously completed entries remain the original left loaded. The loader does
not revisit any earlier checkpoint or rerun its scalar proposal sequence.
-/
@[expose] def extendDyadicRefinements (input : Input polynomial)
    (elimination : Input.Elimination input)
    (initial : WindingOneState polynomial ambient)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) {first : Nat}
    (loaded : Accelerated.RefinementPrefix (Accelerated.dyadicTrack input elimination.certificate initial) 0 first)
    (additional : Nat) :
    IO (Accelerated.RefinementPrefix
      (Accelerated.dyadicTrack input elimination.certificate initial) 0 (first + additional)) := do
  let suffix ← dyadicRefinements input elimination initial columns winding requireSavedHeader directory
    additional first ⟨loaded.current.val, by simpa only [Nat.zero_add] using loaded.current.property⟩
  return loaded.append ((congrArg
    (fun index => Accelerated.RefinementPrefix
      (Accelerated.dyadicTrack input elimination.certificate initial) index additional)
    (Nat.zero_add first)).mpr suffix)

/-- Construct an actual loaded root after restoring the requested dyadic loaded.

The continuation receives the same finite checked entries installed in the
track before any root-dependent work. Cache misses remain the identical total
dyadic policy; loaded coverage identifies which requests are actual hits.
-/
@[expose] def prepareDyadicRoot {α : Type} (input : Input polynomial)
    (elimination : Input.Elimination input)
    (initial : WindingOneState polynomial ambient)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) (last : Nat)
    (use : (loaded : Accelerated.RefinementPrefix
      (Accelerated.dyadicTrack input elimination.certificate initial) 0 last) →
      CertifiedName (Track.Observation.withRefinements
        (Accelerated.dyadicTrack input elimination.certificate initial) loaded.entries) →
      IO α) : IO α := do
  let loaded ← dyadicRefinements input elimination initial columns winding requireSavedHeader directory
    last 0 ⟨initial, rfl⟩
  let root := certifiedName (Track.Observation.withRefinements
    (Accelerated.dyadicTrack input elimination.certificate initial) loaded.entries) input.degreePositive
  use loaded root

/-- Restore and compare a dyadic numerical source while retaining its complete original root owner.

The new root and comparison are constructed only after the exact requested
loaded has loaded. The same-initial comparison pays the new source through
that cache and never pays an old positive-index state.
-/
@[expose] def dyadicFromOriginal {α : Type} (original : CertifiedName track)
    (input : Input polynomial)
    (elimination : Input.Elimination input)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) (last : Nat)
    (use : (prepared : Accelerated.Initial input track) → prepared.original = original → IO α) : IO α := do
  let count := max 1 last
  let loaded ← dyadicRefinements input elimination track.initial columns winding requireSavedHeader directory
    count 0 ⟨track.initial, rfl⟩
  let prepared := Accelerated.fromInitial input original elimination count
    (Purelib.Data.Nat.Order.le_max_left 1 last) loaded
  use prepared rfl

namespace Power

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Power
open Purelib.RootIsolation.Power.Unit
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Progressive.Power.Unit.Rebase
open Purelib.Polynomial.Power
open Purelib.Polynomial.Power.Gaussian.Progressive
open Purelib.Polynomial.Dense.Gaussian.Bounds

/-- Restore the original robust unit-power source at its unchanged coefficient-selected occurrence.

The original initial track, source radius and canonical refinement consume the
existing raw-stage, column and winding stores. The complete state readback
identifies the original source without selecting a replacement owner. -/
def source {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : IO (Source.Preparation.Prepared nonzero unit degree degreeTwo index) := do
  let input := Isolation.isolationInput nonzero degree degreeTwo
  let track := Isolation.Track.isolatedTrack nonzero degree degreeTwo index
  let elimination := input.elimination
  let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns
    (Gaussian.rootPolynomial parameter degree) input.nonzero input.degreePositive
  let saved ← RawSubdivisionCheckpoint.refine input elimination rfl loader columns winding directory track.initial
    (Radius.unitRobustSourceRadius unit degree degreeTwo)
    (Radius.unitRobustSourceRadius_pos unit degree degreeTwo)
  return Source.Preparation.ofRefinement nonzero unit degree degreeTwo index saved

/-- Restore a robust unit-power owner from its same retained complete frame.

The original frame supplies its input, elimination certificate and indexed
track. Its saved refinement pays the original source radius; the resulting
owner consumes that exact state and keeps its complete defining readback. -/
def ownerFromFrame {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (frame : Frame.Preparation.Prepared nonzero degree degreeTwo)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : IO (Unit.Owner.Preparation.Prepared nonzero unit degree degreeTwo index) := do
  let input := frame.input
  let elimination := frame.elimination
  let retained := frame.track index
  let radius := Radius.unitRobustSourceRadius unit degree degreeTwo
  let positive := Radius.unitRobustSourceRadius_pos unit degree degreeTwo
  let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns
    (Gaussian.rootPolynomial parameter degree) input.nonzero input.degreePositive
  let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.cast frame.elimination_eq.symm loader
  let saved ← RawSubdivisionCheckpoint.refine input elimination frame.elimination_eq cachedLoader
    columns winding directory retained.val.initial radius positive
  have initialEq : retained.val.initial = (Isolation.Track.isolatedTrack nonzero degree degreeTwo index).initial :=
    congrArg Track.Basic.WindingOneTrack.initial retained.property
  let original : { value : Source.Preparation.State parameter degree // value =
    Track.Newton.Refinement.refineState
      (Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
      (Isolation.isolationInput nonzero degree degreeTwo).squarefree
      (Isolation.isolationInput nonzero degree degreeTwo).elimination
      (Isolation.Track.isolatedTrack nonzero degree degreeTwo index).initial radius positive } :=
    ⟨saved.val, (saved.property.trans (frame.refine_eq _ _ _)).trans
      (congrArg (fun current : Source.Preparation.State parameter degree =>
        Track.Newton.Refinement.refineState
          (Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
          (Isolation.isolationInput nonzero degree degreeTwo).squarefree
          (Isolation.isolationInput nonzero degree degreeTwo).elimination current radius positive) initialEq)⟩
  let source := Source.Preparation.ofRefinement nonzero unit degree degreeTwo index original
  return Unit.Owner.Preparation.fromSource nonzero unit degree degreeTwo index source

/-- Assign the original transported raw unit-power owner to its retained independent target partition.

The actual raw owner pays the unchanged partition assignment radius through
existing dyadic proposals and the total fallback. Saved header, column and
winding policies remain independent; the assignment retains the supplied
refinement and original source and target owners. -/
def assignment {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Coefficients.coefficientTable target degree).degree)
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (prepared : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (savedOnly : Bool) (directory : System.FilePath) :
    IO (Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small index) := do
  let polynomial := Gaussian.rootPolynomial target degree
  let ambient := RootRadius.Box.largeSquareBox polynomial
  let input := targetFrame.input
  let elimination := targetFrame.elimination
  let raw := Unit.Move.Track.Preparation.rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared
  let radius := Exact.Ownership.Radius.assignmentRadius polynomial ambient targetFrame.isolation
  let positive := Exact.Ownership.Radius.assignmentRadius_pos polynomial ambient targetFrame.isolation
  let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns polynomial input.nonzero
    input.degreePositive
  let cachedLoader := RootRefinementCheckpoint.ClearanceLoader.cast targetFrame.elimination_eq.symm loader
  let refined ← RawRefinementCheckpoint.refine input elimination targetFrame.elimination_eq cachedLoader
    columns winding savedOnly directory raw.val radius positive
  return Matching.Preparation.fromRawReadbacks
    sourceUnit targetUnit degree degreeTwo small index targetFrame raw refined.val

end Power

end CoherentRootCheckpoint
