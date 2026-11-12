module

import Purelib.System.IO.Reference

public import scripts.checkpoint.CoherentRootSamples
import Purelib.System.IO
import Purelib.System.FilePath
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Init.System.IO
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Purelib.Riemann.RootContinuation.CoherentRoot.PointSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Positive.Input
import scripts.checkpoint.RootSelection
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot

/-! # Exact original state readbacks and memoized saved-reader control -/

namespace TestPurelib.Riemann.RootStateCache

open Purelib

open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Provenance
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open CoherentRootCheckpoint
open Purelib.System.IO (StateExecution)
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_pos)
open Purelib.Polynomial.Dense.Gaussian.Factorization
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)

variable {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
  {track : CoherentRoot.WindingOneTrack polynomial ambient}

example (root : CoherentRoot.CertifiedName track) (index : Nat) (current : State root index)
    (remaining : List (CoherentRoot.StateCache.Entry track)) :
    findState root index (stateEntry root index current :: remaining) = some current := by
  unfold findState stateEntry
  rewrite [dif_pos rfl]
  rfl

example (root : CoherentRoot.CertifiedName track) (index : Nat) :
    findState root index [] = none := rfl

example (root : CoherentRoot.CertifiedName track) (index : Nat) (current : State root index) :
    (stateEntry root index current).value.get = current.val := rfl

example (root : CoherentRoot.CertifiedName track) :
    stateEntry root 0 ⟨track.initial, (root.stateAt_eq 0).symm⟩ =
      CoherentRoot.StateCache.first track := rfl

example (root : CoherentRoot.CertifiedName track) (index stage : Nat) (different : stage ≠ index)
    (current : State root stage) (remaining : List (CoherentRoot.StateCache.Entry track)) :
    findState root index (stateEntry root stage current :: remaining) = findState root index remaining := by
  unfold findState stateEntry
  rewrite [dif_neg different]
  cases remaining with
  | nil => rfl
  | cons head tail => rfl

example (root : CoherentRoot.CertifiedName track) (states : (index : Nat) → IO (State root index))
    (directory : System.FilePath) (start : Nat) (target : CoherentRoot.Coordinate) (positive : 0 < target) :
    IO { value : CoherentRoot.Refinement root start //
      value = CoherentRoot.Refinement.ofTarget root start target positive } :=
  ofTargetWithStates root states directory start target positive

example (root : CoherentRoot.CertifiedName track) (start : Nat)
    (target : CoherentRoot.Coordinate) (positive : 0 < target)
    (paid : { value : CoherentRoot.Refinement root start //
      value = CoherentRoot.Refinement.ofTarget root start target positive }) :
    paid.val = CoherentRoot.Refinement.ofTarget root start target positive := paid.property

example (root : CoherentRoot.CertifiedName track)
    (input : Input polynomial) (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
        input.elimination current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (start : Nat) (target : CoherentRoot.Coordinate) (positive : 0 < target)
    (maximum : Nat) (maximumEq : maximum = root.approximation.refineIndex start target positive)
    (remaining index : Nat) (indexGe : start ≤ index) (balance : index + remaining = maximum)
    (current : State root index) :
    search root input elimination canonical columns winding directory start target positive maximum maximumEq
      remaining index indexGe balance current =
      searchWithStates root (nextState root input elimination canonical columns winding directory) directory start
        target positive maximum maximumEq remaining index indexGe balance current := rfl

/-- The exact retained original entries and the attempted successor count of one finite test. -/
private abbrev Cache (track : CoherentRoot.WindingOneTrack polynomial ambient) :=
  List (CoherentRoot.StateCache.Entry track) × Nat

/-- Read the original entry list without changing either finite test component. -/
private def readEntries : StateExecution (Cache track) (List (CoherentRoot.StateCache.Entry track)) := do
  return (← getThe (Cache track)).1

/-- Replace only the original entry list while retaining the actual successor count. -/
private def writeEntries (entries : List (CoherentRoot.StateCache.Entry track)) : StateExecution (Cache track) Unit :=
  modifyThe (Cache track) fun cache => (entries, cache.2)

/-- Check that a replay reader keeps the supplied completed prefix instead of replacing it with an empty bank.

The read action permits only an existing entry and uses no write accessor.
Repeated reads therefore test reuse of the actual supplied state
without invoking any numerical successor or creating a checkpoint store.
-/
public def checkSeededReader (root : CoherentRoot.CertifiedName track) : IO Unit := do
  let current : State root 0 := ⟨track.initial, (root.stateAt_eq 0).symm⟩
  let attempts ← System.IO.mkRef (0 : Nat)
  let read ← stateReader root (fun getEntries _ index => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    let values ← getEntries
    unless values.length = 1 do throw (IO.userError "the supplied original state bank was replaced")
    match findState root index values with
    | some found => pure found
    | none => throw (IO.userError "the supplied original state was discarded before replay"))
    [stateEntry root 0 current]
  let first ← read 0
  let second ← read 0
  unless first.val.box.anchor = current.val.box.anchor ∧ second.val.box.anchor = current.val.box.anchor ∧
      (← System.IO.Ref.get attempts) = 2 do
    throw (IO.userError "repeated reads failed to consume the same supplied original state bank")

/-- Check repeated original initial-state hits and a failed successor without executing any refinement.

The supplied successor only increments the finite counter and fails. The
error-preserving execution retains that counter and the same checked initial
entry for later hits. An empty supplied entry list restores only that initial
state, without invoking any numerical successor.
-/
public def checkInitialHits (root : CoherentRoot.CertifiedName track) : IO Unit := do
  let initial : State root 0 := ⟨track.initial, (root.stateAt_eq 0).symm⟩
  let successor : (index : Nat) → State root index → StateExecution (Cache track) (State root (index + 1)) :=
    fun _ _ => do
      modifyThe (Cache track) fun cache => (cache.1, cache.2 + 1)
      throw (IO.userError "intentional absent saved successor")
  let read := readStateWith root successor readEntries writeEntries
  let action : StateExecution (Cache track) Unit := do
    let first ← read 0
    let second ← read 0
    let cache ← getThe (Cache track)
    unless cache.2 = 0 ∧ cache.1.length = 1 do
      throw (IO.userError "an original initial cache hit invoked a successor or changed the cache")
    unless first.val.box.anchor = track.initial.box.anchor ∧ second.val.box.anchor = first.val.box.anchor do
      throw (IO.userError "an original initial cache hit changed its retained state")
    let failed ← try
        let _ ← read 1
        pure false
      catch _ => pure true
    let cache ← getThe (Cache track)
    unless failed ∧ cache.2 = 1 ∧ cache.1.length = 1 do
      throw (IO.userError "an absent saved successor did not preserve the original checked prefix and attempt count")
    let again ← read 0
    let cache ← getThe (Cache track)
    unless again.val.box.anchor = first.val.box.anchor ∧ cache.2 = 1 do
      throw (IO.userError "a cache hit after an absent successor repeated its failing action")
    writeEntries []
    let restored ← read 0
    let retained ← read 0
    let cache ← getThe (Cache track)
    unless restored.val.box.anchor = initial.val.box.anchor ∧ retained.val.box.anchor = initial.val.box.anchor ∧
        cache.1.length = 1 ∧ cache.2 = 1 do
      throw (IO.userError "restoring the original initial state from an empty cache invoked a successor")
  let (result, _) ← (StateExecution.run action ([stateEntry root 0 initial], 0)).toIO
  match result with
  | .ok _ => pure ()
  | .error error => throw error
  let attempts ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "intentional exact successor-reader failure"
  let directory := System.FilePath.mk "unused-original-successor"
  let refine : (path : System.FilePath) → (current : CoherentRoot.WindingOneState polynomial ambient) →
      (epsilon : CoherentRoot.Coordinate) → (positive : 0 < epsilon) →
      IO {value : CoherentRoot.WindingOneState polynomial ambient //
        value = track.refine current epsilon positive} := fun path current epsilon _ => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    unless path.toString = (Purelib.System.FilePath.join directory "state-1").toString ∧
        current.box.anchor = initial.val.box.anchor ∧
        epsilon = Purelib.Data.Rat.Bounds.AccuracyRadius.accuracyRadius (CoherentRoot.stepTarget track 0) do
      throw (IO.userError "shared successor reader changed its original directory, predecessor or accuracy")
    throw absent
  try
    let _ ← nextStateUsing root refine directory 0 initial
    throw (IO.userError "shared successor reader returned after its actual refinement failed")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
  unless (← System.IO.Ref.get attempts) = 1 do
    throw (IO.userError "shared successor reader repeated or skipped its original refinement action")

/-- Check one original nonroot-point request's exact maximum stage and unchanged state-reader failure.

The reader increments its finite counter, checks the coefficient-derived stage
and fails without producing a state. The complete point-separation adapter must
preserve that error after exactly one call, without executing a root producer.
-/
public def checkPointReaderFailure (root : CoherentRoot.CertifiedName track)
    (point value : CoherentRoot.Gaussian) (valueEq : polynomial.eval point = value) (nonzero : value ≠ 0)
    (start : Nat) : IO Unit := do
  let norm := normSq value
  have normPositive : 0 < norm := normSq_pos nonzero
  let radius := Uniform.uniformExclusionRadius polynomial ambient norm
  have radiusPositive := Uniform.uniformExclusionRadius_pos polynomial ambient normPositive
  let target := radius ^ 2
  have positive := Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2
  let expected := root.approximation.refineIndex start target positive
  let attempts ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "intentional original point-separation state-reader failure"
  let states : (index : Nat) → IO (State root index) := fun index => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    unless index = expected ∧ start ≤ index do
      throw (IO.userError "point separation changed its original coefficient request or sufficient stage")
    throw absent
  try
    let _ ← CoherentRoot.PointSeparation.ofValueWithStates root point value valueEq nonzero start states
    throw (IO.userError "point separation returned after its actual original state read failed")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
  unless (← System.IO.Ref.get attempts) = 1 do
    throw (IO.userError "point separation repeated or skipped its original maximum-stage state read")

/-- Check that disabled inspections reach only the original nonlinear source loader and preserve its failure.

The same squarefree root occupies both inputs at distinct original floors.
A controlled source-elimination miss records the whole attempted stage and
skips both state readers and the final preparation callback. No numerical
producer or checkpoint store is used.
-/
public def checkGlobalPreparationFailure (root : CoherentRoot.CertifiedName track)
    (input : Input polynomial) : IO Unit := do
  let trace ← System.IO.mkRef ([] : List String)
  let absent := IO.userError "intentional original common-source elimination miss"
  let states (label : String) : (index : Nat) → IO (State root index) := fun _ => do
    System.IO.Ref.modify trace (fun events => events ++ [label])
    throw (IO.userError "global preparation read an input state before restoring its original partition")
  let control ← RootRefinementCheckpoint.Control.create true
  try
    withPreparedComparison input.toPositive input.toPositive root root 0 3
      (fun _ _ => do
        System.IO.Ref.modify trace (fun events => events ++ ["source-elimination"])
        throw absent)
      { savedOnly := true } { savedOnly := true } control
      (System.FilePath.mk "unused-original-global-comparison") (states "first") (states "second") false false
      (fun _ => do
        System.IO.Ref.modify trace (fun events => events ++ ["completed-preparation"])
        throw (IO.userError "global preparation called its continuation after the source loader failed"))
    throw (IO.userError "global preparation returned after the original source loader failed")
  catch error =>
    unless (System.IO.Error.toString error) = (System.IO.Error.toString absent) do throw error
  unless (← System.IO.Ref.get trace) == ["source-elimination"] do
    throw (IO.userError "global preparation changed its original disabled-guard order or repeated its failed loader")

/-- Check that original algebraic root-view replay preserves a bank-loader failure before all numerical requests.

Both complete sidecars retain the same actual isolated root at floors zero
and three. All ordinary inspection bits remain enabled. A controlled bank
failure must skip elimination, state requests and the comparison callback.
-/
public def checkSidecarReaderFailure (root : CoherentRoot.CertifiedName track)
    (input : Input polynomial) : IO Unit := do
  let trace ← System.IO.mkRef ([] : List String)
  let absent := IO.userError "intentional original algebraic input-bank miss"
  let sidecar := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root input.toPositive)
  let control ← RootRefinementCheckpoint.Control.create true
  try
    RootSelectionCheckpoint.compareSidecars sidecar sidecar 0 3
      (fun _ => do
        System.IO.Ref.modify trace (fun events => events ++ ["input-banks"])
        throw absent)
      (fun _ _ _ => do
        System.IO.Ref.modify trace (fun events => events ++ ["source-elimination"])
        throw (IO.userError "algebraic replay forced source elimination after its input-bank failure"))
      { savedOnly := true } { savedOnly := true } control (System.FilePath.mk "unused-original-sidecar-comparison")
      true true true (fun _ => do
        System.IO.Ref.modify trace (fun events => events ++ ["completed-comparison"])
        throw (IO.userError "algebraic replay called its continuation after the bank loader failed"))
    throw (IO.userError "algebraic replay returned after its original bank loader failed")
  catch error =>
    unless (System.IO.Error.toString error) = (System.IO.Error.toString absent) do throw error
  unless (← System.IO.Ref.get trace) == ["input-banks"] do
    throw (IO.userError "algebraic replay repeated or skipped its original input-bank loader")

/-- Check a cached original source region and the unchanged failure of its global protection request.

The local presentation consumes one supplied original initial state, retaining
its target, stage, clearances and complete source region. A separate global
request preserves its sufficient stage and reader error after one call, without
producing any refinement or numerical checkpoint.
-/
public def checkSourceRegion (root : CoherentRoot.CertifiedName track)
    (source cofactor : CoherentRoot.GaussianPolynomial) (nonzero : source.isZero = false)
    (factorization : Identity.ProductIdentity source polynomial cofactor)
    (coprime : CoprimeCertificate polynomial cofactor)
    (requested : CoherentRoot.FactorRegion.LocalCofactor cofactor track.initial.box) : IO Unit := do
  let calls ← System.IO.mkRef (0 : Nat)
  let initial : (index : Nat) → IO (State root index) := fun index => do
    System.IO.Ref.modify calls (fun count => count + 1)
    if zero : index = 0 then
      return ⟨track.initial, by cases zero; exact (root.stateAt_eq 0).symm⟩
    else
      throw (IO.userError "the original local source region changed its initial-stage request")
  let restored ← CoherentRoot.FactorRegion.ofRootWithStates root source cofactor nonzero factorization
    coprime 0 (some requested) initial
  let certificate := restored.val
  unless (← System.IO.Ref.get calls) = 1 ∧ certificate.index = 0 ∧ certificate.localCofactor.isSome ∧
      certificate.targetSq = root.approximation.radiusSq 0 + 1 ∧
      certificate.current.box.anchor = track.initial.box.anchor ∧
      certificate.region.box.anchor = certificate.current.box.anchor ∧
      certificate.region.clearance.bound = certificate.current.clearance.bound * certificate.cofactorClearance.bound do
    throw (IO.userError "the cached source region lost its original state, cofactor request or product clearance")
  let _completeOriginal := restored.property
  let start := 3
  let target := CoherentRoot.FactorRegion.target root coprime start none
  have positive := CoherentRoot.FactorRegion.target_pos root coprime start none
  let expected := root.approximation.refineIndex start target positive
  let attempts ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "intentional original source-region reader failure"
  let states : (index : Nat) → IO (State root index) := fun index => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    unless index = expected ∧ start ≤ index do
      throw (IO.userError "source protection changed its original sufficient stage or start")
    throw absent
  try
    let _ ← CoherentRoot.FactorRegion.ofRootWithStates root source cofactor nonzero factorization
      coprime start none states
    throw (IO.userError "source region returned after its original state read failed")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
  unless (← System.IO.Ref.get attempts) = 1 do
    throw (IO.userError "source protection repeated or skipped its original state reader")

/-- Check repeated original named readings whose canonical primitive index is the original initial state.

The shared reader writes that initial entry once. A later absent successor
preserves it and the actual error; another named read uses the same bank.
No root refinement or numerical checkpoint is produced by this test.
-/
public def checkNamedInitial (root : CoherentRoot.CertifiedName track) (named : Nat)
    (zero : Equivalence.Sampling.emittedSampleIndex root.approximation named = 0)
    (input : FTA.Positive.Input.PositiveInput polynomial) : IO Unit := do
  let writes ← System.IO.mkRef (0 : Nat)
  let attempts ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "intentional absent named-observation successor"
  let successor : (index : Nat) → State root index → IO (State root (index + 1)) := fun _ _ => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    throw absent
  let read ← stateReader root fun getEntries setEntries index =>
    readStateWith root successor getEntries (fun entries => do
      System.IO.Ref.modify writes (fun count => count + 1)
      setEntries entries) index
  let first ← namedSampleWithStates root read named
  let view := CoherentRoot.CertifiedName.View.ofRoot root input
  let second ← namedSampleWithView view rfl read named
  unless first.val.index = named ∧ second.val.index = named ∧
      first.val.value = track.initial.box.anchor ∧ second.val.value = first.val.value ∧
      (← System.IO.Ref.get writes) = 1 ∧ (← System.IO.Ref.get attempts) = 0 do
    throw (IO.userError "repeated original named reads changed their index, anchor or shared initial entry")
  have _originalIndex := zero
  let failed ← try
      let _ ← read 1
      pure false
    catch failure =>
      unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
      pure true
  let retained ← namedSampleWithView view rfl read named
  unless failed ∧ retained.val.index = named ∧ retained.val.value = first.val.value ∧
      (← System.IO.Ref.get writes) = 1 ∧ (← System.IO.Ref.get attempts) = 1 do
    throw (IO.userError "an absent successor discarded or rebuilt the original named observation bank")

/-- Check one exact named-to-primitive request and preserve its state reader's failure.

The supplied reader records the unchanged canonical primitive index and fails
once. No state producer or fallback named observation is evaluated afterward.
-/
public def checkNamedReaderFailure (root : CoherentRoot.CertifiedName track) (named : Nat)
    (input : FTA.Positive.Input.PositiveInput polynomial) : IO Unit := do
  let expected := Equivalence.Sampling.emittedSampleIndex root.approximation named
  let attempts ← System.IO.mkRef (0 : Nat)
  let absent := IO.userError "intentional original named-observation reader failure"
  let states : (index : Nat) → IO (State root index) := fun index => do
    System.IO.Ref.modify attempts (fun count => count + 1)
    unless index = expected do
      throw (IO.userError "named observation changed its original canonical primitive index")
    throw absent
  try
    let view := CoherentRoot.CertifiedName.View.ofRoot root input
    let _ ← namedSampleWithView view rfl states named
    throw (IO.userError "named observation returned after its original state reader failed")
  catch failure =>
    unless (System.IO.Error.toString failure) = (System.IO.Error.toString absent) do throw failure
  unless (← System.IO.Ref.get attempts) = 1 do
    throw (IO.userError "named observation repeated or skipped its original primitive-state request")

/-- Check that one supplied exact original successor survives repeated reads and a later absent successor.

The supplied state is already authenticated at original index one. The finite
successor retains it once; its index-two branch only increments the counter
and fails. Both completed entries and the attempted count survive that error,
and this test creates no root, refinement or numerical request.
-/
public def checkOneRestore (root : CoherentRoot.CertifiedName track) (saved : State root 1) : IO Unit := do
  let initial : State root 0 := ⟨track.initial, (root.stateAt_eq 0).symm⟩
  let successor : (index : Nat) → State root index → StateExecution (Cache track) (State root (index + 1))
    | 0, _ => do
        modifyThe (Cache track) fun cache => (cache.1, cache.2 + 1)
        return saved
    | _ + 1, _ => do
        modifyThe (Cache track) fun cache => (cache.1, cache.2 + 1)
        throw (IO.userError "no second saved successor was supplied")
  let read := readStateWith root successor readEntries writeEntries
  let action : StateExecution (Cache track) Unit := do
    let first ← read 1
    let second ← read 1
    let zero ← read 0
    let cache ← getThe (Cache track)
    unless cache.2 = 1 ∧ cache.1.length = 2 do
      throw (IO.userError "the same exact original successor was restored more than once or lost its predecessor")
    unless first.val.box.anchor = saved.val.box.anchor ∧ second.val.box.anchor = saved.val.box.anchor ∧
        zero.val.box.anchor = track.initial.box.anchor do
      throw (IO.userError "the retained original predecessor or successor changed on a repeated read")
    let failed ← try
        let _ ← read 2
        pure false
      catch _ => pure true
    let cache ← getThe (Cache track)
    unless failed ∧ cache.2 = 2 ∧ cache.1.length = 2 do
      throw (IO.userError "a later absent successor discarded the completed original state or attempted count")
    let retained ← read 1
    let cache ← getThe (Cache track)
    unless retained.val.box.anchor = saved.val.box.anchor ∧ cache.2 = 2 ∧ cache.1.length = 2 do
      throw (IO.userError "a retained successor was repeated after a later saved-only failure")
  let (result, _) ← (StateExecution.run action ([stateEntry root 0 initial], 0)).toIO
  match result with
  | .ok _ => pure ()
  | .error error => throw error

end TestPurelib.Riemann.RootStateCache
