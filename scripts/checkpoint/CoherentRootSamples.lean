module

import Purelib.System.IO.Reference

public import scripts.checkpoint.CoherentRoot
public import Purelib.Riemann.RootContinuation.CoherentRoot.SamplePrefix
public import Purelib.Riemann.RootContinuation.CoherentRoot.Family
public import Purelib.Riemann.RootContinuation.CoherentRoot.CommonSource
public import Purelib.System.IO
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Elimination.Axis.Preparation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import scripts.checkpoint.InitialExtraction
import Init.System.IO
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Union
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.Riemann.RootContinuation.CoherentRoot.PairSeparation
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.System.FilePath
import Purelib.Data.Nat.Order
import Purelib.RootIsolation.FTA.Squarefree.Input

/-! # Original root-state caches, checked observations and comparison preparation -/

public section

namespace CoherentRootCheckpoint

open Purelib

open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Approximation.Gaussian
open Purelib.System.IO (StateExecution)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot
open StateCache (FamilyEntries)
open Purelib.Polynomial.Elimination.Axis.Preparation renaming Prepared -> AxisPreparation
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Dense.Gaussian

variable {polynomial : GaussianPolynomial} {ambient : Box}
  {track : WindingOneTrack polynomial ambient}

/-- Restore the complete original partition on the support enclosing the supplied finite box list.

The actual isolation supplies its original ordered tracks and one root cache
per track. Its entire partition equals the default constructor, while the
supplied elimination and numerical policies serve every checked reload.
-/
def withPartition {α : Type} (input : Input polynomial) (boxes : List Box)
    (elimination : Input.Elimination input)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : {partition : Partition input (RootRadius.Box.enclosingSquare polynomial boxes) //
      partition = Partition.ofBoxes input boxes} → IO α) : IO α := do
  let saved ← InitialExtractionCheckpoint.separatedSymmetricWithElimination input elimination
    (RootRadius.Box.enclosingRadius_ge_coefficients polynomial boxes) columns winding control directory
  let partition : Partition input (RootRadius.Box.enclosingSquare polynomial boxes) :=
    { output := saved.val
      support_eq := by rewrite [saved.property]; rfl
      roots := Family.ofTracks input.degreePositive saved.val.tracks }
  have same : partition = Partition.ofBoxes input boxes := by
    rcases elimination with ⟨degree, degreeEq, certificate, same⟩
    cases degreeEq
    cases same
    rcases saved with ⟨saved, original⟩
    cases original
    rfl
  use ⟨partition, same⟩

/-- Compare two original root caches in their restored original common-source partition.

The supplied nonlinear union, both ambient boxes and the exact elimination
index the restored support. The actual partition feeds the same protection
and assignment readers; its whole default identity accompanies the complete
comparison. Any failed reload skips subsequent state reads and the callback.
-/
def withCommonSourceComparison {α : Type} {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
    (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial)
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)
    (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (degree : 2 ≤ algebra.polynomial.natDegree)
    (elimination : Input.Elimination (Input.mk algebra.squarefree degree))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (firstStates : (index : Nat) → IO (State first index))
    (secondStates : (index : Nat) → IO (State second index))
    (use : (source : {source : CommonSource firstInput secondInput [firstAmbient, secondAmbient] //
      source = CommonSource.ofUnion firstInput secondInput [firstAmbient, secondAmbient] algebra degree}) →
      {result : CommonSource.ComparisonResult source.val first second firstStart secondStart //
        result = source.val.compare first second firstStart secondStart
          (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))} → IO α) : IO α := do
  let input : Input algebra.polynomial := ⟨algebra.squarefree, degree⟩
  withPartition input [firstAmbient, secondAmbient] elimination columns winding control directory fun partition => do
    let source := CommonSource.ofUnionWithPartition firstInput secondInput [firstAmbient, secondAmbient]
      algebra degree partition.val
    have same := CommonSource.ofUnionWithPartition_eq firstInput secondInput [firstAmbient, secondAmbient]
      algebra degree partition.val partition.property
    source.compareWithStates first second firstStart secondStart
      (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) firstStates secondStates
      (fun result => use ⟨source, same⟩ result)

section Comparison

open CommonSource (Preparation PreparedComparison)
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.System.FilePath (join)
open Purelib.Data.Nat

variable {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
  {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
  {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
  (firstInput : FTA.Positive.Input.PositiveInput firstPolynomial)
  (secondInput : FTA.Positive.Input.PositiveInput secondPolynomial)
  (first : CertifiedName firstTrack) (second : CertifiedName secondTrack) (firstStart secondStart : Nat)

/-- Restore the original union's complete linear or nonlinear preparation.

Only the nonlinear branch invokes the supplied elimination loader and source
partition. Both original state readers feed that actual restored partition.
-/
private def withUnionPreparation {α : Type} (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (readElimination : (source : Squarefree.Union firstPolynomial secondPolynomial) →
      (degree : 2 ≤ source.polynomial.natDegree) → IO (Input.Elimination (Input.mk source.squarefree degree)))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (firstStates : (index : Nat) → IO (State first index))
    (secondStates : (index : Nat) → IO (State second index))
    (use : {value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra} → IO α) :
    IO α := do
  if sourceDegree : algebra.polynomial.natDegree = 1 then
    use ⟨Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra, rfl⟩
  else
    have positive : 0 < algebra.polynomial.natDegree :=
      firstInput.degreePositive.trans_le algebra.degree_ge_first
    have degree : 2 ≤ algebra.polynomial.natDegree :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_ne positive (Ne.symm sourceDegree))
    let elimination ← readElimination algebra degree
    withCommonSourceComparison firstInput secondInput first second firstStart secondStart algebra degree
      elimination columns winding control directory firstStates secondStates fun source compared => do
      have sameAlgebra : source.val.algebra = algebra := by
        rcases source with ⟨source, same⟩
        cases same
        rfl
      let result : Preparation firstInput secondInput first second firstStart secondStart algebra :=
        .partition source.val sameAlgebra compared.val
      have original : result =
          Preparation.ofUnion firstInput secondInput first second firstStart secondStart algebra := by
        rcases source with ⟨source, same⟩
        cases same
        rcases compared with ⟨compared, same⟩
        cases same
        unfold Preparation.ofUnion
        rewrite [dif_neg sourceDegree]
        rfl
      use ⟨result, original⟩

/-- Restore original local preparation from both actual requested floor states.

Separation precedes the shared cofactor inspection. The same protected state
and second floor payment feed local comparison; each miss invokes only the
supplied complete fallback action.
-/
private def withLocalPreparation {α : Type} (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectLocal : Bool)
    (fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra)
    (unavailable : ({value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = fallback ()} → IO α) → IO α)
    (firstStates : (index : Nat) → IO (State first index))
    (secondStates : (index : Nat) → IO (State second index))
    (use : {value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = Preparation.checkLocal firstInput secondInput first second firstStart secondStart
        algebra inspectLocal fallback} → IO α) : IO α := do
  let miss (same : Preparation.checkLocal firstInput secondInput first second firstStart secondStart
      algebra inspectLocal fallback = fallback ()) : IO α :=
    unavailable fun saved => use ⟨saved.val, saved.property.trans same.symm⟩
  if enabled : inspectLocal = true then
    let left ← firstStates firstStart
    let right ← secondStates secondStart
    if separated : left.val.box.Separated right.val.box then
      let result : Preparation firstInput secondInput first second firstStart secondStart algebra :=
        .separated (PairSeparation.ofStates first second firstStart secondStart
          left.val right.val left.property right.property separated)
      have original : result = Preparation.checkLocal firstInput secondInput first second firstStart secondStart
          algebra inspectLocal fallback := by
        rcases left with ⟨left, leftEq⟩
        cases leftEq
        rcases right with ⟨right, rightEq⟩
        cases rightEq
        unfold Preparation.checkLocal
        rewrite [enabled]
        dsimp only
        rewrite [dif_pos separated]
        rfl
      use ⟨result, original⟩
    else
      match scanned : Preparation.localCofactor? (firstTrack := firstTrack) algebra with
      | none =>
          miss (by
            rcases left with ⟨left, leftEq⟩
            cases leftEq
            rcases right with ⟨right, rightEq⟩
            cases rightEq
            unfold Preparation.checkLocal
            rewrite [enabled]
            dsimp only
            rewrite [dif_neg separated, scanned]
            rfl)
      | some inspected =>
          let cofactor := inspected.val
          let same := inspected.property.1
          let degree := inspected.property.2
          let region ← FactorRegion.ofRootWithStates first algebra.polynomial algebra.result.qFactor
            algebra.nonzero algebra.firstFactorization algebra.firstCoprime firstStart (some cofactor) firstStates
          match nesting : region.val.initialNesting? second with
          | none =>
              miss (by
                rcases left with ⟨left, leftEq⟩
                cases leftEq
                rcases right with ⟨right, rightEq⟩
                cases rightEq
                rcases region with ⟨region, regionEq⟩
                cases regionEq
                unfold Preparation.checkLocal
                rewrite [enabled]
                dsimp only
                rewrite [dif_neg separated, scanned]
                dsimp only
                rewrite [nesting]
                rfl)
          | some inside =>
              let paidRight := Refinement.atFloor second secondStart right.val right.property
              have paidRightEq : paidRight =
                  Refinement.atFloor second secondStart (second.stateAt secondStart) rfl := by
                rcases right with ⟨right, rightEq⟩
                cases rightEq
                rfl
              let compared := Preparation.localComparison (secondInput := secondInput)
                (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
                degree same region.val inside paidRight
              let result : Preparation firstInput secondInput first second firstStart secondStart algebra :=
                .cofactor same degree cofactor region.val region.property inside paidRight paidRightEq compared rfl
              have original : result = Preparation.checkLocal firstInput secondInput first second
                  firstStart secondStart algebra inspectLocal fallback := by
                rcases left with ⟨left, leftEq⟩
                cases leftEq
                rcases right with ⟨right, rightEq⟩
                cases rightEq
                rcases region with ⟨region, regionEq⟩
                cases regionEq
                unfold Preparation.checkLocal
                rewrite [enabled]
                dsimp only
                rewrite [dif_neg separated, scanned]
                dsimp only
                rewrite [nesting]
                rfl
              use ⟨result, original⟩
  else
    have disabled : inspectLocal = false := by
      cases inspectLocal with
      | false => rfl
      | true => exact False.elim (enabled rfl)
    miss (by unfold Preparation.checkLocal; rewrite [disabled]; rfl)

/-- Restore the original enclosing winding and its same protected factor region.

The shared hull inspection runs before any winding loader. Only winding four
pays protection at zero; every other result invokes the same local attempt.
-/
private def withEnclosingPreparation {α : Type} (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectLocal : Bool)
    (fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra)
    (unavailable : ({value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = fallback ()} → IO α) → IO α)
    (winding : WindingCheckpoint.Control IO) (directory : System.FilePath)
    (firstStates : (index : Nat) → IO (State first index))
    (use : {value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = Preparation.checkEnclosing firstInput secondInput first second firstStart secondStart
        algebra inspectLocal fallback} → IO α) : IO α := do
  let miss (same : Preparation.checkEnclosing firstInput secondInput first second firstStart secondStart
      algebra inspectLocal fallback = fallback ()) : IO α :=
    unavailable fun saved => use ⟨saved.val, saved.property.trans same.symm⟩
  match scanned : Preparation.enclosingCofactor? (firstTrack := firstTrack) (secondTrack := secondTrack)
      algebra inspectLocal with
  | none => miss (by unfold Preparation.checkEnclosing; rewrite [scanned]; rfl)
  | some inspected =>
      let cofactor := inspected.val
      let same := inspected.property.2.1
      let degree := inspected.property.2.2.1
      let withinSource := inspected.property.2.2.2.1
      let withinFactor := inspected.property.2.2.2.2
      let container := Preparation.enclosingRegion (firstTrack := firstTrack) (secondTrack := secondTrack)
        algebra same cofactor withinSource withinFactor
      let checked ← WindingCheckpoint.box winding directory secondPolynomial container.box
      if one : checked.val = 4 then
        let region ← FactorRegion.ofRootWithStates first algebra.polynomial algebra.result.qFactor
          algebra.nonzero algebra.firstFactorization algebra.firstCoprime 0
          (some (cofactor.ofRefines (Rational.Box.Hull.left_refines _ _))) firstStates
        let compared := Preparation.enclosingComparison secondInput first second firstStart secondStart
          algebra same degree cofactor withinSource withinFactor container rfl
          (checked.property.symm.trans one) region.val
        let result : Preparation firstInput secondInput first second firstStart secondStart algebra :=
          .enclosing same degree cofactor withinSource withinFactor container rfl checked.val checked.property one
            region.val region.property compared rfl
        have original : result = Preparation.checkEnclosing firstInput secondInput first second
            firstStart secondStart algebra inspectLocal fallback := by
          rcases checked with ⟨checked, windingEq⟩
          cases windingEq
          rcases region with ⟨region, regionEq⟩
          cases regionEq
          unfold Preparation.checkEnclosing
          rewrite [scanned]
          dsimp only
          rewrite [dif_pos one]
          rfl
        use ⟨result, original⟩
      else
        have notOne : ¬ Winding.Box.Basic.quadrupledBoxWinding
            secondPolynomial container.box = 4 := fun original => one (checked.property.trans original)
        miss (by
          unfold Preparation.checkEnclosing
          rewrite [scanned]
          dsimp only
          rewrite [dif_neg notOne]
          rfl)

/-- Restore both original first-accurate unit payments after the shared initial guards succeed.

Both readers keep their original starts and run in input order. The retained
payments give the complete default nested preparation; a failed shared guard
invokes only the supplied unavailable suffix.
-/
private def withInitialPreparation {α : Type} (algebra : Squarefree.Union firstPolynomial secondPolynomial)
    (inspectInitial : Bool)
    (fallback : Unit → Preparation firstInput secondInput first second firstStart secondStart algebra)
    (unavailable : ({value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = fallback ()} → IO α) → IO α)
    (directory : System.FilePath)
    (firstStates : (index : Nat) → IO (State first index))
    (secondStates : (index : Nat) → IO (State second index))
    (use : {value : Preparation firstInput secondInput first second firstStart secondStart algebra //
      value = Preparation.checkInitial firstInput secondInput first second firstStart secondStart
        algebra inspectInitial fallback} → IO α) : IO α := do
  match scanned : Preparation.initialDecision (firstTrack := firstTrack) (secondTrack := secondTrack)
      inspectInitial with
  | .isFalse _ =>
      unavailable fun saved => use ⟨saved.val, by
        unfold Preparation.checkInitial
        rewrite [scanned]
        exact saved.property⟩
  | .isTrue passed =>
      let polynomialEq := passed.2.1
      let endpoints := passed.2.2.1
      let degree := passed.2.2.2.1
      let inside := passed.2.2.2.2
      let left ← ofTargetWithStates first firstStates (join directory "first")
        firstStart 1 (by decide)
      let right ← ofTargetWithStates second secondStates (join directory "second")
        secondStart 1 (by decide)
      let ambientEq := Rational.Box.ext
        endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2
      let compared := Preparation.nestedComparison (firstInput := firstInput)
        (first := first) (second := second) (firstStart := firstStart) (secondStart := secondStart)
        polynomialEq ambientEq degree inside left.val right.val
      let result : Preparation firstInput secondInput first second firstStart secondStart algebra :=
        .nested polynomialEq ambientEq degree inside left.val right.val compared rfl
      have original : result = Preparation.checkInitial firstInput secondInput first second
          firstStart secondStart algebra inspectInitial fallback := by
        rcases left with ⟨left, leftEq⟩
        cases leftEq
        rcases right with ⟨right, rightEq⟩
        cases rightEq
        unfold Preparation.checkInitial
        rewrite [scanned]
        rfl
      use ⟨result, original⟩

/-- Restore the complete original comparison preparation through supplied exact state and elimination readers.

The original Euclidean union, request bits, guard order, starting floors and
fallback remain unchanged. Only a selected nonlinear fallback asks for its
elimination and partition. Successful replay retains the complete original
preparation and outcome; any loader error skips all subsequent actions.
-/
def withPreparedComparison {α : Type}
    (sourceElimination : (algebra : Squarefree.Union firstPolynomial secondPolynomial) →
      (degree : 2 ≤ algebra.polynomial.natDegree) → IO (Input.Elimination (Input.mk algebra.squarefree degree)))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (firstStates : (index : Nat) → IO (State first index))
    (secondStates : (index : Nat) → IO (State second index))
    (inspectInitial inspectLocal : Bool)
    (use : {value : PreparedComparison firstInput secondInput first second firstStart secondStart //
      value = CommonSource.prepareComparison firstInput secondInput first second firstStart secondStart
        inspectInitial inspectLocal} → IO α) : IO α := do
  let algebra := Squarefree.Union.ofInputs firstPolynomial secondPolynomial
    firstInput.nonzero secondInput.nonzero firstInput.squarefree secondInput.squarefree
  let fallback := fun _ : Unit => Preparation.ofUnion firstInput secondInput first second
    firstStart secondStart algebra
  let localAttempt := fun _ : Unit => Preparation.checkLocal firstInput secondInput first second
    firstStart secondStart algebra inspectLocal fallback
  let enclosingAttempt := fun _ : Unit => Preparation.checkEnclosing firstInput secondInput first second
    firstStart secondStart algebra inspectLocal localAttempt
  let partition := fun receive => withUnionPreparation firstInput secondInput first second firstStart secondStart
    algebra sourceElimination columns winding control
    (join directory "partition") firstStates secondStates receive
  let localAction := fun receive => withLocalPreparation firstInput secondInput first second firstStart secondStart
    algebra inspectLocal fallback partition firstStates secondStates receive
  let enclosingAction := fun receive =>
    withEnclosingPreparation firstInput secondInput first second firstStart secondStart
      algebra inspectLocal localAttempt localAction winding
      (join directory "enclosing-winding") firstStates receive
  withInitialPreparation firstInput secondInput first second firstStart secondStart algebra inspectInitial
    enclosingAttempt enclosingAction (join directory "initial")
    firstStates secondStates fun saved => do
    let result : PreparedComparison firstInput secondInput first second firstStart secondStart :=
      ⟨inspectInitial, inspectLocal, algebra, saved.val, saved.val.outcome, rfl⟩
    have original : result = CommonSource.prepareComparison firstInput secondInput first second
        firstStart secondStart inspectInitial inspectLocal := by
      rcases saved with ⟨saved, same⟩
      cases same
      rfl
    use ⟨result, original⟩

end Comparison

/-- Retain the actual restored original state in a thunk, without changing the original certified name's cache. -/
@[expose] def stateEntry (root : CertifiedName track) (index : Nat) (current : State root index) :
    StateCache.Entry track where
  index := index
  value := Thunk.mk fun _ => current.val
  value_eq := current.property.trans (root.stateAt_eq index)

/-- Restore a finite original prefix in order, retaining and consuming each actual checked predecessor once.

Atomic Newton artifacts and checked reloads are supplied by the original
state-refinement owner. Each returned entry stores the actual restored state;
no numerical program repeats the original root producer on a cache hit.
-/
@[expose] def sampleEntries (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : (remaining index : Nat) → (current : State root index) →
    IO (List (StateCache.Entry track))
  | 0, index, current => pure [stateEntry root index current]
  | remaining + 1, index, current => do
      Purelib.System.IO.println s!"original sample cache: restore state {index + 1}"
      (← IO.getStdout).flush
      let next ← nextState root input elimination canonical columns winding directory index current
      Purelib.System.IO.println s!"original sample cache: retain complete state {index + 1}"
      (← IO.getStdout).flush
      let rest ← sampleEntries root input elimination canonical columns winding directory remaining (index + 1) next
      return stateEntry root index current :: rest

/-- Restore actual original state entries from zero through the computed last required primitive index. -/
@[expose] def samplePrefix (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (last : Nat) : IO (List (StateCache.Entry track)) :=
  sampleEntries root input elimination canonical columns winding directory last 0
    ⟨track.initial, (root.stateAt_eq 0).symm⟩

/-- Restore the exact primitive states demanded by the original named sampling trajectory.

Each requested named index computes its unchanged primitive index first.
The original checked prefix loader retains all predecessor states once, and
the returned named sample table consumes their saved anchors directly.
-/
@[expose] def namedSamples (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (indices : List Nat) :
    IO (Sequence.SamplePrefix (Name.Sampling.approximation root.value.name)) := do
  let last := indices.foldl (fun last index => max last
    (Equivalence.Sampling.emittedSampleIndex root.approximation index)) 0
  let entries ← samplePrefix root input elimination canonical columns winding directory last
  return root.namedSamples entries indices

/-- Find an existing exact original state without invoking a numerical fallback on a miss. -/
@[expose] def findState (root : CertifiedName track) (index : Nat) :
    List (StateCache.Entry track) → Option (State root index)
  | [] => none
  | entry :: remaining =>
      if same : entry.index = index then
        some ⟨entry.value.get, by
          have original : entry.value.get = CoherentRoot.state track index := by
            rewrite [← same]
            exact entry.value_eq
          exact original.trans (root.stateAt_eq index).symm⟩
      else findState root index remaining

/-- Read an exact state through supplied finite-cache actions, restoring only missing successors.

A hit returns the retained entry without invoking the successor or write action.
After a completed successor, a fresh cache read preserves every entry retained
by the recursive predecessor before the complete new state is prepended.
-/
@[expose] def readStateWith {m : Type → Type} [Monad m] (root : CertifiedName track)
    (successor : (index : Nat) → State root index → m (State root (index + 1)))
    (readEntries : m (List (StateCache.Entry track)))
    (writeEntries : List (StateCache.Entry track) → m Unit)
    (index : Nat) : m (State root index) := do
  match findState root index (← readEntries) with
  | some current => return current
  | none =>
      let current ← (show m (State root index) from
        match index with
        | 0 => pure ⟨track.initial, (root.stateAt_eq 0).symm⟩
        | previous + 1 => do
            let earlier ← readStateWith root successor readEntries writeEntries previous
            successor previous earlier)
      let retained ← readEntries
      writeEntries (stateEntry root index current :: retained)
      return current

/-- Read an original prepared-axis state using the supplied retained entry-list accessors.

The original successor consumes the same prepared columns and winding data.
Completed predecessors are written through the supplied accessors before a
later failure, allowing several original roots to share one owner-indexed bank.
-/
def readPreparedState (root : CertifiedName track) (input : Input polynomial)
    (axes : AxisPreparation polynomial)
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
        (axes.certificate input.nonzero input.degreePositive) current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (readEntries : IO (List (StateCache.Entry track)))
    (writeEntries : List (StateCache.Entry track) → IO Unit) (index : Nat) : IO (State root index) :=
  let successor := nextStateUsing root (fun directory current epsilon positive => do
    let saved ← RawSubdivisionCheckpoint.refinePrepared input axes columns winding directory current epsilon positive
    return ⟨saved.val, saved.property.trans (canonical current epsilon positive).symm⟩) directory
  readStateWith root successor readEntries writeEntries index

/-- Retain one original state bank behind the supplied indexed reader and its cache accessors.

The reader receives one shared entry list for its lifetime, seeded by the
supplied completed entries. Completed writes survive later loader errors,
and every subsequent call consumes that same bank. The original root and
the reader's numerical policy remain unchanged.
-/
def stateReader (root : CertifiedName track)
    (read : IO (List (StateCache.Entry track)) → (List (StateCache.Entry track) → IO Unit) →
      (index : Nat) → IO (State root index))
    (initial : List (StateCache.Entry track) := []) : IO ((index : Nat) → IO (State root index)) := do
  let entries ← System.IO.mkRef initial
  let readEntries : IO (List (StateCache.Entry track)) := do pure (← System.IO.Ref.get entries)
  let writeEntries : List (StateCache.Entry track) → IO Unit := fun values => do entries.set values
  return read readEntries writeEntries

/-- Read one original named observation through its exact canonical primitive index.

The supplied state reader runs once at the unchanged emitted index. Its actual
anchor supplies the complete named entry, including the requested index and
original scalar identity. A reader failure stops this operation unchanged.
-/
def namedSampleWithStates {m : Type → Type} [Monad m] (root : CertifiedName track)
    (states : (index : Nat) → m (State root index)) (index : Nat) :
    m {reading : Sequence.SamplePrefix.Entry (Name.Sampling.approximation root.value.name) //
      reading.index = index} := do
  let primitive := Equivalence.Sampling.emittedSampleIndex root.approximation index
  let current ← states primitive
  return root.namedEntry (stateEntry root primitive current) index rfl

/-- Read an original channel's named observation through its identical retained root-view channel.

The genuine whole-channel equality transports the complete existing read
action. It preserves the named index, canonical primitive index, actual
state-bank observation and reader failures without evaluating a second
root or named-sample producer. Operational equivalence alone is insufficient.
-/
def namedSampleWithView {m : Type → Type} [Monad m] {channel : Name.Coherent.CoherentNamed}
    (view : CertifiedName.View channel) (same : channel = view.root.value)
    (states : (index : Nat) → m (State view.root index)) (index : Nat) :
    m {reading : Sequence.SamplePrefix.Entry (Name.Sampling.approximation channel.name) //
      reading.index = index} :=
  Eq.mp (congrArg (fun actual : Name.Coherent.CoherentNamed =>
    m {reading : Sequence.SamplePrefix.Entry (Name.Sampling.approximation actual.name) //
      reading.index = index}) same.symm) (namedSampleWithStates view.root states index)

/-- Retain one original prepared-axis root-state reader and consume its actual completed predecessors.

The supplied pointwise law identifies the original track's own prepared
refiner. One retained entry list survives successive reads and loader errors;
only missing successors invoke the same prepared column and winding readers.
Initial-state and cache hits do not evaluate a refinement producer. -/
def preparedStateReader (root : CertifiedName track) (input : Input polynomial)
    (axes : AxisPreparation polynomial)
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
        (axes.certificate input.nonzero input.degreePositive) current epsilon positive)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : IO ((index : Nat) → IO (State root index)) :=
  stateReader root (readPreparedState root input axes canonical columns winding directory)

/-- Read saved-only original states from the supplied exact retained entry list.

Clearance and winding loaders both use literal saved-only controls. Updated
entries accompany their original structured IO error; the execution allocates
no reference and computes no replacement initial cache.
-/
@[expose] def savedStateReader (root : CertifiedName track) (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    (canonical : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (directory : System.FilePath) (index : Nat) :
    StateExecution (List (StateCache.Entry track)) (State root index) :=
  let columns : ClearanceCheckpoint.Control IO := ⟨true, pure (), false⟩
  let winding : WindingCheckpoint.Control IO := ⟨true, pure (), none⟩
  readStateWith root
    (fun stage current => StateExecution.liftIO
      (nextState root input elimination canonical columns winding directory stage current))
    (getThe (List (StateCache.Entry track)))
    (fun entries => modifyThe (List (StateCache.Entry track)) (fun _ => entries)) index

/-- Read one original root state from its existing cell in the same retained family bank.

The original bounded owner selects its actual root, numerical directory and
complete entry list. The updated cell is retained on both success and failure;
all other owners remain unchanged, and no initial bank is rebuilt on lookup.
-/
@[expose] def savedFamilyReaders (input : Input polynomial)
    (elimination : Thunk (Input.Elimination input))
    {tracks : List (WindingOneTrack polynomial ambient)} (roots : Family tracks)
    (canonical : (owner : Fin tracks.length) → ∀ current epsilon positive,
      (tracks.get owner).refine current epsilon positive =
        Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
          current epsilon positive)
    (directory : Fin tracks.length → System.FilePath) (owner : Fin tracks.length) (index : Nat) :
    StateExecution (FamilyEntries tracks) (State (roots.get owner) index) :=
  fun bank => do
    let (result, entries) ← StateExecution.run
      (savedStateReader (roots.get owner) input elimination (canonical owner) (directory owner) index) (bank.get owner)
    return (result, bank.set owner entries)

/-- Read actual same-policy dyadic states through the retained error-preserving entry bank. -/
@[expose] def dyadicStateReader (root : CertifiedName track) (input : Input polynomial)
    (elimination : Input.Elimination input)
    (policy : ∀ current epsilon positive, track.refine current epsilon positive =
      (Track.Accelerated.dyadicRefinement elimination.certificate
        (Subdivision.WindingOne.ofInitial input elimination.certificate current) current epsilon positive).state)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) (index : Nat) :
    StateExecution (List (StateCache.Entry track)) (State root index) :=
  readStateWith root
    (fun stage current => StateExecution.liftIO
      (nextDyadicState root input elimination policy columns winding requireSavedHeader directory stage current))
    (getThe (List (StateCache.Entry track)))
    (fun entries => modifyThe (List (StateCache.Entry track)) (fun _ => entries)) index

/-- Restore exact dyadic root samples with literal saved-only header, column and winding policies. -/
@[expose] def savedDyadicStateReader (root : CertifiedName track) (input : Input polynomial)
    (elimination : Input.Elimination input)
    (policy : ∀ current epsilon positive, track.refine current epsilon positive =
      (Track.Accelerated.dyadicRefinement elimination.certificate
        (Subdivision.WindingOne.ofInitial input elimination.certificate current) current epsilon positive).state)
    (directory : System.FilePath) (index : Nat) :
    StateExecution (List (StateCache.Entry track)) (State root index) :=
  dyadicStateReader root input elimination policy ⟨true, pure (), false⟩ ⟨true, pure (), none⟩ true directory index

/-- Materialize the actual finite same-index dyadic sample entries consumed by existing sample-prefix transports. -/
@[expose] def dyadicSamplePrefix (root : CertifiedName track) (input : Input polynomial)
    (elimination : Input.Elimination input)
    (policy : ∀ current epsilon positive, track.refine current epsilon positive =
      (Track.Accelerated.dyadicRefinement elimination.certificate
        (Subdivision.WindingOne.ofInitial input elimination.certificate current) current epsilon positive).state)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (requireSavedHeader : Bool) (directory : System.FilePath) (last : Nat) : IO (List (StateCache.Entry track)) := do
  let (result, entries) ← StateExecution.run
    (dyadicStateReader root input elimination policy columns winding requireSavedHeader directory last) []
  match result with
  | .ok _ => return entries
  | .error error => throw error

end CoherentRootCheckpoint
