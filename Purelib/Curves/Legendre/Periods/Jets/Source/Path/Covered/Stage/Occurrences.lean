module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Entries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Preparation.Endpoint.Occurrence
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Occurrence
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Occurrence
import Purelib.Data.List.Append

/-! # Ordered occurrence admissions on the same retained source-stage attempt

Each original starting occurrence reads its own complete cached bank entry.
The next original occurrence supplies the finishing reading, with the final
cell returning to the first entry. The actual closed root chain derives
all owner comparisons, including repeated coordinate and local-sheet keys.
Original point-only checks and both of their stored outcomes remain intact.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {sourceStage : Nat}
    {targets : CellEndpoints.Targets original sourceStage}

/-- A materialized actual admission at each original parent, sharing the supplied consecutive endpoint keys. -/
abbrev OccurrenceEntries {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (bank : Vertex.Bank parameter targets.endpoint) (keys : Fin (parents.length + 1) → Fin bank.length) :=
  DependentProduct parents (fun index => Cell.OccurrenceAdmission (prepared.entry index).preparation.cell
    targets bank (keys index.castSucc) (keys index.succ))

namespace OccurrenceEntries

/-- Fold the same cached admissions along the original physical source spine without another comparison or refinement.

Only the original dependent product and its stored tail are consumed.
Every endpoint key, ordered repeated parent and complete source cell stays
in its original position; an empty spine preserves its one supplied key.
-/
def admissions {bank : Vertex.Bank parameter targets.endpoint} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (keys : Fin (parents.length + 1) → Fin bank.length) →
    OccurrenceEntries covered prepared bank keys →
    OccurrenceAdmissions targets bank (sources covered prepared chain) (keys 0) (keys (Fin.last parents.length))
  | [], .nil, _, _, _, .nil point, keys, _ => .nil point (keys 0)
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain, keys, entries =>
      .cons entries.1 (admissions covered prepared.2 chain (fun index => keys index.succ) entries.2)

end OccurrenceEntries

namespace StageAttempt

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)

/-- The actual bounded bank position of an original source occurrence, retaining its literal natural index. -/
@[expose] def sourceKey (position : Fin (parent :: parents).length) : Fin attempt.2.2.1.val.length :=
  ⟨position.val, Eq.mp (congrArg (fun size => position.val < size) attempt.bank_length.symm) position.isLt⟩

/-- The actual first bank value at one exact original covered-parent occurrence. -/
def sourceAt (position : Fin (parent :: parents).length) :
    Vertex.Bank.FoundAt attempt.2.2.1.val
      (PreparedParent.startPoint ((parent :: parents)[position.val]'position.isLt))
      (attempt.sourceKey position) :=
  Vertex.Bank.atPoint attempt.2.2.1.val (attempt.sourceKey position) _
    (congrArg (fun entry : Vertex.Entry parameter attempt.1.val.endpoint => entry.point)
      (attempt.bank_getElem position (attempt.sourceKey position).isLt))

/-- The positional lookup identifies the same complete original request and source Point, with no new request. -/
theorem sourceFound_name (position : Fin (parent :: parents).length)
    (found : Vertex.Bank.FoundAt attempt.2.2.1.val
      (PreparedParent.startPoint ((parent :: parents)[position.val]'position.isLt))
      (attempt.sourceKey position)) :
    found.original.sample.certificate.value.name =
      (attempt.2.1.entry position).firstSample.certificate.value.name := by
  have entryEq := found.entry_eq.trans
    (attempt.bank_getElem position (attempt.sourceKey position).isLt)
  have retained := congrArg (fun entry : Vertex.Entry parameter attempt.1.val.endpoint =>
    entry.original.sample.certificate.value.name) entryEq
  change found.entry.original.sample.certificate.value.name =
    (attempt.2.1.entry position).firstVertex.val.sample.certificate.value.name at retained
  have vertexName := congrArg
    (fun vertex : Vertex parameter (PreparedParent.startPoint
      ((parent :: parents)[position.val]'position.isLt)) => vertex.sample.certificate.value.name)
    (attempt.2.1.entry position).firstVertex.property
  have sampleName := congrArg
    (fun sample : ContinuedNeighborhood.Point _ _ => sample.certificate.value.name)
    (Vertex.ofPoint_sample (attempt.2.1.entry position).firstSample)
  exact found.original_name.trans (retained.trans (vertexName.trans sampleName))

/-- The complete positional bank selections materialized once at the original source occurrences. -/
abbrev SourceLookups :=
  DependentProduct (parent :: parents) (fun position => Vertex.Bank.FoundAt attempt.2.2.1.val
    (PreparedParent.startPoint ((parent :: parents)[position.val]'position.isLt))
    (attempt.sourceKey position))

/-- Select and retain the actual complete entry at every original occurrence once before any endpoint comparison. -/
def sourceLookups : SourceLookups attempt :=
  DependentProduct.ofFn (parent :: parents) (fun position => attempt.sourceAt position)

/-- Read one same stored positional lookup without another bounded list lookup or source request. -/
def lookupAt (lookups : SourceLookups attempt) (position : Fin (parent :: parents).length) :
    Vertex.Bank.FoundAt attempt.2.2.1.val
      (PreparedParent.startPoint ((parent :: parents)[position.val]'position.isLt))
      (attempt.sourceKey position) :=
  DependentProduct.get (parent :: parents) lookups position

/-- Each stored positional selection is its identical original complete readonly selection factory. -/
private theorem packaged_sourceLookups_get (position : Fin (parent :: parents).length) :
    attempt.lookupAt attempt.sourceLookups position = attempt.sourceAt position := by
  unfold lookupAt sourceLookups
  exact DependentProduct.get_ofFn (parent :: parents) (fun position => attempt.sourceAt position) position

/-- Each stored positional selection is its identical original complete readonly selection factory. -/
theorem sourceLookups_get (position : Fin (parent :: parents).length) :
    attempt.lookupAt attempt.sourceLookups position = attempt.sourceAt position :=
  attempt.packaged_sourceLookups_get position

/-- The closed boundary key list uses each source position once and returns literally to its first bank position. -/
@[expose] def boundaryKey (position : Fin ((parent :: parents).length + 1)) : Fin attempt.2.2.1.val.length :=
  if inside : position.val < (parent :: parents).length then attempt.sourceKey ⟨position.val, inside⟩
  else attempt.sourceKey 0

/-- A source cell starts at its identical original bounded bank position. -/
theorem boundaryKey_start (position : Fin (parent :: parents).length) :
    attempt.boundaryKey position.castSucc = attempt.sourceKey position := by
  change (if inside : position.val < (parent :: parents).length then attempt.sourceKey ⟨position.val, inside⟩
    else attempt.sourceKey 0) = attempt.sourceKey position
  rewrite [dif_pos position.isLt]
  rfl

/-- The terminal boundary shares exactly the original first bank key, without identifying other repeated occurrences. -/
theorem boundaryKey_last :
    attempt.boundaryKey (Fin.last (parent :: parents).length) = attempt.boundaryKey 0 := by
  change (if inside : (parent :: parents).length < (parent :: parents).length then
    attempt.sourceKey ⟨(parent :: parents).length, inside⟩ else attempt.sourceKey 0) = attempt.boundaryKey 0
  rewrite [dif_neg (Nat.lt_irrefl _)]
  exact (attempt.boundaryKey_start 0).symm

/-- The next retained source occurrence, with only the literal last parent returning to position zero. -/
@[expose] def followingIndex (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis))
    (position : Fin (parent :: parents).length) : Fin (parent :: parents).length :=
  if inside : position.val + 1 < (parent :: parents).length then ⟨position.val + 1, inside⟩ else 0

/-- Every nonfinal occurrence is followed by its literal successor index. -/
theorem followingIndex_interior (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) (position : Fin parents.length) :
    followingIndex parent parents position.castSucc = position.succ := by
  unfold followingIndex
  change (if inside : position.val + 1 < parents.length + 1 then ⟨position.val + 1, inside⟩ else 0) = position.succ
  rewrite [dif_pos (Nat.succ_lt_succ position.isLt)]
  rfl

/-- Only the literal final occurrence returns to the original position zero. -/
theorem followingIndex_last (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    followingIndex parent parents (Fin.last parents.length) = 0 := by
  unfold followingIndex
  change (if inside : parents.length + 1 < parents.length + 1 then ⟨parents.length + 1, inside⟩ else 0) =
    (0 : Fin (parents.length + 1))
  rewrite [dif_neg (Nat.lt_irrefl (parents.length + 1))]
  rfl

/-- The finish key is the actual following source's bank position, including the original closing occurrence. -/
theorem boundaryKey_finish (position : Fin (parent :: parents).length) :
    attempt.boundaryKey position.succ = attempt.sourceKey (followingIndex parent parents position) := by
  change (if inside : position.val + 1 < (parent :: parents).length then
    attempt.sourceKey ⟨position.val + 1, inside⟩ else attempt.sourceKey 0) =
    attempt.sourceKey (if inside : position.val + 1 < (parent :: parents).length then
      ⟨position.val + 1, inside⟩ else 0)
  split <;> rfl

/-- The actual centered chain identifies the following source start with this source finish, including closure. -/
theorem following_point (chain : CenteredPathChain (parent :: parents)
    (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (position : Fin (parent :: parents).length) :
    PreparedParent.startPoint ((parent :: parents)[(followingIndex parent parents position).val]'
      (followingIndex parent parents position).isLt) =
    PreparedParent.finishPoint ((parent :: parents)[position.val]'position.isLt) := by
  unfold followingIndex
  split
  next later => exact CenteredPathChain.adjacent_eq (parent :: parents) chain position later
  next last =>
    have terminal : position.val + 1 = (parent :: parents).length :=
      Nat.le_antisymm (Nat.succ_le_of_lt position.isLt) (Nat.le_of_not_gt last)
    exact (CenteredPathChain.startAt_eq (parent :: parents) chain 0 rfl).trans
      (CenteredPathChain.finishAt_eq (parent :: parents) chain position terminal).symm

/-- The retained root chain supplies the actual finish-to-following query comparison at every original position.

At an interior occurrence this reads its original adjacency witness.
At the last occurrence it composes the original terminal return and first
incoming witness. No relation between unrelated repeated keys is assumed.
-/
def followingEquivalent {root : Named} (roots : RootChain (parent :: parents) root root)
    (position : Fin (parent :: parents).length) :
    NamedEquivalent
      (((parent :: parents)[position.val]'position.isLt).edge.rootName 1 (of_decide_eq_true rfl))
      (((parent :: parents)[(followingIndex parent parents position).val]'
        (followingIndex parent parents position).isLt).edge.rootName 0
          ((parent :: parents)[(followingIndex parent parents position).val]'
            (followingIndex parent parents position).isLt).edge.baseInside) := by
  unfold followingIndex
  split
  next later => exact RootChain.adjacentEquivalent (parent :: parents) roots position later
  next last =>
    have terminal : position.val + 1 = (parent :: parents).length :=
      Nat.le_antisymm (Nat.succ_le_of_lt position.isLt) (Nat.le_of_not_gt last)
    exact (RootChain.terminalEquivalent (parent :: parents) roots position terminal).trans roots.firstEquivalent

/-- The actual source entry selected at a cell's starting boundary key. -/
def startingAt (lookups : SourceLookups attempt) (position : Fin (parent :: parents).length) :
    Vertex.Bank.FoundAt attempt.2.2.1.val
      (PreparedParent.startPoint ((parent :: parents)[position.val]'position.isLt))
      (attempt.boundaryKey position.castSucc) :=
  (attempt.lookupAt lookups position).castKey (attempt.boundaryKey_start position).symm

/-- The actual following source entry transported only through the whole original physical endpoint equality. -/
def finishingAt (lookups : SourceLookups attempt) (position : Fin (parent :: parents).length) :
    Vertex.Bank.FoundAt attempt.2.2.1.val
      (PreparedParent.finishPoint ((parent :: parents)[position.val]'position.isLt))
      (attempt.boundaryKey position.succ) :=
  ((attempt.lookupAt lookups (followingIndex parent parents position)).castPoint
    (following_point chain position)).castKey
    (attempt.boundaryKey_finish position).symm

/-- The initial source sample is attached to its same actual cached occurrence by original factory readback only. -/
def startingEquivalent (lookups : SourceLookups attempt) (position : Fin (parent :: parents).length) :
    NamedEquivalent (attempt.2.1.entry position).firstSample.certificate.value.name
      (attempt.startingAt lookups position).original.sample.certificate.value.name :=
  NamedEquivalent.transport rfl
    ((attempt.sourceFound_name position (attempt.lookupAt lookups position)).symm.trans
      ((attempt.lookupAt lookups position).castKey_name (attempt.boundaryKey_start position).symm).symm)
    (NamedEquivalent.refl (attempt.2.1.entry position).firstSample.certificate.value.name)

/-- The original root chain and query-to-source laws attach the finish to the next actual cache. -/
def finishingEquivalent (lookups : SourceLookups attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root)
    (position : Fin (parent :: parents).length) :
    NamedEquivalent (attempt.2.1.entry position).lastSample.certificate.value.name
      (attempt.finishingAt lookups position).original.sample.certificate.value.name :=
  let next := followingIndex parent parents position
  let following := attempt.lookupAt lookups next
  let physical := following_point chain position
  let compared := (attempt.2.1.entry position).lastQueryEquivalent.symm.trans
    ((followingEquivalent roots position).trans (attempt.2.1.entry next).firstQueryEquivalent)
  let names := (attempt.sourceFound_name next (attempt.lookupAt lookups next)).symm.trans
    ((following.castPoint_name physical).symm.trans
      ((following.castPoint physical).castKey_name (attempt.boundaryKey_finish position).symm).symm)
  NamedEquivalent.transport rfl names compared

/-- Compute one original cell's two common refinements and numerical comparisons once at its actual consecutive keys.

The original Point, plan, attachment and source model come from the stored
parent preparation. The final endpoint consumes the actual next entry,
including the literal return key; neither bank nor source work is replayed.
-/
def admitOccurrence (lookups : SourceLookups attempt) {root : Named} (roots : RootChain (parent :: parents) root root)
    (position : Fin (parent :: parents).length) :
    Cell.OccurrenceAdmission (attempt.2.1.entry position).preparation.cell attempt.1.val attempt.2.2.1.val
      (attempt.boundaryKey position.castSucc) (attempt.boundaryKey position.succ) :=
  let prepared := attempt.2.1.entry position
  let first := attempt.startingAt lookups position
  let last := attempt.finishingAt lookups position
  let firstEquivalent := attempt.startingEquivalent lookups position
  let lastEquivalent := attempt.finishingEquivalent lookups roots position
  let firstRefinement := RootBranch.acquire prepared.firstSample first.original.sample firstEquivalent
  let lastRefinement := RootBranch.acquire prepared.lastSample last.original.sample lastEquivalent
  let starting := prepared.preparation.occurrenceEndpoint first prepared.firstPlan.val
    prepared.preparation.attached.firstAttachment firstEquivalent firstRefinement
  let finishing := prepared.preparation.occurrenceEndpoint last prepared.lastPlan.val
    prepared.preparation.attached.lastAttachment lastEquivalent lastRefinement
  Cell.OccurrenceAdmission.build prepared.preparation.cell attempt.1.val attempt.2.2.1.val
    (PreparedParent.cost ((parent :: parents)[position.val]'position.isLt))
    (by rewrite [prepared.displacement_eq]; exact Data.Rat.Fraction.Order.Basic.le_refl _)
    prepared.target_eq starting finishing

/-- Materialize actual admissions in parent order once, retaining their independent original refinements. -/
def occurrenceEntries (lookups : SourceLookups attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    OccurrenceEntries covered attempt.2.1 attempt.2.2.1.val attempt.boundaryKey :=
  DependentProduct.ofFn (parent :: parents) (fun position => attempt.admitOccurrence lookups roots position)

/-- Each stored original admission is exactly its once-only supplied per-occurrence factory value. -/
private theorem packaged_occurrenceEntries_get (lookups : SourceLookups attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root)
    (position : Fin (parent :: parents).length) :
    DependentProduct.get (parent :: parents) (attempt.occurrenceEntries lookups roots) position =
      attempt.admitOccurrence lookups roots position := by
  unfold occurrenceEntries
  exact DependentProduct.get_ofFn (parent :: parents) (fun position => attempt.admitOccurrence lookups roots position)
    position

/-- Each retained admission is the whole original supplied per-occurrence factory value. -/
theorem occurrenceEntries_get (lookups : SourceLookups attempt) {root : Named}
    (roots : RootChain (parent :: parents) root root)
    (position : Fin (parent :: parents).length) :
    DependentProduct.get (parent :: parents) (attempt.occurrenceEntries lookups roots) position =
      attempt.admitOccurrence lookups roots position := attempt.packaged_occurrenceEntries_get lookups roots position

/-- The old first-match base still selects the literal first source entry of this same materialized bank. -/
theorem base_entry :
    attempt.2.2.1.val[(attempt.boundaryKey 0).val]'(attempt.boundaryKey 0).isLt = attempt.2.2.2.1.entry := by
  have first := attempt.bank_getElem 0 (attempt.sourceKey 0).isLt
  have selected : Vertex.Bank.find attempt.2.2.1.val (PreparedParent.startPoint parent) =
      some (Vertex.Entry.request attempt.2.1.1.firstVertex.val
        attempt.1.val.endpoint attempt.1.val.endpoint_positive) := by
    rewrite [attempt.2.2.1.property]
    cases covered with
    | cons patch inside remaining =>
      exact Vertex.Bank.find_cons_eq _ _ _ rfl
  have same := Option.some.inj (selected.symm.trans attempt.2.2.2.1.present)
  have keyEq : attempt.boundaryKey 0 = attempt.sourceKey 0 := attempt.boundaryKey_start 0
  have positionEq := congrArg (fun key : Fin attempt.2.2.1.val.length =>
    attempt.2.2.1.val[key.val]'key.isLt) keyEq
  exact positionEq.trans (first.trans same)

/-- Close the same cached admission product without repeating its entry producer. -/
def closeOccurrences
    (entries : OccurrenceEntries covered attempt.2.1 attempt.2.2.1.val attempt.boundaryKey) :
    OccurrenceAdmissions attempt.1.val attempt.2.2.1.val (sources covered attempt.2.1 chain)
      (attempt.boundaryKey 0) (attempt.boundaryKey 0) :=
  Eq.mp (congrArg (fun key => OccurrenceAdmissions attempt.1.val attempt.2.2.1.val
    (sources covered attempt.2.1 chain) (attempt.boundaryKey 0) key) attempt.boundaryKey_last)
    (OccurrenceEntries.admissions covered attempt.2.1 chain attempt.boundaryKey entries)

/-- Retain the old attempt and computed occurrence admissions before the same original Stage consumes them.

The old point-only check outcomes remain unchanged data. This distinct
completion does not label a new keyed selection as an old Found or claim
that the old Ready decision succeeded.
-/
abbrev OccurrenceCompletion (attempt : StageAttempt covered chain index floor rootStage) :=
  (_lookups : {value : SourceLookups attempt // value = attempt.sourceLookups}) ×
  (entries : OccurrenceEntries covered attempt.2.1 attempt.2.2.1.val attempt.boundaryKey) ×
  {result : Stage parameter ⟨PreparedParent.startPoint parent, chain.path⟩ index //
    result = Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
      attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
      (attempt.closeOccurrences entries) attempt.base_entry}

/-- Complete the retained stage attempt using its actual occurrence keys and genuine closed root-chain witnesses.

Only the new per-endpoint Common refinements and their numerical comparisons
execute. The original preparations, bank, Point/Query observations, base
Found, checks, readiness decision and both old outcomes are retained.
-/
def completeOccurrences {root : Named} (roots : RootChain (parent :: parents) root root) :
    (retained : StageAttempt covered chain index floor rootStage) ×
    {_completed : OccurrenceCompletion retained // retained = attempt} :=
  let lookups := attempt.sourceLookups
  let entries := attempt.occurrenceEntries lookups roots
  let result := Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
    attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
    (attempt.closeOccurrences entries) attempt.base_entry
  ⟨attempt, ⟨⟨⟨lookups, rfl⟩, entries, ⟨result, rfl⟩⟩, rfl⟩⟩

namespace OccurrenceCompletion

variable {attempt} (completed : OccurrenceCompletion attempt)

/-- Read the same once-materialized positional selections, shared by both incident endpoint admissions. -/
def lookups : SourceLookups attempt := completed.1.val

/-- The complete lookup product has its original readonly selection factory. -/
private theorem packaged_lookups_eq : completed.lookups = attempt.sourceLookups := completed.1.property

/-- The complete lookup product has its original readonly selection factory. -/
theorem lookups_eq : completed.lookups = attempt.sourceLookups := completed.packaged_lookups_eq

/-- Read the complete materialized original admission product without another endpoint refinement or comparison. -/
def entries : OccurrenceEntries covered attempt.2.1 attempt.2.2.1.val attempt.boundaryKey := completed.2.1

/-- Read the original Stage already constructed from this same stored admission product. -/
def stage : Stage parameter ⟨PreparedParent.startPoint parent, chain.path⟩ index := completed.2.2.val

/-- The retained Stage consumes exactly its original target, bank, base, sources and complete cached admissions. -/
private theorem packaged_stage_eq :
    completed.stage = Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
      attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
      (attempt.closeOccurrences completed.entries) attempt.base_entry := completed.2.2.property

/-- The retained Stage consumes exactly its original target, bank, base, sources and complete cached admissions. -/
theorem stage_eq :
    completed.stage = Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
      attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
      (attempt.closeOccurrences completed.entries) attempt.base_entry := completed.packaged_stage_eq

/-- The completed Stage retains exactly the original source cells of this same attempt and physical chain. -/
theorem stage_sources : completed.stage.sources = sources covered attempt.2.1 chain :=
  congrArg (fun actual : Stage parameter ⟨PreparedParent.startPoint parent, chain.path⟩ index => actual.sources)
    completed.stage_eq

end OccurrenceCompletion

/-- The occurrence completion has precisely its original ordered once-only entry and Stage factories.

The right side describes the whole new retained value, including the same
old attempt and both of its old decision branches. It does not compare
the new certificate with the differently indexed old point-only completion.
-/
private theorem packaged_completeOccurrences_factory {root : Named}
    (roots : RootChain (parent :: parents) root root) :
    attempt.completeOccurrences roots =
      let lookups := attempt.sourceLookups
      let entries := attempt.occurrenceEntries lookups roots
      let result := Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
        attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
        (attempt.closeOccurrences entries) attempt.base_entry
      ⟨attempt, ⟨⟨⟨lookups, rfl⟩, entries, ⟨result, rfl⟩⟩, rfl⟩⟩ := by
  unfold completeOccurrences
  rfl

/-- The occurrence completion retains the old attempt and its three exact original construction values. -/
theorem completeOccurrences_factory {root : Named} (roots : RootChain (parent :: parents) root root) :
    attempt.completeOccurrences roots =
      let lookups := attempt.sourceLookups
      let entries := attempt.occurrenceEntries lookups roots
      let result := Stage.ofOccurrenceAdmissions attempt.1.val attempt.1.property attempt.2.2.1.val
        attempt.2.2.2.1 (sources covered attempt.2.1 chain) (attempt.boundaryKey 0)
        (attempt.closeOccurrences entries) attempt.base_entry
      ⟨attempt, ⟨⟨⟨lookups, rfl⟩, entries, ⟨result, rfl⟩⟩, rfl⟩⟩ := attempt.packaged_completeOccurrences_factory roots

end StageAttempt

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
