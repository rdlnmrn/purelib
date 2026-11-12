module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Root
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement.Check

/-! # Canonical allocation changes retaining original completion geometry

Two actual preparations of the same covered physical parent can have new
numerical Targets while retaining identical source Points and ordered bank
vertices. Exact original factory readbacks transport the selected completion's
whole unpaid acquisitions; actual ready Commons remain with the new checks.
Only the new cell's original numerical admission is constructed.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Checked.Completion

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Vertex.Bank (RootCheck)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

section OnePreparation

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {prepared : PreparedParent patch count floor covered targets}
variable {bank : Vertex.Bank parameter targets.endpoint} {rootStage : Nat}

/-- Read the actual starting Found already retained by a completed check, without a bank scan. -/
private def firstFound : (checked : Checked prepared bank rootStage) → Completion checked →
    Vertex.Bank.Found bank (startPoint parent)
  | ⟨⟨.found first, _⟩, _, _⟩, _ => first
  | ⟨⟨.absent _, _⟩, _, _⟩, completed => nomatch completed.2.2

/-- Read the actual finishing Found already retained by a completed check, without a bank scan. -/
private def lastFound : (checked : Checked prepared bank rootStage) → Completion checked →
    Vertex.Bank.Found bank (finishPoint parent)
  | ⟨_, ⟨.found last, _⟩, _⟩, _ => last
  | ⟨⟨.absent _, _⟩, ⟨.absent _, _⟩, _⟩, completed => nomatch completed.2.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _⟩, _⟩, completed => nomatch completed.2.2
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent _, _⟩, _⟩, completed => nomatch completed.2.2

/-- An unpaid completed starting check retains its original complete acquisition and comparison index. -/
private def firstUnpaid : (checked : Checked prepared bank rootStage) → (completed : Completion checked) →
    (¬ RootCheck.Ready (sample := prepared.firstSample) (bank := bank) (stage := rootStage) checked.first) →
    RootBranch.Refinement prepared.firstSample (firstFound checked completed).original.sample
      (prepared.firstQueryEquivalent.symm.trans (completed.1 (firstFound checked completed)))
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩, completed, _ => completed.2.2.1
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed, _ => completed.2.2.1
  | ⟨⟨.found _, .ready _ _, _⟩, _, _⟩, _, unpaid => False.elim (unpaid True.intro)
  | ⟨⟨.absent _, _⟩, _, _⟩, completed, _ => nomatch completed.2.2
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent _, _⟩, _⟩, completed, _ => nomatch completed.2.2

/-- An unpaid completed finishing check retains its original complete acquisition and comparison index. -/
private def lastUnpaid : (checked : Checked prepared bank rootStage) → (completed : Completion checked) →
    (¬ RootCheck.Ready (sample := prepared.lastSample) (bank := bank) (stage := rootStage) checked.last) →
    RootBranch.Refinement prepared.lastSample (lastFound checked completed).original.sample
      (prepared.lastQueryEquivalent.symm.trans (completed.2.1 (lastFound checked completed)))
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed, _ => completed.2.2.1
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed, _ => completed.2.2.2.1
  | ⟨_, ⟨.found _, .ready _ _, _⟩, _⟩, _, unpaid => False.elim (unpaid True.intro)
  | ⟨⟨.absent _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed, _ => nomatch completed.2.2
  | ⟨⟨.absent _, _⟩, ⟨.absent _, _⟩, _⟩, completed, _ => nomatch completed.2.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _⟩, _⟩, completed, _ => nomatch completed.2.2
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent _, _⟩, _⟩, completed, _ => nomatch completed.2.2

/-- Equal whole preparation caches have the identical retained starting query comparison. -/
private theorem firstQuery_heq (first last : PreparedParent patch count floor covered targets)
    (equal : first = last) : HEq first.firstQueryEquivalent last.firstQueryEquivalent := by
  cases equal
  rfl

/-- Equal whole preparation caches have the identical retained finishing query comparison. -/
private theorem lastQuery_heq (first last : PreparedParent patch count floor covered targets)
    (equal : first = last) : HEq first.lastQueryEquivalent last.lastQueryEquivalent := by
  cases equal
  rfl

end OnePreparation

/-- Equal ordered original vertices prevent a new absent endpoint whenever its old actual Found exists. -/
private theorem notAbsent {parameter : Canonical} {allocation replacement : Rational}
    (firstBank : Vertex.Bank parameter allocation) (lastBank : Vertex.Bank parameter replacement)
    (origins : firstBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)) =
      lastBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
    (point : LiftedPoint 2) (found : Vertex.Bank.Found firstBank point) : lastBank.find point ≠ none := by
  intro missing
  have firstReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter allocation =>
      (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point))) found.present
  have lastReadback := congrArg (Option.map (fun entry : Vertex.Entry parameter replacement =>
      (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point))) missing
  have impossible := firstReadback.symm.trans
    ((Vertex.Bank.find_origins_eq firstBank lastBank origins point).trans lastReadback)
  cases impossible

/-- Exact query and vertex transports retain the entire comparison used to acquire an unpaid refinement. -/
private theorem composed_heq {parameter : Canonical} {point : LiftedPoint 2} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (query : Named)
    (firstSource lastSource : ContinuedNeighborhood.Point patch point.coordinate)
    (firstVertex lastVertex : Vertex parameter point)
    (firstQuery : NamedEquivalent query firstSource.certificate.value.name)
    (lastQuery : NamedEquivalent query lastSource.certificate.value.name)
    (equivalent : NamedEquivalent query firstVertex.sample.certificate.value.name)
    (sources : firstSource = lastSource) (vertices : firstVertex = lastVertex)
    (queries : HEq firstQuery lastQuery) :
    HEq (firstQuery.symm.trans equivalent)
      (lastQuery.symm.trans (equivalent.transport rfl
        (congrArg (fun vertex : Vertex parameter point => vertex.sample.certificate.value.name) vertices))) := by
  cases sources
  cases vertices
  have exactQueries : firstQuery = lastQuery := eq_of_heq queries
  cases exactQueries
  rfl

/-- A retained found check has its original Outcome's readiness, independently of its actual Position cache. -/
private theorem foundReady {parameter : Canonical} {point : LiftedPoint 2} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {allocation : Rational} {stage : Nat}
    (sample : ContinuedNeighborhood.Point patch point.coordinate) (bank : Vertex.Bank parameter allocation)
    (checked : RootCheck (point := point) sample bank stage) (found : Vertex.Bank.Found bank point)
    (outcome : RootOwnerCommonRefinement.Outcome sample.owner found.original.sample.owner stage)
    (same : checked.eraseOccurrence = ⟨.found found, outcome⟩) :
    RootCheck.Ready (sample := sample) (bank := bank) (stage := stage) checked = outcome.Ready := by
  cases checked with
  | mk lookup cached =>
    cases cached with
    | mk result _position =>
      change (⟨lookup, result⟩ :
        (original : Vertex.Bank.Outcome bank point) ×
          match original with
          | .found retained => RootOwnerCommonRefinement.Outcome sample.owner retained.original.sample.owner stage
          | .absent _ => PUnit) = ⟨.found found, outcome⟩ at same
      cases lookup with
      | absent _ => cases same
      | found _ =>
        cases result with
        | ready _ _ =>
          cases same
          rfl
        | inconclusive _ _ _ _ =>
          cases same
          rfl

/-- Whole original Outcome identity preserves readiness after exact source and selected-vertex transports. -/
private theorem outcomeReady_eq {parameter : Canonical} {point : LiftedPoint 2} {count stage : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (firstSource lastSource : ContinuedNeighborhood.Point patch point.coordinate)
    (firstVertex lastVertex : Vertex parameter point)
    (firstOutcome : RootOwnerCommonRefinement.Outcome firstSource.owner firstVertex.sample.owner stage)
    (lastOutcome : RootOwnerCommonRefinement.Outcome lastSource.owner lastVertex.sample.owner stage)
    (sources : firstSource = lastSource) (vertices : firstVertex = lastVertex)
    (outcomes : HEq firstOutcome lastOutcome) : firstOutcome.Ready = lastOutcome.Ready := by
  cases sources
  cases vertices
  exact congrArg RootOwnerCommonRefinement.Outcome.Ready (eq_of_heq outcomes)

/-- Both actual finite checking caches have the same status without changing their stopping stage or candidates. -/
private theorem checkReady_eq {parameter : Canonical} {point : LiftedPoint 2} {count stage : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {allocation replacement : Rational}
    (firstBank : Vertex.Bank parameter allocation) (lastBank : Vertex.Bank parameter replacement)
    (firstSample lastSample : ContinuedNeighborhood.Point patch point.coordinate)
    (firstCheck : RootCheck (point := point) firstSample firstBank stage)
    (lastCheck : RootCheck (point := point) lastSample lastBank stage)
    (firstFactory : firstCheck = firstBank.checkRoot (point := point) firstSample stage)
    (lastFactory : lastCheck = lastBank.checkRoot (point := point) lastSample stage)
    (firstSelected : Vertex.Bank.Found firstBank point) (lastSelected : Vertex.Bank.Found lastBank point)
    (samples : firstSample = lastSample) (vertices : firstSelected.original = lastSelected.original) :
    RootCheck.Ready (sample := firstSample) (bank := firstBank) (stage := stage) firstCheck =
      RootCheck.Ready (sample := lastSample) (bank := lastBank) (stage := stage) lastCheck := by
  have firstWhole := (congrArg
    (fun checked : RootCheck (point := point) firstSample firstBank stage => checked.eraseOccurrence)
    firstFactory).trans
    (Vertex.Bank.checkRoot_found firstBank firstSample stage firstSelected)
  have lastWhole := (congrArg
    (fun checked : RootCheck (point := point) lastSample lastBank stage => checked.eraseOccurrence)
    lastFactory).trans
    (Vertex.Bank.checkRoot_found lastBank lastSample stage lastSelected)
  have second_heq {readingAllocation : Rational} (bank : Vertex.Bank parameter readingAllocation)
      (sample : ContinuedNeighborhood.Point patch point.coordinate)
      (first last : (lookup : Vertex.Bank.Outcome bank point) ×
        match lookup with
        | .found retained => RootOwnerCommonRefinement.Outcome sample.owner retained.original.sample.owner stage
        | .absent _ => PUnit) (equal : first = last) : HEq first.2 last.2 := by
    cases equal
    rfl
  have outcomes := RootCheck.outcome_heq firstBank lastBank firstSample lastSample stage
    firstCheck lastCheck firstFactory lastFactory firstSelected lastSelected samples vertices
  have normalized :=
    (second_heq firstBank firstSample firstCheck.eraseOccurrence _ firstWhole).symm.trans
      (outcomes.trans (second_heq lastBank lastSample lastCheck.eraseOccurrence _ lastWhole))
  have middle := outcomeReady_eq firstSample lastSample firstSelected.original lastSelected.original
    (RootOwnerCommonRefinement.checkAt firstSample.owner firstSelected.original.sample.owner stage)
    (RootOwnerCommonRefinement.checkAt lastSample.owner lastSelected.original.sample.owner stage)
    samples vertices normalized
  have left := foundReady firstSample firstBank firstCheck firstSelected
    (RootOwnerCommonRefinement.checkAt firstSample.owner firstSelected.original.sample.owner stage) firstWhole
  have right := foundReady lastSample lastBank lastCheck lastSelected
    (RootOwnerCommonRefinement.checkAt lastSample.owner lastSelected.original.sample.owner stage) lastWhole
  exact left.trans (middle.trans right.symm)

section TwoPreparations

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
variable {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
variable {firstIndex lastIndex firstFloor lastFloor rootStage : Nat}
variable {firstTargets : CellEndpoints.Targets firstPath firstIndex}
variable {lastTargets : CellEndpoints.Targets lastPath lastIndex}
variable (firstPrepared : PreparedParent patch count firstFloor covered firstTargets)
variable (lastPrepared : PreparedParent patch count lastFloor covered lastTargets)
variable (firstBank : Vertex.Bank parameter firstTargets.endpoint)
variable (lastBank : Vertex.Bank parameter lastTargets.endpoint)
variable (origins : firstBank.map (fun entry =>
    (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)) =
  lastBank.map (fun entry =>
    (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
variable (firstChecked : Checked firstPrepared firstBank rootStage)
variable (completed : Completion firstChecked)

/-- Transport the original first endpoint query through the actual retained old Found and exact selected vertex. -/
private def firstQueryAt
    (retained : NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      (firstFound firstChecked completed).original.sample.certificate.value.name)
    (found : Vertex.Bank.Found lastBank (startPoint parent)) :
    NamedEquivalent (parent.edge.rootName 0 (by decide +kernel)) found.original.sample.certificate.value.name :=
  retained.transport rfl
    (congrArg (fun vertex : Vertex parameter (startPoint parent) => vertex.sample.certificate.value.name)
      (Vertex.Bank.Found.original_eq_of_origins firstBank lastBank origins (startPoint parent)
        (firstFound firstChecked completed) found))

/-- Transport the original last endpoint query through the actual retained old Found and exact selected vertex. -/
private def lastQueryAt
    (retained : NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      (lastFound firstChecked completed).original.sample.certificate.value.name)
    (found : Vertex.Bank.Found lastBank (finishPoint parent)) :
    NamedEquivalent (parent.edge.rootName 1 (by decide +kernel)) found.original.sample.certificate.value.name :=
  retained.transport rfl
    (congrArg (fun vertex : Vertex parameter (finishPoint parent) => vertex.sample.certificate.value.name)
      (Vertex.Bank.Found.original_eq_of_origins firstBank lastBank origins (finishPoint parent)
        (lastFound firstChecked completed) found))

/-- Reuse the complete old first acquisition at an actually unpaid new endpoint with its same original owners. -/
private def firstCache
    (oldQuery : NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      (firstFound firstChecked completed).original.sample.certificate.value.name)
    (oldQueryFactory : oldQuery = completed.1 (firstFound firstChecked completed))
    (samples : firstPrepared.firstSample = lastPrepared.firstSample)
    (queries : HEq firstPrepared.firstQueryEquivalent lastPrepared.firstQueryEquivalent)
    (firstFactory : firstChecked.first = firstBank.checkRoot (point := startPoint parent)
      firstPrepared.firstSample rootStage)
    (found : Vertex.Bank.Found lastBank (startPoint parent))
    (newCheck : RootCheck (point := startPoint parent) lastPrepared.firstSample lastBank rootStage)
    (newFactory : newCheck = lastBank.checkRoot (point := startPoint parent) lastPrepared.firstSample rootStage)
    (unpaid : ¬ RootCheck.Ready (sample := lastPrepared.firstSample)
      (bank := lastBank) (stage := rootStage) newCheck) :
    RootBranch.Refinement lastPrepared.firstSample found.original.sample
      (lastPrepared.firstQueryEquivalent.symm.trans
        (firstQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed
          oldQuery found)) :=
  let oldFound := firstFound firstChecked completed
  have vertices : oldFound.original = found.original :=
    Vertex.Bank.Found.original_eq_of_origins firstBank lastBank origins (startPoint parent) oldFound found
  have statuses := checkReady_eq firstBank lastBank firstPrepared.firstSample lastPrepared.firstSample
    firstChecked.first newCheck firstFactory newFactory oldFound found samples vertices
  have oldUnpaid : ¬ RootCheck.Ready (sample := firstPrepared.firstSample)
      (bank := firstBank) (stage := rootStage) firstChecked.first := fun paid => unpaid (Eq.mp statuses paid)
  have comparisonEq := congrArg
    (fun equivalent : NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      oldFound.original.sample.certificate.value.name =>
      firstPrepared.firstQueryEquivalent.symm.trans equivalent) oldQueryFactory.symm
  let retained := Eq.mp
    (congrArg (fun equivalent : NamedEquivalent firstPrepared.firstSample.certificate.value.name
        oldFound.original.sample.certificate.value.name =>
      RootBranch.Refinement firstPrepared.firstSample oldFound.original.sample equivalent) comparisonEq)
    (firstUnpaid firstChecked completed oldUnpaid)
  RootBranch.Refinement.castVertex oldFound.original found.original
    firstPrepared.firstSample lastPrepared.firstSample
    (firstPrepared.firstQueryEquivalent.symm.trans oldQuery)
    (lastPrepared.firstQueryEquivalent.symm.trans
      (firstQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed oldQuery found))
    samples vertices
    (composed_heq (parent.edge.rootName 0 (by decide +kernel))
      firstPrepared.firstSample lastPrepared.firstSample oldFound.original found.original
      firstPrepared.firstQueryEquivalent lastPrepared.firstQueryEquivalent oldQuery
      samples vertices queries) retained

/-- Reuse the complete old last acquisition at an actually unpaid new endpoint with its same original owners. -/
private def lastCache
    (oldQuery : NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      (lastFound firstChecked completed).original.sample.certificate.value.name)
    (oldQueryFactory : oldQuery = completed.2.1 (lastFound firstChecked completed))
    (samples : firstPrepared.lastSample = lastPrepared.lastSample)
    (queries : HEq firstPrepared.lastQueryEquivalent lastPrepared.lastQueryEquivalent)
    (firstFactory : firstChecked.last = firstBank.checkRoot (point := finishPoint parent)
      firstPrepared.lastSample rootStage)
    (found : Vertex.Bank.Found lastBank (finishPoint parent))
    (newCheck : RootCheck (point := finishPoint parent) lastPrepared.lastSample lastBank rootStage)
    (newFactory : newCheck = lastBank.checkRoot (point := finishPoint parent) lastPrepared.lastSample rootStage)
    (unpaid : ¬ RootCheck.Ready (sample := lastPrepared.lastSample)
      (bank := lastBank) (stage := rootStage) newCheck) :
    RootBranch.Refinement lastPrepared.lastSample found.original.sample
      (lastPrepared.lastQueryEquivalent.symm.trans
        (lastQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed
          oldQuery found)) :=
  let oldFound := lastFound firstChecked completed
  have vertices : oldFound.original = found.original :=
    Vertex.Bank.Found.original_eq_of_origins firstBank lastBank origins (finishPoint parent) oldFound found
  have statuses := checkReady_eq firstBank lastBank firstPrepared.lastSample lastPrepared.lastSample
    firstChecked.last newCheck firstFactory newFactory oldFound found samples vertices
  have oldUnpaid : ¬ RootCheck.Ready (sample := firstPrepared.lastSample)
      (bank := firstBank) (stage := rootStage) firstChecked.last := fun paid => unpaid (Eq.mp statuses paid)
  have comparisonEq := congrArg
    (fun equivalent : NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      oldFound.original.sample.certificate.value.name =>
      firstPrepared.lastQueryEquivalent.symm.trans equivalent) oldQueryFactory.symm
  let retained := Eq.mp
    (congrArg (fun equivalent : NamedEquivalent firstPrepared.lastSample.certificate.value.name
        oldFound.original.sample.certificate.value.name =>
      RootBranch.Refinement firstPrepared.lastSample oldFound.original.sample equivalent) comparisonEq)
    (lastUnpaid firstChecked completed oldUnpaid)
  RootBranch.Refinement.castVertex oldFound.original found.original
    firstPrepared.lastSample lastPrepared.lastSample
    (firstPrepared.lastQueryEquivalent.symm.trans oldQuery)
    (lastPrepared.lastQueryEquivalent.symm.trans
      (lastQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed oldQuery found))
    samples vertices
    (composed_heq (parent.edge.rootName 1 (by decide +kernel))
      firstPrepared.lastSample lastPrepared.lastSample oldFound.original found.original
      firstPrepared.lastQueryEquivalent lastPrepared.lastQueryEquivalent oldQuery
      samples vertices queries) retained

/-- Assemble all four actual new checking outcomes from the same original completion and exact cache identities. -/
private def ofIdentities
    (firstSamples : firstPrepared.firstSample = lastPrepared.firstSample)
    (lastSamples : firstPrepared.lastSample = lastPrepared.lastSample)
    (firstQueries : HEq firstPrepared.firstQueryEquivalent lastPrepared.firstQueryEquivalent)
    (lastQueries : HEq firstPrepared.lastQueryEquivalent lastPrepared.lastQueryEquivalent)
    (firstFactory : firstChecked = check firstPrepared firstBank rootStage)
    (lastChecked : Checked lastPrepared lastBank rootStage)
    (lastFactory : lastChecked = check lastPrepared lastBank rootStage) : Completion lastChecked :=
  let oldFirst := firstFound firstChecked completed
  let oldLast := lastFound firstChecked completed
  let retainedFirstQuery := completed.1 oldFirst
  let retainedLastQuery := completed.2.1 oldLast
  let firstQuery := firstQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed
    retainedFirstQuery
  let lastQuery := lastQueryAt (firstPrepared := firstPrepared) firstBank lastBank origins firstChecked completed
    retainedLastQuery
  have oldFirstFactory := (congrArg
    (fun checked : Checked firstPrepared firstBank rootStage => checked.first) firstFactory).trans
      (check_first firstPrepared firstBank rootStage)
  have oldLastFactory := (congrArg
    (fun checked : Checked firstPrepared firstBank rootStage => checked.last) firstFactory).trans
      (check_last firstPrepared firstBank rootStage)
  have newFirstFactory := (congrArg
    (fun checked : Checked lastPrepared lastBank rootStage => checked.first) lastFactory).trans
      (check_first lastPrepared lastBank rootStage)
  have newLastFactory := (congrArg
    (fun checked : Checked lastPrepared lastBank rootStage => checked.last) lastFactory).trans
      (check_last lastPrepared lastBank rootStage)
  ⟨firstQuery, lastQuery,
    match lastChecked, newFirstFactory, newLastFactory with
    | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩, _, _ => PUnit.unit
    | ⟨⟨.found first, .ready firstCommon _, _⟩,
        ⟨.found last, .inconclusive candidate candidateEq strict unpaid, lastPosition⟩, _⟩, _, finishing =>
        let retained := lastCache firstPrepared lastPrepared firstBank lastBank origins firstChecked completed
          retainedLastQuery rfl lastSamples lastQueries oldLastFactory last
          ⟨.found last, .inconclusive candidate candidateEq strict unpaid, lastPosition⟩
          finishing (fun impossible => impossible)
        let admission := lastPrepared.admitBranches first last
          (RootBranch.ofCommonRefinement firstCommon) retained.2.val
        ⟨retained, ⟨admission, rfl⟩⟩
    | ⟨⟨.found first, .inconclusive candidate candidateEq strict unpaid, firstPosition⟩,
        ⟨.found last, .ready lastCommon _, _⟩, _⟩, starting, _ =>
        let retained := firstCache firstPrepared lastPrepared firstBank lastBank origins firstChecked completed
          retainedFirstQuery rfl firstSamples firstQueries oldFirstFactory first
          ⟨.found first, .inconclusive candidate candidateEq strict unpaid, firstPosition⟩
          starting (fun impossible => impossible)
        let admission := lastPrepared.admitBranches first last retained.2.val
          (RootBranch.ofCommonRefinement lastCommon)
        ⟨retained, ⟨admission, rfl⟩⟩
    | ⟨⟨.found first, .inconclusive firstCandidate firstEq firstStrict firstUnpaid, firstPosition⟩,
        ⟨.found last, .inconclusive lastCandidate lastEq lastStrict lastUnpaid,
          lastPosition⟩, _⟩, starting, finishing =>
        let firstRetained := firstCache firstPrepared lastPrepared firstBank lastBank origins firstChecked completed
          retainedFirstQuery rfl firstSamples firstQueries oldFirstFactory first
          ⟨.found first, .inconclusive firstCandidate firstEq firstStrict firstUnpaid, firstPosition⟩ starting
          (fun impossible => impossible)
        let lastRetained := lastCache firstPrepared lastPrepared firstBank lastBank origins firstChecked completed
          retainedLastQuery rfl lastSamples lastQueries oldLastFactory last
          ⟨.found last, .inconclusive lastCandidate lastEq lastStrict lastUnpaid, lastPosition⟩ finishing
          (fun impossible => impossible)
        Admitted.ofRefinements lastPrepared first last
          (lastPrepared.firstQueryEquivalent.symm.trans (firstQuery first))
          (lastPrepared.lastQueryEquivalent.symm.trans (lastQuery last)) firstRetained lastRetained
    | ⟨⟨.absent missing, _⟩, _, _⟩, _, _ =>
        False.elim (notAbsent firstBank lastBank origins (startPoint parent)
          (firstFound firstChecked completed) missing)
    | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent missing, _⟩, _⟩, _, _ =>
        False.elim (notAbsent firstBank lastBank origins (finishPoint parent)
          (lastFound firstChecked completed) missing)
    | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent missing, _⟩, _⟩, _, _ =>
        False.elim (notAbsent firstBank lastBank origins (finishPoint parent)
          (lastFound firstChecked completed) missing)⟩

end TwoPreparations

/-- Transport an actual selected completion across canonical allocations of the same original covered physical parent.

Both actual PreparedParent and Checked caches remain inputs with their
whole original factory equations. Ordered original bank vertices, including
repeated signed occurrences, determine the same first matches. The same
rootStage preserves both actual checking Outcomes. Unpaid old acquisitions
are consumed unchanged, ready new Commons remain authoritative, and only
new numerical admissions are constructed from the new cells and readings.
The original selected Completion is a genuine required geometric payment.
-/
public def ofCanonical
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent) (count : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex : Nat} (firstFloor lastFloor rootStage : Nat)
    (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex)
    (firstPrepared : PreparedParent patch count firstFloor covered firstTargets)
    (lastPrepared : PreparedParent patch count lastFloor covered lastTargets)
    (firstPreparedFactory : firstPrepared = prepareParent (frame := frame) (basis := basis)
      patch count firstFloor covered firstTargets)
    (lastPreparedFactory : lastPrepared = prepareParent (frame := frame) (basis := basis)
      patch count lastFloor covered lastTargets)
    (firstBank : Vertex.Bank parameter firstTargets.endpoint)
    (lastBank : Vertex.Bank parameter lastTargets.endpoint)
    (origins : firstBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)) =
      lastBank.map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ point : LiftedPoint 2, Vertex parameter point)))
    (firstChecked : Checked firstPrepared firstBank rootStage)
    (lastChecked : Checked lastPrepared lastBank rootStage)
    (firstFactory : firstChecked = check firstPrepared firstBank rootStage)
    (lastFactory : lastChecked = check lastPrepared lastBank rootStage)
    (completed : Completion firstChecked) : Completion lastChecked := by
  have firstSamples : firstPrepared.firstSample = lastPrepared.firstSample :=
    (congrArg (fun prepared : PreparedParent patch count firstFloor covered firstTargets => prepared.firstSample)
      firstPreparedFactory).trans
      ((prepareParent_firstSample (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).trans
        ((prepareParent_firstSample (frame := frame) (basis := basis)
          patch count lastFloor covered lastTargets).symm.trans
          (congrArg (fun prepared : PreparedParent patch count lastFloor covered lastTargets => prepared.firstSample)
            lastPreparedFactory).symm))
  have lastSamples : firstPrepared.lastSample = lastPrepared.lastSample :=
    (congrArg (fun prepared : PreparedParent patch count firstFloor covered firstTargets => prepared.lastSample)
      firstPreparedFactory).trans
      ((prepareParent_lastSample (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).trans
        ((prepareParent_lastSample (frame := frame) (basis := basis)
          patch count lastFloor covered lastTargets).symm.trans
          (congrArg (fun prepared : PreparedParent patch count lastFloor covered lastTargets => prepared.lastSample)
            lastPreparedFactory).symm))
  have firstOld := firstQuery_heq firstPrepared
    (prepareParent (frame := frame) (basis := basis) patch count firstFloor covered firstTargets)
    firstPreparedFactory
  have firstNew := firstQuery_heq lastPrepared
    (prepareParent (frame := frame) (basis := basis) patch count lastFloor covered lastTargets)
    lastPreparedFactory
  have lastOld := lastQuery_heq firstPrepared
    (prepareParent (frame := frame) (basis := basis) patch count firstFloor covered firstTargets)
    firstPreparedFactory
  have lastNew := lastQuery_heq lastPrepared
    (prepareParent (frame := frame) (basis := basis) patch count lastFloor covered lastTargets)
    lastPreparedFactory
  have firstQueries := firstOld.trans
    ((firstQueryEquivalent_prepareParent_heq (frame := frame) (basis := basis)
      patch count firstFloor lastFloor covered firstTargets lastTargets).trans firstNew.symm)
  have lastQueries := lastOld.trans
    ((lastQueryEquivalent_prepareParent_heq (frame := frame) (basis := basis)
      patch count firstFloor lastFloor covered firstTargets lastTargets).trans lastNew.symm)
  exact ofIdentities firstPrepared lastPrepared firstBank lastBank origins firstChecked completed
    firstSamples lastSamples firstQueries lastQueries firstFactory lastChecked lastFactory

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Checked.Completion
