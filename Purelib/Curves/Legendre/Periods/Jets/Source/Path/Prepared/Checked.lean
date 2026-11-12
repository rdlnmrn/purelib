module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Root

/-! # Checked original-cell admissions retaining both endpoint attempts

Both actual endpoint lookup/refinement attempts are materialized before a
result is assembled. Two successful original common refinements construct
the existing admission internally. Otherwise every absent lookup or unpaid
owner inclusion remains in its original retained checking result.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- The actual original admission factory when both retained endpoint checks passed, and no admission otherwise. -/
@[expose] def CheckedResult (prepared : PreparedParent patch count floor covered targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) :
    Vertex.Bank.RootCheck prepared.firstSample bank rootStage →
    Vertex.Bank.RootCheck prepared.lastSample bank rootStage → Type 1
  | ⟨.found first, .ready firstCommon _, _⟩, ⟨.found last, .ready lastCommon _, _⟩ =>
      { admission : Cell.Admission prepared.preparation.cell targets bank //
        admission = prepared.admitBranches first last (RootBranch.ofCommonRefinement firstCommon)
          (RootBranch.ofCommonRefinement lastCommon) }
  | _, _ => PUnit

/-- Both complete endpoint attempts and the original internally derived admission exactly when they succeeded.

All lookup outcomes and actual refinement candidates remain stored even
when one is unpaid. A successful result preserves the complete admission
factory on those same two original common owners and the unchanged cell.
-/
abbrev Checked (prepared : PreparedParent patch count floor covered targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) :=
  (first : Vertex.Bank.RootCheck prepared.firstSample bank rootStage) ×
  (last : Vertex.Bank.RootCheck prepared.lastSample bank rootStage) × CheckedResult prepared bank rootStage first last

namespace Checked

variable {prepared : PreparedParent patch count floor covered targets}
variable {bank : Vertex.Bank parameter targets.endpoint} {rootStage : Nat}

/-- Read the entire source-endpoint lookup and same-owner refinement attempt without another bank scan. -/
@[expose] def first (checked : Checked prepared bank rootStage) :
    Vertex.Bank.RootCheck prepared.firstSample bank rootStage := checked.1

/-- Read the independent whole finishing-endpoint attempt, including any actual unpaid containment. -/
@[expose] def last (checked : Checked prepared bank rootStage) :
    Vertex.Bank.RootCheck prepared.lastSample bank rootStage := checked.2.1

/-- The cell admission is available exactly when both actual retained endpoint attempts are ready. -/
@[expose] def Ready (checked : Checked prepared bank rootStage) : Prop :=
  Vertex.Bank.RootCheck.Ready (sample := prepared.firstSample) (bank := bank) (stage := rootStage) checked.first ∧
    Vertex.Bank.RootCheck.Ready (sample := prepared.lastSample) (bank := bank) (stage := rootStage) checked.last

/-- Decide the two-endpoint readiness from the same stored checking outcomes. -/
@[expose] def decideReady (checked : Checked prepared bank rootStage) : Decidable checked.Ready :=
  match checked.first.decideReady with
  | isFalse unpaid => isFalse (fun ready => unpaid ready.1)
  | isTrue firstReady =>
      match checked.last.decideReady with
      | isFalse unpaid => isFalse (fun ready => unpaid ready.2)
      | isTrue lastReady => isTrue ⟨firstReady, lastReady⟩

/-- Read the actual previously constructed admission when its two original retained checks are ready. -/
def admission : (checked : Checked prepared bank rootStage) → checked.Ready →
    Cell.Admission prepared.preparation.cell targets bank
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, result⟩, _ => result.val
  | ⟨⟨.absent _, _, _⟩, _, _⟩, ready => False.elim ready.1
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, _, _⟩, ready => False.elim ready.1
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩, _⟩, ready => False.elim ready.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, ready => False.elim ready.2

end Checked

/-- Check both actual bank endpoints once and construct their original cell admission only after both checks pass.

Every root request is a positive-index refinement of the actual selected
bank owner's retained track. Successful checks supply genuine common-owner
branches; the existing admission builder derives all numerical endpoint
and local primitive bounds without desired-inequality inputs.
-/
def check (prepared : PreparedParent patch count floor covered targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) : Checked prepared bank rootStage :=
  let first := bank.checkRoot prepared.firstSample rootStage
  let last := bank.checkRoot prepared.lastSample rootStage
  let result : CheckedResult prepared bank rootStage first last :=
    match first, last with
    | ⟨.found first, .ready firstCommon _, _⟩, ⟨.found last, .ready lastCommon _, _⟩ =>
        ⟨prepared.admitBranches first last (RootBranch.ofCommonRefinement firstCommon)
          (RootBranch.ofCommonRefinement lastCommon), rfl⟩
    | ⟨.absent _, _, _⟩, _ => PUnit.unit
    | ⟨.found _, .inconclusive _ _ _ _, _⟩, _ => PUnit.unit
    | ⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩ => PUnit.unit
    | ⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩ => PUnit.unit
  ⟨first, last, result⟩

/-- The original cell check retains the whole actual starting lookup/refinement factory. -/
theorem check_first (prepared : PreparedParent patch count floor covered targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) :
    (check prepared bank rootStage).first =
      bank.checkRoot (point := startPoint parent) prepared.firstSample rootStage := by
  unfold check Checked.first
  rfl

/-- The original cell check retains the whole actual finishing lookup/refinement factory. -/
theorem check_last (prepared : PreparedParent patch count floor covered targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) :
    (check prepared bank rootStage).last =
      bank.checkRoot (point := finishPoint parent) prepared.lastSample rootStage := by
  unfold check Checked.last
  rfl

namespace Checked

variable {prepared : PreparedParent patch count floor covered targets}
variable {bank : Vertex.Bank parameter targets.endpoint} {rootStage : Nat}

/-- Additional paid data for exactly the endpoints left unpaid by the original two retained checking outcomes.

A ready endpoint reuses its original CommonRefinement and actual index.
Only an inconclusive endpoint acquires and stores a genuinely additional
complete refinement factory. When both old checks passed, no new acquisition
or admission is produced; the original cached admission is consumed.
-/
@[expose] def CompletionResult
    (firstQuery : (found : Vertex.Bank.Found bank (startPoint parent)) →
      NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
        found.original.sample.certificate.value.name)
    (lastQuery : (found : Vertex.Bank.Found bank (finishPoint parent)) →
      NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
        found.original.sample.certificate.value.name) :
    Checked prepared bank rootStage → Type 1
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩ => PUnit
  | ⟨⟨.found first, .ready firstCommon _, _⟩, ⟨.found last, .inconclusive _ _ _ _, _⟩, _⟩ =>
      (lastRefinement : RootBranch.Refinement prepared.lastSample last.original.sample
        (prepared.lastQueryEquivalent.symm.trans (lastQuery last))) ×
      { admission : Cell.Admission prepared.preparation.cell targets bank //
        admission = prepared.admitBranches first last (RootBranch.ofCommonRefinement firstCommon)
          lastRefinement.2.val }
  | ⟨⟨.found first, .inconclusive _ _ _ _, _⟩, ⟨.found last, .ready lastCommon _, _⟩, _⟩ =>
      (firstRefinement : RootBranch.Refinement prepared.firstSample first.original.sample
        (prepared.firstQueryEquivalent.symm.trans (firstQuery first))) ×
      { admission : Cell.Admission prepared.preparation.cell targets bank //
        admission = prepared.admitBranches first last firstRefinement.2.val
          (RootBranch.ofCommonRefinement lastCommon) }
  | ⟨⟨.found first, .inconclusive _ _ _ _, _⟩, ⟨.found last, .inconclusive _ _ _ _, _⟩, _⟩ =>
      (firstRefinement : RootBranch.Refinement prepared.firstSample first.original.sample
        (prepared.firstQueryEquivalent.symm.trans (firstQuery first))) ×
      (lastRefinement : RootBranch.Refinement prepared.lastSample last.original.sample
        (prepared.lastQueryEquivalent.symm.trans (lastQuery last))) ×
      { admission : Cell.Admission prepared.preparation.cell targets bank //
        admission = prepared.admitBranches first last firstRefinement.2.val lastRefinement.2.val }
  | ⟨⟨.absent _, _, _⟩, _, _⟩ => PEmpty
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩, _⟩ => PEmpty
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent _, _, _⟩, _⟩ => PEmpty

/-- The geometrically derived endpoint comparisons and only genuinely additional original-owner payment data.

The original Checked cache remains the nominal parent. Its lookup outcomes,
old refinement candidates and ready Commons remain unchanged. Comparisons
to any successful actual lookup at each nominal point are supplied by the
same original source, adjacency and returning-root construction.
-/
@[expose] def Completion (checked : Checked prepared bank rootStage) :=
  (firstQuery : (found : Vertex.Bank.Found bank (startPoint parent)) →
    NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      found.original.sample.certificate.value.name) ×
  (lastQuery : (found : Vertex.Bank.Found bank (finishPoint parent)) →
    NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      found.original.sample.certificate.value.name) × CompletionResult firstQuery lastQuery checked

namespace Completion

/-- Read the admission using old ready Commons and only the additional original acquisitions actually needed. -/
def admission : (checked : Checked prepared bank rootStage) → Completion checked →
    Cell.Admission prepared.preparation.cell targets bank
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, result⟩, _ => result.val
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed => completed.2.2.2.val
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩, completed => completed.2.2.2.val
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, completed =>
      completed.2.2.2.2.val
  | ⟨⟨.absent _, _, _⟩, _, _⟩, completed => nomatch completed.2.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩, _⟩, completed => nomatch completed.2.2
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent _, _, _⟩, _⟩, completed => nomatch completed.2.2

/-- Any completion of already successful checks reads the identical original admission cache.

Both old endpoint Commons remain authoritative. The additional completion
data cannot replace the admission materialized by those successful checks.
-/
theorem admission_eq_of_ready : (checked : Checked prepared bank rootStage) →
    (completed : Completion checked) → (paid : checked.Ready) →
    admission checked completed = checked.admission paid
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩, _, _ => by rfl
  | ⟨⟨.absent _, _, _⟩, _, _⟩, _, paid => False.elim paid.1
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, _, _⟩, _, paid => False.elim paid.1
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩, _⟩, _, paid => False.elim paid.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, _, paid => False.elim paid.2

end Completion

/-- Derive additional payment from actual endpoint-root comparisons while reusing every already ready original cache.

The erased membership witnesses eliminate a genuinely impossible absence;
they do not select an entry or execute a request. Both actual old lookups
remain untouched. New common-owner and numerical admission work occurs only
in the branches whose original finite containment attempt was inconclusive.
-/
def complete (checked : Checked prepared bank rootStage)
    (firstPresent : ∃ entry, entry ∈ bank ∧ entry.point = startPoint parent)
    (lastPresent : ∃ entry, entry ∈ bank ∧ entry.point = finishPoint parent)
    (firstQuery : (found : Vertex.Bank.Found bank (startPoint parent)) →
      NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
        found.original.sample.certificate.value.name)
    (lastQuery : (found : Vertex.Bank.Found bank (finishPoint parent)) →
      NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
        found.original.sample.certificate.value.name) : Completion checked :=
  ⟨firstQuery, lastQuery,
    match checked with
    | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .ready _ _, _⟩, _⟩ => PUnit.unit
    | ⟨⟨.found first, .ready firstCommon _, _⟩, ⟨.found last, .inconclusive _ _ _ _, _⟩, _⟩ =>
        let lastRefinement := RootBranch.acquire prepared.lastSample last.original.sample
          (prepared.lastQueryEquivalent.symm.trans (lastQuery last))
        let admission := prepared.admitBranches first last (RootBranch.ofCommonRefinement firstCommon)
          lastRefinement.2.val
        ⟨lastRefinement, ⟨admission, rfl⟩⟩
    | ⟨⟨.found first, .inconclusive _ _ _ _, _⟩, ⟨.found last, .ready lastCommon _, _⟩, _⟩ =>
        let firstRefinement := RootBranch.acquire prepared.firstSample first.original.sample
          (prepared.firstQueryEquivalent.symm.trans (firstQuery first))
        let admission := prepared.admitBranches first last firstRefinement.2.val
          (RootBranch.ofCommonRefinement lastCommon)
        ⟨firstRefinement, ⟨admission, rfl⟩⟩
    | ⟨⟨.found first, .inconclusive _ _ _ _, _⟩, ⟨.found last, .inconclusive _ _ _ _, _⟩, _⟩ =>
        let firstRefinement := RootBranch.acquire prepared.firstSample first.original.sample
          (prepared.firstQueryEquivalent.symm.trans (firstQuery first))
        let lastRefinement := RootBranch.acquire prepared.lastSample last.original.sample
          (prepared.lastQueryEquivalent.symm.trans (lastQuery last))
        let admission := prepared.admitBranches first last firstRefinement.2.val lastRefinement.2.val
        ⟨firstRefinement, lastRefinement, ⟨admission, rfl⟩⟩
    | ⟨⟨.absent missing, _, _⟩, _, _⟩ => False.elim (by
        have found := (Vertex.Bank.Outcome.absent missing).locate firstPresent
        have impossible := missing.symm.trans found.present
        cases impossible)
    | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent missing, _, _⟩, _⟩ => False.elim (by
        have found := (Vertex.Bank.Outcome.absent missing).locate lastPresent
        have impossible := missing.symm.trans found.present
        cases impossible)
    | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, ⟨.absent missing, _, _⟩, _⟩ => False.elim (by
        have found := (Vertex.Bank.Outcome.absent missing).locate lastPresent
        have impossible := missing.symm.trans found.present
        cases impossible)⟩

end Checked

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
