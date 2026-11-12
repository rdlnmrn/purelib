module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked.Ready
import Purelib.Data.List.DependentProduct

/-! # Actual checked source stages on the original centered parent chain

The original cover and geometric spine determine one actual source cache,
finite bank and complete family of endpoint attempts. Successful readiness
assembles the existing Stage from those same stored cells and admissions.
An incomplete attempt retains every actual lookup, candidate, unpaid side
condition and the common finite stopping request. No desired sample bound
or inferred returning sheet is supplied as an input.
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
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}

section Parents

variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage floor : Nat}
variable {targets : CellEndpoints.Targets original stage} {rootStage : Nat}

/-- Request one original three-channel bank entry at each retained source vertex in the same parent order.

Each entry consumes its actual already stored Vertex, primitive factors
and denotations. The actual bank is materialized once before endpoint
lookups; duplicate physical points remain separate original occurrences.
-/
@[expose] def requestBank : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → PreparedParents covered floor targets →
    Vertex.Bank parameter targets.endpoint
  | [], .nil, _ => []
  | _ :: _, .cons _ _ covered, prepared =>
      Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive ::
        requestBank covered prepared.2

/-- Independent allocations on the same canonical covered parents retain the same ordered original bank vertices.

Only the requested bank readings and numerical preparation budgets may
change. Original parent occurrences, Points, Vertex caches and order are
preserved, including repeated signed keys; no coordinate injectivity or
root comparison is assumed.
-/
theorem requestBank_prepareCovered_origins
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex : Nat} (firstFloor lastFloor : Nat)
    (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} → (covered : CoveredParents count parents) →
    (requestBank (frame := frame) (targets := firstTargets) covered
        (prepareCovered covered firstFloor firstTargets)).map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
      (requestBank (frame := frame) (targets := lastTargets) covered
        (prepareCovered covered lastFloor lastTargets)).map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint))
  | [], .nil => by rfl
  | parent :: parents, .cons patch inside remaining => by
    let firstHead := prepareParent patch count firstFloor inside firstTargets
    let lastHead := prepareParent patch count lastFloor inside lastTargets
    have firstStep :
        (requestBank (frame := frame) (targets := firstTargets)
          (CoveredParents.cons patch inside remaining)
          (prepareCovered (CoveredParents.cons patch inside remaining) firstFloor firstTargets)).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
        (⟨PreparedParent.startPoint parent, firstHead.firstVertex.val⟩ :
            Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) ::
          (requestBank (frame := frame) (targets := firstTargets) remaining
            (prepareCovered remaining firstFloor firstTargets)).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) :=
      congrArg (fun prepared :
          PreparedParents (CoveredParents.cons patch inside remaining) firstFloor firstTargets =>
        (requestBank (frame := frame) (targets := firstTargets)
          (CoveredParents.cons patch inside remaining) prepared).map (fun entry =>
          (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
        (prepareCovered_cons patch inside remaining firstFloor firstTargets)
    have lastStep :
        (requestBank (frame := frame) (targets := lastTargets)
          (CoveredParents.cons patch inside remaining)
          (prepareCovered (CoveredParents.cons patch inside remaining) lastFloor lastTargets)).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) =
        (⟨PreparedParent.startPoint parent, lastHead.firstVertex.val⟩ :
            Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) ::
          (requestBank (frame := frame) (targets := lastTargets) remaining
            (prepareCovered remaining lastFloor lastTargets)).map (fun entry =>
            (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)) :=
      congrArg (fun prepared :
          PreparedParents (CoveredParents.cons patch inside remaining) lastFloor lastTargets =>
        (requestBank (frame := frame) (targets := lastTargets)
          (CoveredParents.cons patch inside remaining) prepared).map (fun entry =>
          (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint)))
        (prepareCovered_cons patch inside remaining lastFloor lastTargets)
    have headSame :
        (⟨PreparedParent.startPoint parent, firstHead.firstVertex.val⟩ :
          Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) =
        ⟨PreparedParent.startPoint parent, lastHead.firstVertex.val⟩ :=
      congrArg (fun original : Vertex parameter (PreparedParent.startPoint parent) =>
        (⟨PreparedParent.startPoint parent, original⟩ :
          Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint))
        (prepareParent_firstVertex_eq patch count firstFloor lastFloor inside firstTargets lastTargets)
    have tailSame := requestBank_prepareCovered_origins (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) firstFloor lastFloor firstTargets lastTargets remaining
    have firstCons := congrArg (fun original : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint =>
      original :: (requestBank (frame := frame) (targets := firstTargets) remaining
        (prepareCovered remaining firstFloor firstTargets)).map (fun entry =>
        (⟨entry.point, entry.original⟩ : Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint))) headSame
    have lastCons := congrArg
      (fun originals : List (Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) =>
        (⟨PreparedParent.startPoint parent, lastHead.firstVertex.val⟩ :
          Σ originalPoint : LiftedPoint 2, Vertex parameter originalPoint) :: originals) tailSame
    exact firstStep.trans (firstCons.trans (lastCons.trans lastStep.symm))

/-- Both endpoint checking caches at every exact original bounded parent occurrence. -/
abbrev Checks {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) :=
  DependentProduct parents (fun index => PreparedParent.Checked (prepared.entry index) bank rootStage)

namespace Checks

variable {bank : Vertex.Bank parameter targets.endpoint}

/-- All actual original endpoint attempts of the stored parent family have passed. -/
@[expose] def Ready : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    Checks covered prepared bank rootStage → Prop
  | [], .nil, _, _ => True
  | _ :: _, .cons _ _ covered, prepared, checked =>
      checked.1.Ready ∧ Ready covered prepared.2 checked.2

/-- Decide complete readiness by reading the stored head attempts and unchanged stored tail only. -/
@[expose] def decideReady : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (checked : Checks covered prepared bank rootStage) → Decidable (Ready covered prepared checked)
  | [], .nil, _, _ => isTrue True.intro
  | _ :: _, .cons _ _ covered, prepared, checked =>
      match checked.1.decideReady with
      | isFalse unpaid => isFalse (fun ready => unpaid ready.1)
      | isTrue firstReady =>
          match decideReady covered prepared.2 checked.2 with
          | isFalse unpaid => isFalse (fun ready => unpaid ready.2)
          | isTrue tailReady => isTrue ⟨firstReady, tailReady⟩

/-- Join the actual already computed admissions along the identical original source and geometry spine. -/
def admissions : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (checked : Checks covered prepared bank rootStage) → Ready covered prepared checked →
      Admissions targets bank (sources covered prepared chain)
  | [], .nil, _, _, _, .nil point, _, _ => .nil point
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain, checked, ready =>
      .cons (checked.1.admission ready.1) (admissions covered prepared.2 chain checked.2 ready.2)

end Checks

/-- Materialize every original parent attempt once against the same actual global bank and stopping stage.

The existing dependent list product stores both endpoint lookups, all
actual refinement candidates and each successful original admission. It
does not retain a producer to be run again for different relation rows.
-/
def checkParents {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) : Checks covered prepared bank rootStage :=
  DependentProduct.ofFn parents (fun index => (prepared.entry index).check bank rootStage)

/-- The original checking product retains the whole original check at each bounded parent occurrence. -/
theorem checkParents_entry {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (bank : Vertex.Bank parameter targets.endpoint) (rootStage : Nat) (index : Fin parents.length) :
    DependentProduct.get parents (checkParents covered prepared bank rootStage) index =
      (prepared.entry index).check bank rootStage := by
  unfold checkParents
  exact DependentProduct.get_ofFn parents (fun index => (prepared.entry index).check bank rootStage) index

/-- Every original bounded source occurrence contributes its identical retained vertex request to the actual bank. -/
theorem requestBank_entry_member : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (index : Fin parents.length) →
    Vertex.Entry.request (prepared.entry index).firstVertex.val targets.endpoint targets.endpoint_positive ∈
      requestBank covered prepared
  | [], .nil, _, index => Fin.elim0 index
  | _ :: _, .cons _ _ covered, prepared, index => by
      refine Fin.cases ?_ ?_ index
      · exact List.Mem.head _
      · intro tail
        exact List.Mem.tail _ (requestBank_entry_member covered prepared.2 tail)

section RetainedAcquisitions

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- All original retained source-vertex occurrences belong to one actual materialized bank.

This is erased membership of complete original entries. Its entry factories
are never evaluated as data arguments to a bank lookup or owner acquisition.
-/
abbrev SourceMembers {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (bank : Vertex.Bank parameter targets.endpoint) :=
  ∀ index : Fin parents.length,
    Vertex.Entry.request (prepared.entry index).firstVertex.val targets.endpoint targets.endpoint_positive ∈ bank

/-- The original requestBank factory pays every original source-occurrence membership without another request. -/
theorem requestBank_sourceMembers {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets) :
    SourceMembers covered prepared (requestBank covered prepared) :=
  fun index => requestBank_entry_member covered prepared index

/-- Completion caches at every exact bounded occurrence of the original retained parent checks.

An entry retains additional factories only for its actual unpaid endpoint
attempts. Existing ready Commons and admissions are read from that exact
original Checked parent. The dependent product materializes each completion
once and does not retain a cell-producing function in place of its data.
-/
@[expose] def Acquisitions {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {bank : Vertex.Bank parameter targets.endpoint} (checked : Checks covered prepared bank rootStage) :=
  DependentProduct parents (fun index => PreparedParent.Checked.Completion
    (DependentProduct.get parents checked index))

namespace Acquisitions

/-- Prepend the retained original head completion to the identical stored tail without rebuilding either cache.

The original covered list, source preparation and checking product determine
both entry types. Their bounded-index conversion is checked here before any
concrete geometric comparison callbacks enter the recursive construction.
-/
@[expose] def cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (prepared : PreparedParents (CoveredParents.cons patch inside covered) floor targets)
    {bank : Vertex.Bank parameter targets.endpoint}
    (checked : Checks (CoveredParents.cons patch inside covered) prepared bank rootStage)
    (first : PreparedParent.Checked.Completion checked.1)
    (remaining : Acquisitions covered prepared.2 checked.2) :
    Acquisitions (CoveredParents.cons patch inside covered) prepared checked :=
  ⟨first, remaining⟩

end Acquisitions

/-- Pay original local admissions on a genuine closed-root continuation spine and a distinct actual source bank.

The retained endpoint lookup outcomes are consumed directly. Erased
membership and bank distinctness identify each selected source owner.
Actual RootChain adjacency and return comparisons identify finishing
owners before any additional common-refinement acquisition. Ready Commons
and admissions are reused; only unpaid endpoint attempts acquire new work.
-/
def acquireParents : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (bank : Vertex.Bank parameter targets.endpoint) → Vertex.Bank.Distinct bank →
    SourceMembers covered prepared bank →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    {incoming returning : Named} → RootChain parents incoming returning →
    (returnFound : Vertex.Bank.Found bank finish) →
    NamedEquivalent returning returnFound.original.sample.certificate.value.name →
    (checked : Checks covered prepared bank rootStage) → Acquisitions covered prepared checked
  | [], .nil, _, _, _, _, _, _, .nil _, _, _, .nil _, _, _, _ => PUnit.unit
  | [parent], .cons firstPatch firstInside .nil, prepared, bank, distinct, members, _, finish, .cons _ chain, _, _,
      .cons _ _ (.nil finishing), returnFound, returnEquivalent, checked =>
      have emptyEnds : ∀ {left right : LiftedPoint 2},
          CenteredPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
            (start := left) (finish := right) → left = right := by
        intro left right retained
        cases retained
        rfl
      have closing : PreparedParent.finishPoint parent = finish := emptyEnds chain
      have firstPresent : ∃ entry, entry ∈ bank ∧ entry.point = PreparedParent.startPoint parent :=
        ⟨Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive,
          members 0, rfl⟩
      let firstQuery := fun found => prepared.1.firstQueryToFound distinct found rfl (members 0)
      have lastPresent : ∃ entry, entry ∈ bank ∧ entry.point = PreparedParent.finishPoint parent :=
        ⟨returnFound.entry, returnFound.member, returnFound.point_eq.trans closing.symm⟩
      let lastQuery := fun (found : Vertex.Bank.Found bank (PreparedParent.finishPoint parent)) =>
        have names : returnFound.original.sample.certificate.value.name =
            found.original.sample.certificate.value.name := by
          cases closing
          exact congrArg (fun vertex : Vertex parameter (PreparedParent.finishPoint parent) =>
            vertex.sample.certificate.value.name) (returnFound.original_eq found)
        finishing.trans (NamedEquivalent.transport rfl names returnEquivalent)
      let completed : PreparedParent.Checked.Completion checked.1 :=
        checked.1.complete firstPresent lastPresent firstQuery lastQuery
      Acquisitions.cons firstPatch firstInside CoveredParents.nil prepared checked completed PUnit.unit
  | parent :: nextParent :: remainingParents, .cons firstPatch firstInside (.cons nextPatch nextInside covered),
      prepared, bank, distinct, members, _, _, .cons _ chain, _, _, .cons _ _ roots,
      returnFound, returnEquivalent, checked =>
      have headStart : ∀ {left right : LiftedPoint 2},
          CenteredPathChain (nextParent :: remainingParents) (start := left) (finish := right) →
            PreparedParent.startPoint nextParent = left := by
        intro left right retained
        cases retained
        rfl
      have incidence : PreparedParent.startPoint nextParent = PreparedParent.finishPoint parent := headStart chain
      have firstPresent : ∃ entry, entry ∈ bank ∧ entry.point = PreparedParent.startPoint parent :=
        ⟨Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive,
          members 0, rfl⟩
      let firstQuery := fun found => prepared.1.firstQueryToFound distinct found rfl (members 0)
      let nextPrepared := prepared.2.1
      have lastPresent : ∃ entry, entry ∈ bank ∧ entry.point = PreparedParent.finishPoint parent :=
        ⟨Vertex.Entry.request nextPrepared.firstVertex.val targets.endpoint targets.endpoint_positive,
          members (Fin.succ 0), incidence⟩
      let lastQuery := fun (found : Vertex.Bank.Found bank (PreparedParent.finishPoint parent)) =>
        roots.firstEquivalent.trans
          (nextPrepared.firstQueryToFound distinct found incidence (members (Fin.succ 0)))
      let completed : PreparedParent.Checked.Completion checked.1 :=
        checked.1.complete firstPresent lastPresent firstQuery lastQuery
      let remaining : Acquisitions (CoveredParents.cons nextPatch nextInside covered) prepared.2 checked.2 :=
        acquireParents (CoveredParents.cons nextPatch nextInside covered) prepared.2 bank distinct
          (fun index => members index.succ) chain roots returnFound returnEquivalent checked.2
      Acquisitions.cons firstPatch firstInside (CoveredParents.cons nextPatch nextInside covered)
        prepared checked completed remaining

namespace Acquisitions

variable {bank : Vertex.Bank parameter targets.endpoint}

/-- Join actual completed admissions on the identical original cells, checks and geometric parent spine. -/
def admissions : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (checked : Checks covered prepared bank rootStage) → Acquisitions covered prepared checked →
    Admissions targets bank (sources covered prepared chain)
  | [], .nil, _, _, _, .nil point, _, _ => .nil point
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain, checked, acquired =>
      .cons (PreparedParent.Checked.Completion.admission checked.1 acquired.1)
        (admissions covered prepared.2 chain checked.2 acquired.2)

/-- Retain completion data from each SAME successful original check without a bank-key injectivity premise.

Every head consumes its own old successful CommonRefinements and cached
admission; recursion reads the unchanged original tail. No lookup, owner
refinement, endpoint request or numerical admission factory executes.
-/
def ofReady : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (checked : Checks covered prepared bank rootStage) → Checks.Ready covered prepared checked →
    Acquisitions covered prepared checked
  | [], .nil, _, _, _ => PUnit.unit
  | _ :: _, .cons patch inside covered, prepared, checked, paid =>
      cons patch inside covered prepared checked
        (PreparedParent.Checked.completeReady checked.1 paid.1)
        (ofReady covered prepared.2 checked.2 paid.2)

/-- The ready completion fold retains exactly the original successful admission at every signed occurrence. -/
theorem admissions_ofReady : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (checked : Checks covered prepared bank rootStage) → (paid : Checks.Ready covered prepared checked) →
    admissions covered prepared chain checked (ofReady covered prepared checked paid) =
      Checks.admissions covered prepared chain checked paid
  | [], .nil, _, _, _, .nil _, _, _ => by rfl
  | _ :: _, .cons _ _ covered, prepared, _, _, .cons _ chain, checked, paid => by
      change Admissions.cons
          (PreparedParent.Checked.Completion.admission checked.1
            (PreparedParent.Checked.completeReady checked.1 paid.1))
          (admissions covered prepared.2 chain checked.2 (ofReady covered prepared.2 checked.2 paid.2)) =
        Admissions.cons (checked.1.admission paid.1)
          (Checks.admissions covered prepared.2 chain checked.2 paid.2)
      rewrite [PreparedParent.Checked.completeReady_admission,
        admissions_ofReady covered prepared.2 chain checked.2 paid.2]
      rfl

end Acquisitions

end RetainedAcquisitions

end Parents

namespace Checks

/-- Assemble the existing original Stage from the same counted path, actual bank and successful stored attempts.

The original path's Targets factory and actual basepoint lookup remain
separate inputs. All local admissions and three relation telescopes are
read from the checked original cache; no source model is constructed again.
-/
def stage {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor rootStage : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) (checked : Checks covered prepared bank rootStage)
    (paid : Ready covered prepared checked) :
    Stage parameter ⟨point, chain.path⟩ index :=
  let sources := sources covered prepared chain
  let admitted := admissions covered prepared chain checked paid
  Stage.ofAdmissions targets computed bank base sources admitted

/-- A ready decision retains the whole actual Stage factory; an unpaid decision creates no Stage. -/
@[expose] def StageResult {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor rootStage : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) (checked : Checks covered prepared bank rootStage) :
    Decidable (Ready covered prepared checked) → Type 1
  | isTrue paid => { result : Stage parameter ⟨point, chain.path⟩ index //
      result = stage covered chain targets computed prepared bank base checked paid }
  | isFalse _ => PUnit

namespace StageResult

/-- The retained whole Stage factory determines the complete result in either readiness branch. -/
private theorem eq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor rootStage : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) (checked : Checks covered prepared bank rootStage)
    (decision : Decidable (Ready covered prepared checked))
    (first second : StageResult covered chain targets computed prepared bank base checked decision) :
    first = second := by
  cases decision with
  | isTrue _ =>
    cases first with
    | mk first first_eq =>
      cases second with
      | mk second second_eq =>
        have same : first = second := first_eq.trans second_eq.symm
        cases same
        rfl
  | isFalse _ =>
    cases first
    cases second
    rfl

end StageResult

end Checks

/-- One complete actual attempt to construct a count-paid Stage on a nonempty original closed centered chain.

Targets, six-channel sources, bank requests, actual base lookup and every
endpoint checking cache are retained once. The readiness decision records
success or incompleteness of all stored cases at the original common
stopping stage; only success retains the original constructed Stage.
-/
abbrev StageAttempt {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :=
  (targets : { retained : CellEndpoints.Targets chain.path index //
    retained = CellEndpoints.Targets.build chain.path index }) ×
  (prepared : PreparedParents covered floor targets.val) ×
  (bank : { retained : Vertex.Bank parameter targets.val.endpoint // retained = requestBank covered prepared }) ×
  (base : Vertex.Bank.Found bank.val (PreparedParent.startPoint parent)) ×
  (checked : Checks covered prepared bank.val rootStage) ×
  (decision : Decidable (Checks.Ready covered prepared checked)) ×
  Checks.StageResult covered chain targets.val targets.property prepared bank.val base checked decision

namespace StageAttempt

/-- Construct the original bank/check tail on its exact retained nonempty covered-parent constructor.

The supplied preparation product is unchanged. Its literal head cover is
known before elaborating the original bank, lookup, check and conditional
Stage tuple; no source or allocation is reconstructed.
-/
private def ofPreparedHead {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor : Nat} (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents (CoveredParents.cons patch inside covered) floor targets) (rootStage : Nat) :
    StageAttempt (CoveredParents.cons patch inside covered) chain index floor rootStage :=
  let first := Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive
  let remaining := requestBank covered prepared.2
  let bank := first :: remaining
  let base := Vertex.Bank.Found.head first remaining
  let checked := checkParents (CoveredParents.cons patch inside covered) prepared bank rootStage
  let decision := Checks.decideReady (CoveredParents.cons patch inside covered) prepared checked
  let result : Checks.StageResult (CoveredParents.cons patch inside covered) chain targets computed
      prepared bank base checked decision :=
    match decision with
    | isTrue paid => ⟨Checks.stage (CoveredParents.cons patch inside covered) chain targets computed
        prepared bank base checked paid, rfl⟩
    | isFalse _ => PUnit.unit
  ⟨⟨targets, computed⟩, prepared, ⟨bank, rfl⟩, base, checked, decision, result⟩

/-- The exact curried attempt operation for each original covered-parent list.

Only the list is eliminated here. The empty case is an internal unit;
the nonempty case retains the original closed chain, allocation, source
product and stopping stage as arguments to the unchanged StageAttempt type.
-/
private def PreparedBuilder :
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) → CoveredParents count parents → Type 2
  | [], _ => PUnit
  | parent :: parents, covered =>
      (chain : CenteredPathChain (parent :: parents)
        (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)) →
      {index floor : Nat} → (targets : CellEndpoints.Targets chain.path index) →
      (computed : targets = CellEndpoints.Targets.build chain.path index) →
      (prepared : PreparedParents covered floor targets) → (rootStage : Nat) →
      StageAttempt covered chain index floor rootStage

/-- Eliminate the original unrestricted cover before applying the same retained-preparation head constructor.

The empty case produces only the internal unit. The nonempty case passes
every supplied actual argument to the same private constructor; it performs
no allocation, preparation, lookup, owner advancement or tail reconstruction.
-/
private def executePrepared : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → PreparedBuilder parents covered
  | [], .nil => PUnit.unit
  | _ :: _, .cons patch inside remaining =>
      fun chain {index floor} targets computed prepared rootStage =>
        ofPreparedHead (index := index) (floor := floor) patch inside remaining chain targets computed
          prepared rootStage

/-- Construct the original finite bank and checks from the same retained Targets and source preparations.

The nonempty covered spine supplies the actual first bank entry. The
whole preparation product is consumed unchanged; only the original bank,
lookups, checks, readiness decision and conditional Stage are constructed.
Both ready and unpaid outcomes retain the same original checker caches.
-/
def ofPrepared {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor : Nat} (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (rootStage : Nat) :
    StageAttempt covered chain index floor rootStage :=
  executePrepared (parents := parent :: parents) covered chain targets computed prepared rootStage

/-- The retained-preparation constructor stores the entire original checking product on its own actual bank. -/
theorem ofPrepared_checks {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor : Nat} (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (rootStage : Nat) :
    (ofPrepared covered chain targets computed prepared rootStage).2.2.2.2.1 =
      checkParents covered (ofPrepared covered chain targets computed prepared rootStage).2.1
        (ofPrepared covered chain targets computed prepared rootStage).2.2.1.val rootStage := by
  cases covered
  rfl

/-- A canonical input product remains the same whole canonical preparation on the constructor's own retained Targets. -/
theorem ofPrepared_canonical {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor : Nat} (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets)
    (canonical : prepared = prepareCovered covered floor targets) (rootStage : Nat) :
    (ofPrepared covered chain targets computed prepared rootStage).2.1 =
      prepareCovered covered floor (ofPrepared covered chain targets computed prepared rootStage).1.val := by
  cases canonical
  cases covered
  rfl

end StageAttempt

/-- Construct and retain the actual finite global source-stage attempt from the supplied original closed geometry.

One Targets allocation chooses all source and endpoint requests. The bank
contains one original source-vertex entry per parent; all lookups retain
its actual first matching entry. Genuine common-owner checks, rather than
coordinate or sheet equality, determine whether a Stage can be assembled.
An unpaid result retains every original attempt and proves no global root
mismatch or failure of a later finite refinement.
-/
def checkStage {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    StageAttempt (CoveredParents.cons patch inside covered) chain index floor rootStage :=
  let targets := CellEndpoints.Targets.build chain.path index
  let prepared := prepareCovered (CoveredParents.cons patch inside covered) floor targets
  StageAttempt.ofPreparedHead (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (index := index) (floor := floor)
    patch inside covered chain targets rfl prepared rootStage

/-- The canonical retained-preparation constructor and the original stage producer have the same whole attempt.

Both expressions call the same original head constructor on this literal
nonempty cover. Targets, preparations, bank, first lookup, complete checks,
readiness decision and both stored StageResult branches remain identical.
-/
theorem checkStage_eq_ofPrepared
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    checkStage (frame := frame) patch inside covered chain index floor rootStage =
      StageAttempt.ofPrepared (CoveredParents.cons patch inside covered) chain
        (CellEndpoints.Targets.build chain.path index) rfl
        (prepareCovered (CoveredParents.cons patch inside covered) floor
          (CellEndpoints.Targets.build chain.path index)) rootStage := by
  rfl

/-- The factored source-stage builder has exactly the original whole factory value and both readiness outcomes. -/
private theorem checkStage_factory {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    checkStage patch inside covered chain index floor rootStage =
    let targets := CellEndpoints.Targets.build chain.path index
    let prepared := prepareCovered (CoveredParents.cons patch inside covered) floor targets
    let first := Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive
    let remaining := requestBank covered prepared.2
    let bank := first :: remaining
    let base := Vertex.Bank.Found.head first remaining
    let checked := checkParents (CoveredParents.cons patch inside covered) prepared bank rootStage
    let decision := Checks.decideReady (CoveredParents.cons patch inside covered) prepared checked
    let result : Checks.StageResult (CoveredParents.cons patch inside covered) chain targets rfl
        prepared bank base checked decision :=
      match decision with
      | isTrue paid => ⟨Checks.stage (CoveredParents.cons patch inside covered) chain targets rfl
          prepared bank base checked paid, rfl⟩
      | isFalse _ => PUnit.unit
    ⟨⟨targets, rfl⟩, prepared, ⟨bank, rfl⟩, base, checked, decision, result⟩ := by
  let targets := CellEndpoints.Targets.build chain.path index
  let prepared := prepareCovered (CoveredParents.cons patch inside covered) floor targets
  let first := Vertex.Entry.request prepared.1.firstVertex.val targets.endpoint targets.endpoint_positive
  let remaining := requestBank covered prepared.2
  let bank := first :: remaining
  let base := Vertex.Bank.Found.head first remaining
  let checked := checkParents (CoveredParents.cons patch inside covered) prepared bank rootStage
  let decision := Checks.decideReady (CoveredParents.cons patch inside covered) prepared checked
  let result : Checks.StageResult (CoveredParents.cons patch inside covered) chain targets rfl
      prepared bank base checked decision :=
    match decision with
    | isTrue paid => ⟨Checks.stage (CoveredParents.cons patch inside covered) chain targets rfl
        prepared bank base checked paid, rfl⟩
    | isFalse _ => PUnit.unit
  let pack (actual : Checks.StageResult (CoveredParents.cons patch inside covered) chain targets rfl
      prepared bank base checked decision) :
      StageAttempt (CoveredParents.cons patch inside covered) chain index floor rootStage :=
    ⟨⟨targets, rfl⟩, prepared, ⟨bank, rfl⟩, base, checked, decision, actual⟩
  exact congrArg pack
    (Checks.StageResult.eq (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (index := index) (floor := floor) (rootStage := rootStage)
      (CoveredParents.cons patch inside covered) chain targets rfl prepared bank base checked decision
      (checkStage patch inside covered chain index floor rootStage).2.2.2.2.2.2 result)

namespace Acquisitions

/-- Build the existing original Stage directly from retained actual common-owner acquisitions and source cells. -/
def stage {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) {rootStage : Nat}
    (checked : Checks covered prepared bank rootStage) (acquired : Acquisitions covered prepared checked) :
    Stage parameter ⟨point, chain.path⟩ index :=
  Stage.ofAdmissions targets computed bank base (sources covered prepared chain)
    (admissions covered prepared chain checked acquired)

/-- The actual constructed Stage retains the literal source cells of the original covered-parent cache and chain. -/
theorem stage_sources {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) {rootStage : Nat}
    (checked : Checks covered prepared bank rootStage) (acquired : Acquisitions covered prepared checked) :
    (stage covered chain targets computed prepared bank base checked acquired).sources =
      sources covered prepared chain := by rfl

/-- The ready completion fold has the SAME original Stage factory expression on those identical cached admissions.

This equality transports the stored successful StageResult; it does not
execute either Stage expression as data. All original source, bank, base
lookup, target and signed occurrence owners remain the identical inputs.
-/
theorem stage_ofReady {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point)) {index floor : Nat}
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank point) {rootStage : Nat}
    (checked : Checks covered prepared bank rootStage) (paid : Checks.Ready covered prepared checked) :
    stage covered chain targets computed prepared bank base checked (ofReady covered prepared checked paid) =
      Checks.stage covered chain targets computed prepared bank base checked paid := by
  unfold stage Checks.stage
  rewrite [admissions_ofReady covered prepared chain checked paid]
  rfl

end Acquisitions

/-- The original whole source-stage factory retains its exact prepared family on the SAME actual global Targets.

This readback exposes only the existing selected preparation. The source
factory and its endpoint bank/checks stay opaque; no caller reconstructs
an output or reruns preparation to prove its whole-cache equality.
-/
theorem checkStage_prepared {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    (checkStage patch inside covered chain index floor rootStage).2.1 =
      prepareCovered (CoveredParents.cons patch inside covered) floor
        (checkStage patch inside covered chain index floor rootStage).1.val := by
  rfl

/-- The original covered-stage producer retains its entire checking product on the same actual preparation and bank. -/
theorem checkStage_checks {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    (checkStage patch inside covered chain index floor rootStage).2.2.2.2.1 =
      checkParents (CoveredParents.cons patch inside covered)
        (checkStage patch inside covered chain index floor rootStage).2.1
        (checkStage patch inside covered chain index floor rootStage).2.2.1.val rootStage := by
  rfl

namespace StageAttempt

variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {covered : CoveredParents count (parent :: parents)}
variable {chain : CenteredPathChain (parent :: parents)
  (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
variable {index floor rootStage : Nat}

/-- The additional original-owner acquisition caches and Stage consuming exactly those same retained original sources.

The earlier finite attempt remains the nominal parent, including all old
lookup outcomes, candidate refinements and ready Commons/admissions. Only
actual unpaid endpoints acquire additional Commons. The resulting Stage
uses these same sources and bank without relabelling the old request.
-/
abbrev Completion (attempt : StageAttempt covered chain index floor rootStage) :=
  (acquired : Acquisitions covered attempt.2.1 attempt.2.2.2.2.1) ×
  { result : Stage parameter ⟨PreparedParent.startPoint parent, chain.path⟩ index //
    result = Acquisitions.stage covered chain attempt.1.val attempt.1.property attempt.2.1
      attempt.2.2.1.val attempt.2.2.2.1 attempt.2.2.2.2.1 acquired }

/-- Complete the actual retained source-stage attempt from its genuine closed root spine and distinct original bank.

Every source request, endpoint plan, selected lookup, old candidate and bank
reading comes from the supplied attempt. Actual geometric root comparisons
are derived before any additional Common acquisitions. Ready Commons are reused. The returned
Stage consumes their exact cached local admissions and original six lists;
no radial-to-spatial or canonical-integral identification is asserted.
-/
def complete (attempt : StageAttempt covered chain index floor rootStage)
    (distinct : Vertex.Bank.Distinct attempt.2.2.1.val) {root : Named}
    (roots : RootChain (parent :: parents) root root) : Completion attempt :=
  let prepared := attempt.2.1
  let bank := attempt.2.2.1.val
  have members : SourceMembers covered prepared bank :=
    Eq.mp (congrArg (fun actual => SourceMembers covered prepared actual) attempt.2.2.1.property.symm)
      (requestBank_sourceMembers covered prepared)
  let base := attempt.2.2.2.1
  let returning := roots.firstEquivalent.trans (prepared.1.firstQueryToFound distinct base rfl (members 0))
  let acquired := acquireParents covered prepared bank distinct members chain roots base returning
    attempt.2.2.2.2.1
  let result := Acquisitions.stage covered chain attempt.1.val attempt.1.property prepared bank base
    attempt.2.2.2.2.1 acquired
  ⟨acquired, ⟨result, rfl⟩⟩

/-- The actual original endpoint checks of this SAME retained attempt have all succeeded. -/
@[expose] def Ready (attempt : StageAttempt covered chain index floor rootStage) : Prop :=
  Checks.Ready covered attempt.2.1 attempt.2.2.2.2.1

/-- Complete a successful actual attempt using its SAME stored StageResult and original ready acquisition fold.

The retained decision selects the original successful Stage value. Its
factory equality and the exact admission-fold equality supply the existing
Completion contract. No replacement Stage, lookup, common-owner acquisition,
admission, source selection or request is executed, and repeated signed
keys need no Distinct certificate when their actual endpoint checks passed.
-/
def completeReady : (attempt : StageAttempt covered chain index floor rootStage) →
    attempt.Ready → Completion attempt
  | ⟨targets, prepared, bank, base, checked, isTrue paid, result⟩, _ =>
      let acquired := Acquisitions.ofReady covered prepared checked paid
      ⟨acquired, ⟨result.val, result.property.trans
        (Acquisitions.stage_ofReady covered chain targets.val targets.property prepared bank.val
          base checked paid).symm⟩⟩
  | ⟨_, _, _, _, _, isFalse unpaid, _⟩, paid => False.elim (unpaid paid)

/-- Read the actual original preparation product under its certified-equal computed target index.

The retained Targets cache and all original source data remain the owners.
The computed-index view performs only exact equality transport, permitting
analytic programmes to consume the same already selected preparations.
-/
def preparations (attempt : StageAttempt covered chain index floor rootStage) :
    PreparedParents covered floor (CellEndpoints.Targets.build chain.path index) :=
  attempt.2.1.castTargets attempt.1.property

/-- The prepared-stage computed-index view transports the same whole supplied product, without preparation replay. -/
theorem ofPrepared_preparations
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (targets : CellEndpoints.Targets chain.path index)
    (computed : targets = CellEndpoints.Targets.build chain.path index)
    (prepared : PreparedParents covered floor targets) (rootStage : Nat) :
    (ofPrepared covered chain targets computed prepared rootStage).preparations =
      prepared.castTargets computed := by
  cases covered
  rfl

/-- The computed-index preparation view retains the exact original source chain of the attempt. -/
theorem preparations_sources (attempt : StageAttempt covered chain index floor rootStage) :
    sources covered attempt.preparations chain = sources covered attempt.2.1 chain := by
  unfold preparations
  exact sources_castTargets covered attempt.2.1 attempt.1.property chain

/-- A completed Stage retains the source chain of that same actual original preparation cache. -/
theorem Completion.stage_sources (attempt : StageAttempt covered chain index floor rootStage)
    (completed : Completion attempt) :
    completed.2.val.sources = sources covered attempt.preparations chain := by
  have original := (congrArg
    (fun stage : Stage parameter ⟨PreparedParent.startPoint parent, chain.path⟩ index => stage.sources)
    completed.2.property).trans
      (Acquisitions.stage_sources covered chain attempt.1.val attempt.1.property attempt.2.1
        attempt.2.2.1.val attempt.2.2.2.1 attempt.2.2.2.2.1 completed.1)
  exact original.trans attempt.preparations_sources.symm

/-- A complete finite request retaining the original attempt as data beside its actual completion caches.

The completion remains indexed by that exact attempt. Storing both lets
programmes and source attachments read the original preparations and the
completed Stage without repeating source selection, lookup or refinement.
-/
@[expose] def Completed (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :=
  (attempt : StageAttempt covered chain index floor rootStage) × Completion attempt

namespace Completed

/-- Complete and retain one actual original request using its genuine closed root spine and actual distinct bank.

The existing completion operation consumes the original lookups and reuses
ready common-owner certificates. Only its unpaid endpoint cases acquire
additional work; the original attempt is stored unchanged beside the result.
-/
def acquire (attempt : StageAttempt covered chain index floor rootStage)
    (distinct : Vertex.Bank.Distinct attempt.2.2.1.val) {root : Named}
    (roots : RootChain (parent :: parents) root root) : Completed covered chain index floor rootStage :=
  let completed := attempt.complete distinct roots
  ⟨attempt, completed⟩

/-- Retain one actual successful attempt and its SAME original Stage without key injectivity or new execution.

The existing ready Commons and admission caches supply completion. This
finite success construction leaves all unresolved attempts visible and
establishes no total repeated-visit coherence for other stages or inputs.
-/
def ofReady (attempt : StageAttempt covered chain index floor rootStage)
    (paid : attempt.Ready) :
    Completed covered chain index floor rootStage :=
  let completed := attempt.completeReady paid
  ⟨attempt, completed⟩

/-- Ready completion keeps the entire supplied original attempt, including every actual checked outcome and cache. -/
theorem ofReady_attempt (attempt : StageAttempt covered chain index floor rootStage)
    (paid : attempt.Ready) :
    (ofReady attempt paid).1 = attempt := by rfl

end Completed

end StageAttempt

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
