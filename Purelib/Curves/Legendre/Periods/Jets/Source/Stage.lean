module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path
public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Indexed
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Refinement
public import Purelib.Integration.Path.Primitive.Cells.Keyed
public import Purelib.Integration.Path.Primitive.Cells.Targets
public import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Admitted original Legendre source stages

Original cell geometry determines the source target. Endpoint plans retain
the actual primitive requests, selected root witnesses, finite bank lookups
and common-owner branch geometry. Their computed comparisons construct the
three original cell telescopes, whose count-paid budgets are derived here.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib.Approximation.Rational
open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Cell

variable {parameter : Canonical} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}

set_option genInjectivity false in
/-- An original source cell's prepared endpoint and its retained common-owner transport to a finite bank entry.

The source point belongs to the original cell's chart. Its primitive requests
and one shared root attach to the same cell's model and odd-power caches.
The finite bank lookup and branch geometry remain separate original data. -/
structure Endpoint (cell : Cell (parameter := parameter) lifted) (point : LiftedPoint 2)
    {allocation : Rational} (bank : Vertex.Bank parameter allocation) where
  /-- The actual successful lookup in the original finite vertex bank. -/
  found : Vertex.Bank.Found bank point
  /-- The actual original source point at this endpoint coordinate. -/
  sample : ContinuedNeighborhood.Point cell.patch point.coordinate
  /-- The original floor used when preparing the endpoint requests. -/
  floor : Nat
  /-- The original three primitive requests and one root precision prepared before the model. -/
  plan : EndpointPlan sample floor allocation
  /-- The original endpoint plans attached to this exact original source model. -/
  attached : EndpointPlan.Attachment plan cell.request
  /-- The original common winding-one owner and both strict branch inclusions. -/
  branch : RootBranch sample found.original.sample

namespace Endpoint

/-- Reuse a prepared endpoint's attachment and cached point at another incident cell with the same source request. -/
@[expose] def ofAttachment (cell : Cell (parameter := parameter) lifted) {point : LiftedPoint 2}
    {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    (found : Vertex.Bank.Found bank point) {sample : ContinuedNeighborhood.Point cell.patch point.coordinate}
    {floor : Nat} (plan : EndpointPlan sample floor allocation)
    (attached : EndpointPlan.Attachment plan cell.request) (branch : RootBranch sample found.original.sample) :
    Endpoint cell point bank :=
  let retained : (prepared : EndpointPlan attached.root.owner floor allocation) ×
      EndpointPlan.Attachment prepared cell.request :=
    attached.root.owner_eq.symm ▸
      (⟨plan, attached⟩ : (prepared : EndpointPlan sample floor allocation) ×
        EndpointPlan.Attachment prepared cell.request)
  let retainedBranch : RootBranch attached.root.owner found.original.sample :=
    attached.root.owner_eq.symm ▸ branch
  ⟨found, attached.root.owner, floor, retained.1, retained.2, retainedBranch⟩

/-- The retained cached endpoint point is the actual original point supplied with the prepared plan. -/
theorem ofAttachment_sample (cell : Cell (parameter := parameter) lifted) {point : LiftedPoint 2}
    {allocation : Rational} {bank : Vertex.Bank parameter allocation}
    (found : Vertex.Bank.Found bank point) {sample : ContinuedNeighborhood.Point cell.patch point.coordinate}
    {floor : Nat} (plan : EndpointPlan sample floor allocation)
    (attached : EndpointPlan.Attachment plan cell.request) (branch : RootBranch sample found.original.sample) :
    (ofAttachment cell found plan attached branch).sample = sample := attached.root.owner_eq

/-- Attach a prepared endpoint to its actual source cell while retaining the finite bank lookup and branch geometry. -/
def ofPlan (cell : Cell (parameter := parameter) lifted) {point : LiftedPoint 2} {allocation : Rational}
    {bank : Vertex.Bank parameter allocation} (found : Vertex.Bank.Found bank point)
    {sample : ContinuedNeighborhood.Point cell.patch point.coordinate} {floor : Nat}
    (plan : EndpointPlan sample floor allocation) (branch : RootBranch sample found.original.sample)
    (stage : plan.requests.stage ≤ cell.request.selection.stage) : Endpoint cell point bank :=
  ofAttachment cell found plan (plan.attach cell.request stage) branch

end Endpoint

set_option genInjectivity false in
/-- The computed local admission of one actual source cell to the original count-paid vertex telescope.

The request target is the original computed displacement-cost allocation.
Endpoint comparisons consume the retained requests and common-owner branch
data. No local primitive bound or final polynomial-to-bank estimate is an
extra constructor input. -/
structure Admission (cell : Cell (parameter := parameter) lifted)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets original stage) (bank : Vertex.Bank parameter targets.endpoint) where
  /-- The retained geometric source cost shared by the actual model request. -/
  cost : Rational
  /-- The retained cost bounds this original cell's actual displacement quadrance. -/
  displacement_le : cell.primitives.displacementNorm ≤ cost
  /-- The actual original request uses the computed count-paid displacement target. -/
  target_eq : cell.target = targets.sourceTarget cost
  /-- The original starting point, requests, bank lookup and branch geometry. -/
  starting : Endpoint cell start bank
  /-- The original finishing point, requests, bank lookup and branch geometry. -/
  finishing : Endpoint cell finish bank
  /-- The computed first, second and scalar endpoint comparisons at the original start. -/
  startComparison : EndpointPlan.Attachment.Comparison
    starting.attached starting.found.original starting.found.readings
  /-- The computed first, second and scalar endpoint comparisons at the original finish. -/
  finishComparison : EndpointPlan.Attachment.Comparison
    finishing.attached finishing.found.original finishing.found.readings

/-- The original source selection and its actual displacement cost pay the count-derived local primitive ceiling.

The same source target is used for point-found and bounded-occurrence
admissions. Its scalar payment depends only on these original cell data,
not on a chosen bank lookup or endpoint comparison.
-/
theorem local_bound_le (cell : Cell (parameter := parameter) lifted)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets original stage) (cost : Rational)
    (displacement_le : cell.primitives.displacementNorm ≤ cost)
    (target_eq : cell.target = targets.sourceTarget cost) : cell.primitives.bound ≤ targets.localBound := by
  have costNonnegative := cell.primitives.displacementNorm_nonnegative.trans displacement_le
  have sourcePositive := targets.sourceTarget_positive cost costNonnegative
  have selected := cell.primitives.bound_le_selected_target
  have scalar := congrArg (fun target : Rational => cell.primitives.displacementNorm * target) target_eq
  exact (selected.trans_eq scalar).trans ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    displacement_le sourcePositive.le).trans (targets.sourceTarget_payment cost costNonnegative).le)

namespace Admission

variable {cell : Cell (parameter := parameter) lifted} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {bank : Vertex.Bank parameter targets.endpoint}

/-- Derive the original endpoint admissions from retained geometric costs, source plans and common-owner branches. -/
def build (cell : Cell (parameter := parameter) lifted) (targets : CellEndpoints.Targets original stage)
    (bank : Vertex.Bank parameter targets.endpoint) (cost : Rational)
    (displacement_le : cell.primitives.displacementNorm ≤ cost)
    (target_eq : cell.target = targets.sourceTarget cost)
    (starting : Endpoint cell start bank) (finishing : Endpoint cell finish bank) : Admission cell targets bank :=
  let startComparison := starting.attached.compare starting.found.original starting.found.readings
    starting.branch cell.startInside targets.endpoint_positive
  let finishComparison := finishing.attached.compare finishing.found.original finishing.found.readings
    finishing.branch cell.finishInside targets.endpoint_positive
  ⟨cost, displacement_le, target_eq, starting, finishing, startComparison, finishComparison⟩

/-- Retain an original cell admission under the same computed allocations transported to an equal-count path.

The original source cell, endpoint plans, selected root witnesses and paid
comparisons are reused. The enclosing path changes explicitly; its own
ordered source chain must still be supplied to close a stage telescope. -/
@[expose] def onPath (admission : Admission cell targets bank)
    {nextStart nextFinish : LiftedPoint 2} (next : LiftedPath 2 nextStart nextFinish)
    (sameCount : next.cellCount = original.cellCount) :
    Admission cell (targets.onPath next sameCount) bank :=
  ⟨admission.cost, admission.displacement_le, admission.target_eq, admission.starting, admission.finishing,
    admission.startComparison, admission.finishComparison⟩

/-- The actual source selection and geometric cost pay the original local primitive ceiling. -/
theorem local_le (admission : Admission cell targets bank) : cell.primitives.bound ≤ targets.localBound :=
  cell.local_bound_le targets admission.cost admission.displacement_le admission.target_eq

/-- The first original local primitive comparison obeys the computed common local allocation. -/
theorem zero_local_le (admission : Admission cell targets bank) : cell.primitives.zero.bound ≤ targets.localBound := by
  rewrite [cell.primitives.zero_bound_eq]
  exact admission.local_le

/-- The second original local primitive comparison obeys the same computed local allocation. -/
theorem one_local_le (admission : Admission cell targets bank) : cell.primitives.one.bound ≤ targets.localBound := by
  rewrite [cell.primitives.one_bound_eq]
  exact admission.local_le

/-- The scalar original local primitive comparison obeys the same computed local allocation. -/
theorem scalar_local_le (admission : Admission cell targets bank) :
    cell.primitives.scalar.bound ≤ targets.localBound := by
  rewrite [cell.primitives.scalar_bound_eq]
  exact admission.local_le

/-- The first original primitive's start is close to the actual shared bank reading. -/
theorem zero_start_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.zero.value.eval 0 - bank.zero start) ≤ targets.endpoint := by
  have bound := admission.startComparison.zero_le
  rewrite [admission.starting.found.zero_eq] at bound
  rewrite [cell.primitives.zero_start]
  exact bound

/-- The first original primitive's finish is close to the actual shared bank reading. -/
theorem zero_finish_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.zero.value.eval 1 - bank.zero finish) ≤ targets.endpoint := by
  have bound := admission.finishComparison.zero_le
  rewrite [admission.finishing.found.zero_eq] at bound
  rewrite [cell.primitives.zero_finish]
  exact bound

/-- The second original primitive's start is close to the actual shared bank reading. -/
theorem one_start_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.one.value.eval 0 - bank.one start) ≤ targets.endpoint := by
  have bound := admission.startComparison.one_le
  rewrite [admission.starting.found.one_eq] at bound
  rewrite [cell.primitives.one_start]
  exact bound

/-- The second original primitive's finish is close to the actual shared bank reading. -/
theorem one_finish_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.one.value.eval 1 - bank.one finish) ≤ targets.endpoint := by
  have bound := admission.finishComparison.one_le
  rewrite [admission.finishing.found.one_eq] at bound
  rewrite [cell.primitives.one_finish]
  exact bound

/-- The scalar original primitive's start is close to the actual shared bank reading. -/
theorem scalar_start_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.scalar.value.eval 0 - bank.scalar start) ≤ targets.endpoint := by
  have bound := admission.startComparison.scalar_le
  rewrite [admission.starting.found.scalar_eq] at bound
  rewrite [cell.primitives.scalar_start]
  exact bound

/-- The scalar original primitive's finish is close to the actual shared bank reading. -/
theorem scalar_finish_le (admission : Admission cell targets bank) :
    Norm.Basic.normSq (cell.primitives.scalar.value.eval 1 - bank.scalar finish) ≤ targets.endpoint := by
  have bound := admission.finishComparison.scalar_le
  rewrite [admission.finishing.found.scalar_eq] at bound
  rewrite [cell.primitives.scalar_finish]
  exact bound

end Admission

end Cell

set_option genInjectivity false in
/-- Original source-cell admissions in exact lifted-path order under one computed whole-stage budget and finite bank. -/
inductive Admissions {parameter : Canonical} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets original stage) (bank : Vertex.Bank parameter targets.endpoint) :
    {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} → Path parameter path → Type 1
  /-- The exact original empty source chain. -/
  | nil (point : LiftedPoint 2) : Admissions targets bank (.nil point)
  /-- Prepend the original source cell's computed admission without changing the source or path owners. -/
  | cons {start middle finish : LiftedPoint 2} {head : LiftedCell start middle} {tail : LiftedPath 2 middle finish}
      {source : Cell (parameter := parameter) head} {sources : Path parameter tail}
      (admission : Cell.Admission source targets bank) (remaining : Admissions targets bank sources) :
      Admissions targets bank (.cons source sources)

namespace Admissions

variable {parameter : Canonical} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {bank : Vertex.Bank parameter targets.endpoint}

/-- Concatenate original admissions while reusing the same actual source and geometric constructor fields. -/
@[expose] def append {start middle finish : LiftedPoint 2} {first : LiftedPath 2 start middle}
    {second : LiftedPath 2 middle finish} (leftSources : Path parameter first) {rightSources : Path parameter second} :
    Admissions targets bank leftSources → Admissions targets bank rightSources →
      Admissions targets bank (Path.append first leftSources rightSources)
  | .nil _, right => right
  | .cons (source := source) (sources := remaining) head tail, right =>
      .cons head (append remaining tail right)

/-- Reuse each original admission under the actual scalar allocations transported to an equal-count enclosing path. -/
@[expose] def onPath {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish} {sources : Path parameter path}
    (admissions : Admissions targets bank sources) {nextStart nextFinish : LiftedPoint 2}
    (next : LiftedPath 2 nextStart nextFinish) (sameCount : next.cellCount = original.cellCount) :
    Admissions (targets.onPath next sameCount) bank sources :=
  Admissions.casesOn admissions
    (fun point => .nil point)
    (fun {actualStart actualMiddle actualFinish head tail source sources} admitted remaining =>
      .cons (start := actualStart) (middle := actualMiddle) (finish := actualFinish)
        (head := head) (tail := tail) (source := source) (sources := sources)
        (admitted.onPath next sameCount) (remaining.onPath next sameCount))
termination_by structural admissions

/-- The admitted head-rotation result on an exactly closed original source chain.

A nonempty chain retains the closing endpoint equality and the same
endpoint comparisons in the source chain's cyclic order.
-/
@[expose] def HeadRotation {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish}
    (sources : Path parameter path) : Type 1 :=
  match sources with
  | .nil _ => PUnit
  | .cons (start := actualStart) (finish := actualFinish) source remaining =>
      (closed : actualFinish = actualStart) →
        Admissions targets bank ((Path.cons source remaining).rotate closed)

/-- Rotate original admissions using their actual stored source and geometric constructor fields. -/
@[expose] def rotate {start finish : LiftedPoint 2} {path : LiftedPath 2 start finish}
    {sources : Path parameter path} (admissions : Admissions targets bank sources) :
    HeadRotation (targets := targets) (bank := bank) sources :=
  Admissions.casesOn admissions
    (fun _ => PUnit.unit)
    (fun {actualStart actualMiddle actualFinish head tail source remaining} admitted rest closed => by
      cases closed
      exact append remaining rest
        (.cons (start := actualStart) (middle := actualMiddle) (finish := actualMiddle)
          (head := head) (tail := .nil actualMiddle) (source := source) (sources := .nil actualMiddle)
          admitted (.nil actualMiddle)))

/-- Move the original admitted head to the end while preserving all actual endpoint and comparison caches. -/
@[expose] def rotateHead {start middle : LiftedPoint 2} {head : LiftedCell start middle}
    {tail : LiftedPath 2 middle start} (sources : Path parameter (.cons head tail))
    (admissions : Admissions targets bank sources) : Admissions targets bank sources.rotateHead :=
  match sources, admissions with
  | .cons _ _, admitted => admitted.rotate rfl

/-- Construct the actual first-row primitive telescope from original admitted source cells and shared bank readings. -/
def zeroCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → Admissions targets bank sources →
    CellEndpoints.Cells bank.zero targets.localBound targets.endpoint sources.zero path
  | _, _, _, _, .nil point => .nil point
  | _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.zero _ (by rewrite [source.models.zero_eq]; rfl)
        (by rewrite [source.models.zero_eq]; rfl) source.primitives.zero admission.zero_local_le
        admission.zero_start_le admission.zero_finish_le remaining.zeroCells

/-- Construct the actual second-row primitive telescope from those same original admitted source cells. -/
def oneCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → Admissions targets bank sources →
    CellEndpoints.Cells bank.one targets.localBound targets.endpoint sources.one path
  | _, _, _, _, .nil point => .nil point
  | _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.one _ (by rewrite [source.models.one_eq]; rfl)
        (by rewrite [source.models.one_eq]; rfl) source.primitives.one admission.one_local_le
        admission.one_start_le admission.one_finish_le remaining.oneCells

/-- Construct the actual scalar primitive telescope from those same original admitted source cells. -/
def scalarCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → Admissions targets bank sources →
    CellEndpoints.Cells bank.scalar targets.localBound targets.endpoint sources.scalar path
  | _, _, _, _, .nil point => .nil point
  | _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.scalar _ (by rewrite [source.models.scalar_eq]; rfl)
        (by rewrite [source.models.scalar_eq]; rfl) source.primitives.scalar admission.scalar_local_le
        admission.scalar_start_le admission.scalar_finish_le remaining.scalarCells

end Admissions

namespace Cell

variable {parameter : Canonical} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}

section

attribute [local irreducible] RootBranch.Comparison RootBranch.Refinement

set_option genInjectivity false in
/-- A prepared endpoint attached to one exact original bank occurrence and its retained common-root factory.

The source Point, plan and attachment remain unchanged. Its positional
FoundAt has a whole lifted-point identity; the retained refinement keeps
the actual selected index, common owner and original acquire equation.
-/
structure OccurrenceEndpoint (cell : Cell (parameter := parameter) lifted) (point : LiftedPoint 2)
    {allocation : Rational} (bank : Vertex.Bank parameter allocation) (key : Fin bank.length) where
  /-- The complete actual bank value at this original occurrence. -/
  found : Vertex.Bank.FoundAt bank point key
  /-- The original continued source Point. -/
  sample : ContinuedNeighborhood.Point cell.patch point.coordinate
  /-- The original endpoint request floor. -/
  floor : Nat
  /-- The retained three primitive requests and shared root precision. -/
  plan : EndpointPlan sample floor allocation
  /-- The original source request consumes this same endpoint plan. -/
  attached : EndpointPlan.Attachment plan cell.request
  /-- The operational comparison derived from the actual original root-chain path. -/
  equivalent : RootBranch.Comparison sample found.original.sample
  /-- The same original common-refinement factory and its exact branch view. -/
  refinement : RootBranch.Refinement sample found.original.sample equivalent

constructive_injectivity OccurrenceEndpoint

end

namespace OccurrenceEndpoint

/-- Retain the supplied actual positional lookup, prepared Point, plan and whole common-refinement cache. -/
@[expose] def ofRefinement (cell : Cell (parameter := parameter) lifted) {point : LiftedPoint 2}
    {allocation : Rational} {bank : Vertex.Bank parameter allocation} {key : Fin bank.length}
    (found : Vertex.Bank.FoundAt bank point key)
    {sample : ContinuedNeighborhood.Point cell.patch point.coordinate} {floor : Nat}
    (plan : EndpointPlan sample floor allocation) (attached : EndpointPlan.Attachment plan cell.request)
    (equivalent : NamedEquivalent sample.certificate.value.name
      found.original.sample.certificate.value.name)
    (refinement : RootBranch.Refinement sample found.original.sample equivalent) :
    OccurrenceEndpoint cell point bank key :=
  ⟨found, sample, floor, plan, attached, equivalent, refinement⟩

end OccurrenceEndpoint

set_option genInjectivity false in
/-- One source cell's computed admission at two original bank-position keys.

Each endpoint retains its actual complete bank occurrence and original
source caches. Both numerical comparisons are computed from their retained
strict common-root certificates, with no signed estimate as an input.
-/
structure OccurrenceAdmission (cell : Cell (parameter := parameter) lifted)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets original stage) (bank : Vertex.Bank parameter targets.endpoint)
    (firstKey lastKey : Fin bank.length) where
  /-- The actual nonnegative displacement cost. -/
  cost : Rational
  /-- This cost pays the original source cell's squared displacement. -/
  displacement_le : cell.primitives.displacementNorm ≤ cost
  /-- The source request has its original computed count-paid target. -/
  target_eq : cell.target = targets.sourceTarget cost
  /-- The original prepared starting endpoint on its actual positional bank owner. -/
  starting : OccurrenceEndpoint cell start bank firstKey
  /-- The independent original finishing endpoint on its actual positional bank owner. -/
  finishing : OccurrenceEndpoint cell finish bank lastKey
  /-- The computed starting comparisons retain those same Point, plan and bank readings. -/
  startComparison : EndpointPlan.Attachment.Comparison starting.attached
    starting.found.original starting.found.readings
  /-- The computed finishing comparisons retain their same original inputs. -/
  finishComparison : EndpointPlan.Attachment.Comparison finishing.attached
    finishing.found.original finishing.found.readings

constructive_injectivity OccurrenceAdmission

namespace OccurrenceAdmission

variable {cell : Cell (parameter := parameter) lifted} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {bank : Vertex.Bank parameter targets.endpoint} {firstKey lastKey : Fin bank.length}

/-- Compute both original primitive-to-bank comparisons once from retained positional endpoint refinements. -/
def build (cell : Cell (parameter := parameter) lifted) (targets : CellEndpoints.Targets original stage)
    (bank : Vertex.Bank parameter targets.endpoint) {firstKey lastKey : Fin bank.length} (cost : Rational)
    (displacement_le : cell.primitives.displacementNorm ≤ cost)
    (target_eq : cell.target = targets.sourceTarget cost)
    (starting : OccurrenceEndpoint cell start bank firstKey)
    (finishing : OccurrenceEndpoint cell finish bank lastKey) :
    OccurrenceAdmission cell targets bank firstKey lastKey :=
  let first := starting.attached.compare starting.found.original starting.found.readings
    starting.refinement.2.val cell.startInside targets.endpoint_positive
  let last := finishing.attached.compare finishing.found.original finishing.found.readings
    finishing.refinement.2.val cell.finishInside targets.endpoint_positive
  ⟨cost, displacement_le, target_eq, starting, finishing, first, last⟩

/-- The same original source selection pays the count-derived local primitive budget. -/
theorem local_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    cell.primitives.bound ≤ targets.localBound :=
  cell.local_bound_le targets admission.cost admission.displacement_le admission.target_eq

/-- The zero primitive has that same original local budget. -/
theorem zero_local_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    cell.primitives.zero.bound ≤ targets.localBound := by
  rewrite [cell.primitives.zero_bound_eq]
  exact admission.local_le

/-- The one primitive has that same original local budget. -/
theorem one_local_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    cell.primitives.one.bound ≤ targets.localBound := by
  rewrite [cell.primitives.one_bound_eq]
  exact admission.local_le

/-- The scalar primitive has that same original local budget. -/
theorem scalar_local_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    cell.primitives.scalar.bound ≤ targets.localBound := by
  rewrite [cell.primitives.scalar_bound_eq]
  exact admission.local_le

/-- The actual zero primitive starts near its exact retained occurrence reading. -/
theorem zero_start_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.zero.value.eval 0 - bank.zeroAt firstKey) ≤ targets.endpoint := by
  have bound := admission.startComparison.zero_le
  rewrite [admission.starting.found.zero_eq] at bound
  rewrite [cell.primitives.zero_start]
  exact bound

/-- The actual zero primitive finishes near the same stored final occurrence reading. -/
theorem zero_finish_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.zero.value.eval 1 - bank.zeroAt lastKey) ≤ targets.endpoint := by
  have bound := admission.finishComparison.zero_le
  rewrite [admission.finishing.found.zero_eq] at bound
  rewrite [cell.primitives.zero_finish]
  exact bound

/-- The actual one primitive starts near its exact retained occurrence reading. -/
theorem one_start_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.one.value.eval 0 - bank.oneAt firstKey) ≤ targets.endpoint := by
  have bound := admission.startComparison.one_le
  rewrite [admission.starting.found.one_eq] at bound
  rewrite [cell.primitives.one_start]
  exact bound

/-- The actual one primitive finishes near the same stored final occurrence reading. -/
theorem one_finish_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.one.value.eval 1 - bank.oneAt lastKey) ≤ targets.endpoint := by
  have bound := admission.finishComparison.one_le
  rewrite [admission.finishing.found.one_eq] at bound
  rewrite [cell.primitives.one_finish]
  exact bound

/-- The actual scalar primitive starts near its exact retained occurrence reading. -/
theorem scalar_start_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.scalar.value.eval 0 - bank.scalarAt firstKey) ≤ targets.endpoint := by
  have bound := admission.startComparison.scalar_le
  rewrite [admission.starting.found.scalar_eq] at bound
  rewrite [cell.primitives.scalar_start]
  exact bound

/-- The actual scalar primitive finishes near the same stored final occurrence reading. -/
theorem scalar_finish_le (admission : OccurrenceAdmission cell targets bank firstKey lastKey) :
    Norm.Basic.normSq (cell.primitives.scalar.value.eval 1 - bank.scalarAt lastKey) ≤ targets.endpoint := by
  have bound := admission.finishComparison.scalar_le
  rewrite [admission.finishing.found.scalar_eq] at bound
  rewrite [cell.primitives.scalar_finish]
  exact bound

end OccurrenceAdmission

end Cell

set_option genInjectivity false in
/-- Original source-cell admissions sharing actual bounded endpoint occurrences along the same physical path.

The middle occurrence is retained by both adjacent cells. Equal physical
points at unrelated occurrences remain separate keys; actual common-root
and numerical caches belong to each original admission.
-/
inductive OccurrenceAdmissions {parameter : Canonical} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets original stage) (bank : Vertex.Bank parameter targets.endpoint) :
    {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} → Path parameter path →
      Fin bank.length → Fin bank.length → Type 1
  /-- The empty source spine has one unchanged endpoint occurrence. -/
  | nil (point : LiftedPoint 2) (key : Fin bank.length) :
      OccurrenceAdmissions targets bank (.nil point) key key
  /-- Keep the actual head admission and share its final bank occurrence with the original tail. -/
  | cons {start middle finish : LiftedPoint 2} {head : LiftedCell start middle}
      {tail : LiftedPath 2 middle finish} {source : Cell (parameter := parameter) head}
      {sources : Path parameter tail} {firstKey middleKey lastKey : Fin bank.length}
      (admission : Cell.OccurrenceAdmission source targets bank firstKey middleKey)
      (remaining : OccurrenceAdmissions targets bank sources middleKey lastKey) :
      OccurrenceAdmissions targets bank (.cons source sources) firstKey lastKey

constructive_injectivity OccurrenceAdmissions

namespace OccurrenceAdmissions

variable {parameter : Canonical} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {bank : Vertex.Bank parameter targets.endpoint}

/-- Construct the zero primitive's original numerical comparison chain using the same finite endpoint keys. -/
def zeroCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → {firstKey lastKey : Fin bank.length} →
    OccurrenceAdmissions targets bank sources firstKey lastKey →
    CellEndpoints.KeyedCells bank.zeroAt targets.localBound targets.endpoint sources.zero path firstKey lastKey
  | _, _, _, _, _, _, .nil point key => .nil point key
  | _, _, _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.zero _ (by rewrite [source.models.zero_eq]; rfl)
        (by rewrite [source.models.zero_eq]; rfl) source.primitives.zero admission.zero_local_le
        admission.zero_start_le admission.zero_finish_le remaining.zeroCells

/-- Construct the one primitive's comparison chain from those same original admissions and keys. -/
def oneCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → {firstKey lastKey : Fin bank.length} →
    OccurrenceAdmissions targets bank sources firstKey lastKey →
    CellEndpoints.KeyedCells bank.oneAt targets.localBound targets.endpoint sources.one path firstKey lastKey
  | _, _, _, _, _, _, .nil point key => .nil point key
  | _, _, _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.one _ (by rewrite [source.models.one_eq]; rfl)
        (by rewrite [source.models.one_eq]; rfl) source.primitives.one admission.one_local_le
        admission.one_start_le admission.one_finish_le remaining.oneCells

/-- Construct the scalar primitive's comparison chain without rebuilding any endpoint observation or source. -/
def scalarCells : {start finish : LiftedPoint 2} → {path : LiftedPath 2 start finish} →
    {sources : Path parameter path} → {firstKey lastKey : Fin bank.length} →
    OccurrenceAdmissions targets bank sources firstKey lastKey →
    CellEndpoints.KeyedCells bank.scalarAt targets.localBound targets.endpoint sources.scalar path firstKey lastKey
  | _, _, _, _, _, _, .nil point key => .nil point key
  | _, _, _, _, _, _, .cons (source := source) admission remaining =>
      .cons source.models.scalar _ (by rewrite [source.models.scalar_eq]; rfl)
        (by rewrite [source.models.scalar_eq]; rfl) source.primitives.scalar admission.scalar_local_le
        admission.scalar_start_le admission.scalar_finish_le remaining.scalarCells

end OccurrenceAdmissions

namespace Admissions

/-- Closed original source admissions using either the actual point-only or bounded-occurrence lookup contract.

Each branch retains its complete original admission cache. The occurrence
branch additionally retains its shared closing key and whole original bank
entry identity at the retained legacy basepoint lookup.
-/
@[expose] def Closed {parameter : Canonical} {point : LiftedPoint 2}
    {original : LiftedPath 2 point point} {stage : Nat} (targets : CellEndpoints.Targets original stage)
    (bank : Vertex.Bank parameter targets.endpoint) (base : Vertex.Bank.Found bank point)
    (sources : Path parameter original) :=
  Admissions targets bank sources ⊕
    ((key : Fin bank.length) ×
      {_admitted : OccurrenceAdmissions targets bank sources key key // bank[key.val]'key.isLt = base.entry})

end Admissions

set_option genInjectivity false in
/-- One original closed lifted representative with its actual sources and internally paid primitive endpoint banks.

Each stage retains its actual numerical precision, bank basepoint and
selected root owners. Its programme index may be earlier than that precision.
The three original row integrals telescope on this stage's closed lift;
no equality between bank samples of different stages is asserted. -/
structure Stage (parameter : Canonical) (original : ClosedLiftedPath 2) (index : Nat) where
  /-- The actual numerical precision already paid by this retained stage's original caches. -/
  precision : Nat
  /-- The original programme index is no later than that SAME actual numerical precision. -/
  index_le_precision : index ≤ precision
  /-- The computed budget of this exact original closed lifted representative at its actual precision. -/
  targets : CellEndpoints.Targets original.path precision
  /-- The retained target cache is the original count-based procedure at that SAME precision. -/
  targets_eq : targets = CellEndpoints.Targets.build original.path precision
  /-- The actual finite original bank entries and paid requests at this stage. -/
  bank : Vertex.Bank parameter targets.endpoint
  /-- The actual original bank owner at this representative's lifted basepoint. -/
  base : Vertex.Bank.Found bank original.basepoint
  /-- The literal original six-channel cell-source chain on this exact path. -/
  sources : Path parameter original.path
  /-- The complete original point-found or bounded-occurrence admissions and their actual closing bank key. -/
  admissions : Admissions.Closed targets bank base sources

namespace Stage

variable {parameter : Canonical} {original : ClosedLiftedPath 2} {index : Nat}

/-- Retain the actual precomputed stage budget, admitted sources and original bank basepoint without recomputation. -/
@[expose] def ofAdmissions (targets : CellEndpoints.Targets original.path index)
    (computed : targets = CellEndpoints.Targets.build original.path index)
    (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank original.basepoint) (sources : Path parameter original.path)
    (admissions : Admissions targets bank sources) : Stage parameter original index :=
  ⟨index, Nat.le_refl index, targets, computed, bank, base, sources, Sum.inl admissions⟩

/-- Retain original source admissions at their same actual closed bank-occurrence path.

The source path and bank remain unchanged. The original basepoint Found
is kept, and its complete entry is the same entry at the closing key.
Every primitive bound is derived from the supplied actual admissions.
-/
@[expose] def ofOccurrenceAdmissions (targets : CellEndpoints.Targets original.path index)
    (computed : targets = CellEndpoints.Targets.build original.path index)
    (bank : Vertex.Bank parameter targets.endpoint)
    (base : Vertex.Bank.Found bank original.basepoint) (sources : Path parameter original.path)
    (key : Fin bank.length) (admissions : OccurrenceAdmissions targets bank sources key key)
    (base_eq : bank[key.val]'key.isLt = base.entry) : Stage parameter original index :=
  ⟨index, Nat.le_refl index, targets, computed, bank, base, sources, Sum.inr ⟨key, ⟨admissions, base_eq⟩⟩⟩

/-- Lower only the programme index, retaining the actual precision and every original Stage cache.

The Targets, finite bank, base Found, complete source path and actual
closed-admission branch are copied unchanged. The new floor is composed
with the retained actual-precision witness; no request or observation is
retagged, rebuilt or re-executed.
-/
@[expose] def lower (stage : Stage parameter original index) (next : Nat) (before : next ≤ index) :
    Stage parameter original next :=
  ⟨stage.precision, before.trans stage.index_le_precision, stage.targets, stage.targets_eq,
    stage.bank, stage.base, stage.sources, stage.admissions⟩

/-- Lowering the programme index retains the SAME whole six-channel source path. -/
theorem lower_sources (stage : Stage parameter original index) (next : Nat) (before : next ≤ index) :
    (stage.lower next before).sources = stage.sources := rfl

/-- The actual zero primitive telescope obeys the retained actual numerical precision. -/
private theorem zero_error_at_precision_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.zero).integralSample ≤
      Geometric.Basic.quarterRadius 1 stage.precision := by
  cases stage.admissions with
  | inl admitted =>
    have estimate := stage.targets.integral_error_le admitted.zeroCells
    have cancellation : stage.bank.zero original.basepoint - stage.bank.zero original.basepoint = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.zero).integralSample - 0 =
        (PathModel.mk stage.sources.zero).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate
  | inr admitted =>
    have estimate := stage.targets.integral_keyed_error_le admitted.2.val.zeroCells
    have cancellation : stage.bank.zeroAt admitted.1 - stage.bank.zeroAt admitted.1 = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.zero).integralSample - 0 =
        (PathModel.mk stage.sources.zero).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate

/-- The actual first-row source-cell integral meets this original closed representative's geometric request. -/
theorem zero_error_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.zero).integralSample ≤
      Geometric.Basic.quarterRadius 1 index :=
  (zero_error_at_precision_le stage).trans
    (Geometric.Basic.quarterRadius_antitone
      (by decide +kernel : (0 : Rational) ≤ 1) stage.index_le_precision)

/-- The actual one primitive telescope obeys the retained actual numerical precision. -/
private theorem one_error_at_precision_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.one).integralSample ≤
      Geometric.Basic.quarterRadius 1 stage.precision := by
  cases stage.admissions with
  | inl admitted =>
    have estimate := stage.targets.integral_error_le admitted.oneCells
    have cancellation : stage.bank.one original.basepoint - stage.bank.one original.basepoint = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.one).integralSample - 0 =
        (PathModel.mk stage.sources.one).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate
  | inr admitted =>
    have estimate := stage.targets.integral_keyed_error_le admitted.2.val.oneCells
    have cancellation : stage.bank.oneAt admitted.1 - stage.bank.oneAt admitted.1 = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.one).integralSample - 0 =
        (PathModel.mk stage.sources.one).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate

/-- The actual second-row source-cell integral meets that same original closed representative's request. -/
theorem one_error_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.one).integralSample ≤
      Geometric.Basic.quarterRadius 1 index :=
  (one_error_at_precision_le stage).trans
    (Geometric.Basic.quarterRadius_antitone
      (by decide +kernel : (0 : Rational) ≤ 1) stage.index_le_precision)

/-- The actual scalar primitive telescope obeys the retained actual numerical precision. -/
private theorem scalar_error_at_precision_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.scalar).integralSample ≤
      Geometric.Basic.quarterRadius 1 stage.precision := by
  cases stage.admissions with
  | inl admitted =>
    have estimate := stage.targets.integral_error_le admitted.scalarCells
    have cancellation : stage.bank.scalar original.basepoint - stage.bank.scalar original.basepoint = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.scalar).integralSample - 0 =
        (PathModel.mk stage.sources.scalar).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate
  | inr admitted =>
    have estimate := stage.targets.integral_keyed_error_le admitted.2.val.scalarCells
    have cancellation : stage.bank.scalarAt admitted.1 - stage.bank.scalarAt admitted.1 = 0 := by ring1
    rewrite [cancellation] at estimate
    have difference : (PathModel.mk stage.sources.scalar).integralSample - 0 =
        (PathModel.mk stage.sources.scalar).integralSample := by ring1
    rewrite [difference] at estimate
    exact estimate

/-- The actual scalar source-cell integral meets that same original closed representative's request. -/
theorem scalar_error_le (stage : Stage parameter original index) :
    Norm.Basic.normSq (PathModel.mk stage.sources.scalar).integralSample ≤
      Geometric.Basic.quarterRadius 1 index :=
  (scalar_error_at_precision_le stage).trans
    (Geometric.Basic.quarterRadius_antitone
      (by decide +kernel : (0 : Rational) ≤ 1) stage.index_le_precision)

end Stage

end Purelib.Curves.Legendre.Periods.Jets.Source

end
