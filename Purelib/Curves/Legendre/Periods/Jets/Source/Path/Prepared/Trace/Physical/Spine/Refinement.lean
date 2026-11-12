module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Observations
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Partition.Path
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Approximation.Rational.Budget.Aggregate

/-! # Actual six-channel refinements of the original full physical spine

The whole old Compared cache and original split product remain actual data.
Existing segment readers select each old observation/comparison once. Each
segment retains its actual acquired interval model caches and common lifted
path with six genuine uniform certificates. Ordered products and the original
ClearPath join those actual paths in original segment, parent and interval
order. Repeated and stationary slots remain present.

The signed source root chain retains the actual source and paid finish
Owners independently of labelled geometric endpoints. Neither a geometric
root return, physical integral comparison nor canonical sewing is inferred
from the displayed path or its exact polynomial sample sums.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Sources

/-- The original source-segment occurrences index their actual retained lifted paths and exact endpoint labels. -/
@[expose] def SegmentPaths
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest)
    {start finish : Canonical} (path : ClearPath (Paths.polynomial parameter) ambient start finish)
    (within : path.WithinAmbient) (owner : Owner ((Paths.polynomial parameter).eval start))
    (retained : Acquisition.Spine width path within owner)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) :=
  (index : Fin (parentWords width path within owner retained sources).length) →
    LiftedPath 2 ⟨(segmentAt width path within owner retained sources index).endpoints.1, sheet⟩
      ⟨(segmentAt width path within owner retained sources index).endpoints.2, sheet⟩

/-- Join the actual stored Segment refinements on the original physical ClearPath and literal source tails. -/
def segmentPath
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    SegmentPaths (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained sources →
    LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩
  | _, _, .nil point, _, _, _, _, _ => .nil ⟨point, sheet⟩
  | _, _, .cons _ tail, within, _, retained, sources, paths =>
      (paths ⟨0, Nat.zero_lt_succ _⟩).append
        (segmentPath width tail within.tail retained.1.traced.finishOwner retained.2
        sources.2.2 (fun index => paths index.succ))
termination_by structural _ _ path _ _ _ _ _ => path

/-- The six actual Segment certificates concatenate on the same retained physical path without replay. -/
def certifySegments
    (width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
      AccuracyRequest) (channel : Fin 6) :
    {start finish : Canonical} → (path : ClearPath (Paths.polynomial parameter) ambient start finish) →
    (within : path.WithinAmbient) → (owner : Owner ((Paths.polynomial parameter).eval start)) →
    (retained : Acquisition.Spine width path within owner) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained) →
    (paths : SegmentPaths (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width path within owner retained sources) →
    (cells : Fin (parentWords width path within owner retained sources).length → List CellModel) →
    (∀ index, UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (cells index) (paths index)) →
    UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (List.ofFn cells).flatten (segmentPath width path within owner retained sources paths)
  | _, _, .nil point, _, _, _, _, _, _, _ => .nil ⟨point, sheet⟩
  | _, _, .cons head tail, within, owner, retained, sources, paths, cells, valid =>
      Eq.mpr (congrArg (fun models : List CellModel =>
        UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
          models (segmentPath width (.cons head tail) within owner retained sources paths))
        (congrArg List.flatten (OfFn.Basic.ofFn_succ (function := cells))))
        (UniformPathCertificates.append (paths ⟨0, Nat.zero_lt_succ _⟩) (valid ⟨0, Nat.zero_lt_succ _⟩)
        (certifySegments width channel tail within.tail retained.1.traced.finishOwner retained.2 sources.2.2
          (fun index => paths index.succ) (fun index => cells index.succ) (fun index => valid index.succ)))
termination_by structural _ _ path _ _ _ _ _ _ _ => path

end Sources

namespace Compared

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start finish : Canonical} {physicalPath : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {within : physicalPath.WithinAmbient} {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {row : Row} {retained : Acquisition width physicalPath within owner}
variable {observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
variable {views : Acquisition.Observations retained observed}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width physicalPath within owner retained.spine}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {gridAmbient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid (Fibre.frameCurve frame).polynomial gridAmbient}
variable (axes : PrimitiveAxes grid)
variable (compared : Compared row retained views sources allocation)

/-- Actual original splitting spines at each retained physical Segment occurrence, stored as an ordered product. -/
@[expose] def Splits :=
  DependentProduct (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
    (fun index => PrimitiveSplits axes
      (Sources.segmentAt width physicalPath within owner retained.spine
        compared.prepared index).parents.covered.parents)

namespace Splits

/-- Construct each original Segment's axis splitting once before any crop acquisition or new observation. -/
def build : Splits axes compared :=
  DependentProduct.ofFn (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
    (fun index => PrimitiveSplits.build axes
      (Sources.segmentAt width physicalPath within owner retained.spine
        compared.prepared index).parents.covered.parents)

/-- Count the actual cached split intervals before any refined crop or primitive observation is acquired. -/
@[expose] def intervalCount (splits : Splits axes compared) : Nat :=
  DependentProduct.sum
    (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
    (fun index (actual : PrimitiveSplits axes
      (Sources.segmentAt width physicalPath within owner retained.spine compared.prepared
        index).parents.covered.parents) => actual.count) splits

/-- The original finite parent word supplies the exact number of parent-boundary handoffs. -/
@[expose] def parentCount : Nat :=
  (Sources.parentWords width physicalPath within owner retained.spine compared.prepared).flatten.length

/-- The original retained split and parent counts determine the planned whole-Spine sewing handoff count.

Each actual interval contributes one opening handoff, each parent one
additional terminal handoff, and the original parent chain contributes
one opening per parent and one final handoff. Empty Segment words add no
parent or interval, while the original final comparison remains counted.
-/
@[expose] def handoffCount (splits : Splits axes compared) : Nat :=
  intervalCount axes compared splits + 2 * parentCount compared + 1

/-- Choose the child request before acquiring any new observations, reserving this exact finite sewing budget.

The original observer allocates localRequest child 3. Inverting that
existing allocation makes its actual local tolerance the aggregate share
for the supplied whole-Spine target and planned handoff count. Existing
endpoint requests, model stages and model remainders remain unchanged.
-/
def childRequest (splits : Splits axes compared) (target : AccuracyRequest) : AccuracyRequest :=
  OwnerPath.Primitive.requestFor
    (OwnerPath.Primitive.localRequest target (handoffCount axes compared splits)) 3

/-- The actual original three-link observer request recovers the preselected whole-Spine local sewing share. -/
theorem childRequest_local (splits : Splits axes compared) (target : AccuracyRequest) :
    OwnerPath.Primitive.localRequest (childRequest axes compared splits target) 3 =
      OwnerPath.Primitive.localRequest target (handoffCount axes compared splits) :=
  OwnerPath.Primitive.localRequest_requestFor
    (OwnerPath.Primitive.localRequest target (handoffCount axes compared splits)) 3

/-- The planned finite handoff count is paid by the child request chosen before observations.

This establishes the scalar allocation itself. Applying it to an executed
sewing additionally requires the exact handoff-count readback; it pays no
old endpoint, model-remainder or canonical integral error.
-/
theorem childRequest_payment (splits : Splits axes compared) (target : AccuracyRequest) :
    ((handoffCount axes compared splits : Nat) : Rational) *
      (((handoffCount axes compared splits : Nat) : Rational) *
        (OwnerPath.Primitive.localRequest (childRequest axes compared splits target) 3).tolerance) <
          target.tolerance := by
  have sameAllowance := congrArg AccuracyRequest.tolerance (childRequest_local axes compared splits target)
  exact Eq.mpr (congrArg (fun allowance : Rational =>
      ((handoffCount axes compared splits : Nat) : Rational) *
        (((handoffCount axes compared splits : Nat) : Rational) * allowance) < target.tolerance) sameAllowance)
    (Aggregate.count_mul_perTerm_lt target.positive (handoffCount axes compared splits))

/-- Allocate one additional original handoff before acquisition for a genuine signed closing comparison.

This request reserves H + 1 comparisons. The open childRequest reserves
only H and supplies no closing payment. Both factories keep the original
three-link local observer allocation and never retag an old observation.
-/
def closingChildRequest (splits : Splits axes compared) (target : AccuracyRequest) : AccuracyRequest :=
  OwnerPath.Primitive.requestFor
    (OwnerPath.Primitive.localRequest target (handoffCount axes compared splits + 1)) 3

/-- The actual three-link request recovers the distinct H + 1 allowance selected for closing. -/
theorem closingChildRequest_local (splits : Splits axes compared) (target : AccuracyRequest) :
    OwnerPath.Primitive.localRequest (closingChildRequest axes compared splits target) 3 =
      OwnerPath.Primitive.localRequest target (handoffCount axes compared splits + 1) :=
  OwnerPath.Primitive.localRequest_requestFor
    (OwnerPath.Primitive.localRequest target (handoffCount axes compared splits + 1)) 3

/-- The separately selected closing request pays its H + 1 aggregate allowance before observations exist. -/
theorem closingChildRequest_payment (splits : Splits axes compared) (target : AccuracyRequest) :
    ((handoffCount axes compared splits + 1 : Nat) : Rational) *
      (((handoffCount axes compared splits + 1 : Nat) : Rational) *
        (OwnerPath.Primitive.localRequest (closingChildRequest axes compared splits target) 3).tolerance) <
          target.tolerance := by
  have sameAllowance := congrArg AccuracyRequest.tolerance
    (closingChildRequest_local axes compared splits target)
  exact Eq.mpr (congrArg (fun allowance : Rational =>
      ((handoffCount axes compared splits + 1 : Nat) : Rational) *
        (((handoffCount axes compared splits + 1 : Nat) : Rational) * allowance) < target.tolerance) sameAllowance)
    (Aggregate.count_mul_perTerm_lt target.positive (handoffCount axes compared splits + 1))

end Splits

namespace Refinement

/-- The original paid acquisition, old comparison and splitting product share their exact input boundary. -/
@[expose] def Input (splits : Splits axes compared) :=
  {value : Acquisition width physicalPath within owner ×
      (Σ old : Compared row retained views sources allocation, Splits axes old) //
    value = (retained, ⟨compared, splits⟩)}

/-- One SAME old Segment observation/comparison, its real crop acquisition and its actual six-channel lifted path. -/
@[expose] def Segment (splits : Splits axes compared) (comparisonRequest requested : AccuracyRequest)
    (index : Fin (Sources.parentWords width physicalPath within owner retained.spine compared.prepared).length) :=
  Σ old : {value : Sources.SegmentObservation (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) (width := width) row allocation
      (Sources.segmentAt width physicalPath within owner retained.spine compared.prepared index) //
    value = compared.segmentAt index},
  Σ acquired : Physical.Comparison.Partition old.val.comparison
      (DependentProduct.get (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
        splits index)
      comparisonRequest requested,
    acquired.Lifted

namespace Segment

variable {axes compared} {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
variable {index : Fin (Sources.parentWords width physicalPath within owner retained.spine compared.prepared).length}
variable (stored : Segment axes compared splits comparisonRequest requested index)

/-- Read the exact retained original complete Segment observation and its already computed comparison. -/
abbrev old := stored.1.val

/-- Read the same actual original-parent/interval crop execution, including every original Query, Point and join. -/
abbrev crop := stored.2.1

/-- Read the actual stored common Segment path and all six whole-path uniform integrand certificates. -/
abbrev lifted := stored.2.2

/-- The complete original Segment observation/comparison is the SAME existing ordered spine reader result. -/
theorem old_eq : stored.old = compared.segmentAt index := stored.1.property

end Segment

/-- Read one exact old Segment pair and build only its requested actual crops and their certified refinement. -/
private def acquireSegment (splits : Splits axes compared) (comparisonRequest requested : AccuracyRequest)
    (index : Fin (Sources.parentWords width physicalPath within owner retained.spine compared.prepared).length) :
    Segment axes compared splits comparisonRequest requested index :=
  let old := compared.segmentAt index
  let partition := DependentProduct.get
    (Sources.parentWords width physicalPath within owner retained.spine compared.prepared) splits index
  let acquired := Physical.Comparison.Partition.build old.comparison partition comparisonRequest requested
  let lifted := acquired.lift
  ⟨⟨old, rfl⟩, acquired, lifted⟩

/-- Store one completed Segment refinement at every original physical occurrence, with exact source indices. -/
@[expose] def Segments (splits : Splits axes compared) (comparisonRequest requested : AccuracyRequest) :=
  DependentProduct (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
    (Segment axes compared splits comparisonRequest requested)

namespace Segments

/-- Read the actual original ordered Segment execution without selecting or acquiring it again. -/
abbrev entry {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
    (segments : Segments axes compared splits comparisonRequest requested)
    (index : Fin (Sources.parentWords width physicalPath within owner retained.spine compared.prepared).length) :=
  DependentProduct.get (Sources.parentWords width physicalPath within owner retained.spine compared.prepared)
    segments index

/-- Read the actual cached common lifted path at each original Segment occurrence. -/
def paths {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
    (segments : Segments axes compared splits comparisonRequest requested) :
    Sources.SegmentPaths (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := targets) width physicalPath within owner retained.spine compared.prepared :=
  fun index => (entry axes compared segments index).lifted.path

/-- Read one original differential's actual refined model lists in literal Segment, parent and interval order. -/
def cells {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
    (segments : Segments axes compared splits comparisonRequest requested) (channel : Fin 6) : List CellModel :=
  (List.ofFn (fun index => (entry axes compared segments index).lifted.original.cells channel)).flatten

/-- Attach all six actual model-list certificates to one supplied retained full-spine path value. -/
def certifyAt {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
    (segments : Segments axes compared splits comparisonRequest requested)
    (actual : LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩)
    (same : actual = Sources.segmentPath width physicalPath within owner retained.spine compared.prepared
      (paths axes compared segments)) :
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (cells axes compared segments channel) actual) :=
  DependentVector.ofFn (fun channel =>
    let certified := Sources.certifySegments width channel physicalPath within owner retained.spine compared.prepared
      (paths axes compared segments)
      (fun index => (entry axes compared segments index).lifted.original.cells channel)
      (fun index => (entry axes compared segments index).lifted.certificates.get channel)
    Eq.mpr (congrArg (fun lifted =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (cells axes compared segments channel) lifted) same) certified)

end Segments
end Refinement

/-- Actual old/splitting caches, root transport, retained child paths and six whole-path uniform certificates.

The original root names belong to the actual retained source and paid finish
Owners. They remain distinct indices even when the displayed labelled path
has equal endpoint coordinates. Every old View, stationary comparison,
selected source pair and newly executed crop remains in the stored inputs
or the ordered Segment caches.
-/
@[expose] def Refinement (splits : Splits axes compared) (comparisonRequest requested : AccuracyRequest) :=
  Σ original : Refinement.Input axes compared splits,
  Σ _roots : {value : RootChain
      (Sources.assemble width physicalPath within owner retained.spine original.val.2.1.prepared).geometry.parents
      (ownerRootName owner.parameterNonzero owner)
      (ownerRootName retained.covered.traced.finishOwner.parameterNonzero retained.covered.traced.finishOwner) //
    value = Sources.acquiredRootChain width physicalPath within owner retained original.val.2.1.prepared},
  Σ segments : Refinement.Segments axes original.val.2.1 original.val.2.2 comparisonRequest requested,
  Σ actual : {value : LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩ //
    value = Sources.segmentPath width physicalPath within owner retained.spine original.val.2.1.prepared
      (Refinement.Segments.paths axes original.val.2.1 segments)},
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (Refinement.Segments.cells axes original.val.2.1 segments channel) actual.val)

namespace Refinement

/-- Package abstract retained root, Segment, path and certificate caches without reducing acquisition factories. -/
private def pack {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
    (original : Input axes compared splits)
    (roots : RootChain
      (Sources.assemble width physicalPath within owner retained.spine original.val.2.1.prepared).geometry.parents
      (ownerRootName owner.parameterNonzero owner)
      (ownerRootName retained.covered.traced.finishOwner.parameterNonzero retained.covered.traced.finishOwner))
    (rootEq : roots = Sources.acquiredRootChain width physicalPath within owner retained original.val.2.1.prepared)
    (segments : Segments axes original.val.2.1 original.val.2.2 comparisonRequest requested)
    (actual : LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩)
    (pathEq : actual = Sources.segmentPath width physicalPath within owner retained.spine original.val.2.1.prepared
      (Segments.paths axes original.val.2.1 segments))
    (certificates : DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (Segments.cells axes original.val.2.1 segments channel) actual)) :
    Refinement axes compared splits comparisonRequest requested :=
  ⟨original, ⟨roots, rootEq⟩, segments, ⟨actual, pathEq⟩, certificates⟩

/-- Execute the stored Segment selections and real crop acquisitions once, retaining their actual common path. -/
def build (splits : Splits axes compared) (comparisonRequest requested : AccuracyRequest) :
    Refinement axes compared splits comparisonRequest requested :=
  let original : Acquisition width physicalPath within owner ×
      (Σ old : Compared row retained views sources allocation, Splits axes old) :=
    (retained, ⟨compared, splits⟩)
  let roots := Sources.acquiredRootChain width physicalPath within owner retained original.2.1.prepared
  let segments : Segments axes original.2.1 original.2.2 comparisonRequest requested :=
    DependentProduct.ofFn (Sources.parentWords width physicalPath within owner retained.spine original.2.1.prepared)
      (acquireSegment axes original.2.1 original.2.2 comparisonRequest requested)
  let actual := Sources.segmentPath width physicalPath within owner retained.spine original.2.1.prepared
    (Segments.paths axes original.2.1 segments)
  let certificates := Segments.certifyAt axes original.2.1 segments actual rfl
  pack axes compared ⟨original, rfl⟩ roots rfl segments actual rfl certificates

variable {axes compared} {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
variable (refined : Refinement axes compared splits comparisonRequest requested)

/-- Read the exact whole original paid physical acquisition, retaining its actual endpoint Owner and closing lineage. -/
abbrev paid := refined.1.val.1

/-- Read the identical whole original Compared cache, including every old shared Vertex and stationary comparison. -/
abbrev original := refined.1.val.2.1

/-- Read the same supplied original ordered splitting product without a second partition construction. -/
abbrev splitting := refined.1.val.2.2

/-- Read the cached signed original source root chain at its unchanged source and paid finish Owner names. -/
abbrev roots := refined.2.1.val

/-- Read the actual ordered Segment execution caches and their complete lifted-path/certificate values. -/
abbrev segments := refined.2.2.1

/-- Read the genuine common full-spine lifted path assembled from those same retained Segment paths. -/
abbrev path := refined.2.2.2.1.val

/-- Read all six genuine UniformPathCertificates on the identical actual full-spine path value. -/
abbrev certificates := refined.2.2.2.2

/-- The paid acquisition, old comparison and supplied split product retain their complete joint identity. -/
theorem inputs_eq :
    (refined.paid, (⟨refined.original, refined.splitting⟩ :
      Σ old : Compared row retained views sources allocation, Splits axes old)) =
        (retained, ⟨compared, splits⟩) := refined.1.property

/-- The whole actual physical acquisition retains its original input identity. -/
theorem paid_eq : refined.paid = retained := congrArg Prod.fst refined.1.property

/-- The whole supplied old comparison retains its exact original identity and original observations. -/
theorem original_eq : refined.original = compared :=
  congrArg (fun value => value.2.1) refined.1.property

/-- The original actual source root chain has its complete retained original construction. -/
theorem roots_eq : refined.roots =
    Sources.acquiredRootChain width physicalPath within owner retained refined.original.prepared := refined.2.1.property

/-- The actual common lifted path has the original ordered Segment-path factory. -/
theorem path_eq : refined.path = Sources.segmentPath width physicalPath within owner retained.spine
    refined.original.prepared (Segments.paths axes refined.original refined.segments) := refined.2.2.2.1.property

/-- Read the six exact differential model lists from the same retained Segment executions. -/
abbrev cells (channel : Fin 6) := Segments.cells axes refined.original refined.segments channel

/-- Every actual refined differential sample equals the unchanged original full-spine six-program source sample. -/
theorem integralSample_eq_original (channel : Fin 6) :
    (PathModel.mk (refined.cells channel)).integralSample =
      (PathModel.mk ((PreparedParents.sources
        (Sources.assemble width physicalPath within owner retained.spine refined.original.prepared).covered
        (Sources.assemble width physicalPath within owner retained.spine refined.original.prepared).prepared
        (Sources.assemble width physicalPath within owner retained.spine
          refined.original.prepared).geometry.chain).cells channel)).integralSample := by
  let segmentCells := fun index : Fin
      (Sources.parentWords width physicalPath within owner retained.spine refined.original.prepared).length =>
    let selected := Sources.segmentAt width physicalPath within owner retained.spine refined.original.prepared index
    (PreparedParents.sources selected.parents.coveredParents selected.prepared selected.parents.covered.chain).cells
      channel
  have actual := PathModel.integralSample_flatten_ofFn
    (fun index => (Segments.entry axes refined.original refined.segments index).lifted.original.cells channel)
  have entries := Algebra.FiniteSum.Fin.sumFin_congr
    (fun index =>
      (Segments.entry axes refined.original refined.segments index).lifted.original.integralSample_eq_original channel)
  have original := PathModel.integralSample_flatten_ofFn segmentCells
  have lists := (Sources.assemble_cells width channel physicalPath within owner retained.spine
    refined.original.prepared).trans
      (congrArg List.flatten (Sources.cellWords_eq_ofFn width channel physicalPath within owner retained.spine
        refined.original.prepared))
  exact actual.trans (entries.trans (original.symm.trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample) lists).symm))

/-- Read the separate actual row-integrand cells without treating them as one of the six differential channels. -/
def relationCells : List CellModel :=
  (List.ofFn (fun index =>
    (Segments.entry axes refined.original refined.segments index).lifted.original.relationCells)).flatten

/-- Sum every actual joined Point-owned row increment, with independently acquired junctions left uncancelled. -/
def rowSample : Canonical :=
  sumFin (fun index => (Segments.entry axes refined.original refined.segments index).lifted.original.rowSample)

/-- The whole row sample is the original ordered sum of its same retained Segment executions. -/
theorem rowSample_eq : refined.rowSample = sumFin (fun index =>
    (Segments.entry axes refined.original refined.segments index).lifted.original.rowSample) := by
  unfold rowSample
  rfl

/-- The finite row budget retains the real original Segment counts and all inner parent/interval payments. -/
def rowBound : Rational :=
  ((Sources.parentWords width physicalPath within owner retained.spine refined.original.prepared).length : Rational) *
    sumFin (fun index => (Segments.entry axes refined.original refined.segments index).lifted.original.rowBound)

/-- The actual complete row sample pays its distinct ordered row-cell list by internally derived finite bounds. -/
theorem row_integral_le : Norm.Basic.normSq
    (refined.rowSample - (PathModel.mk refined.relationCells).integralSample) ≤ refined.rowBound := by
  unfold relationCells
  rewrite [PathModel.integralSample_flatten_ofFn]
  exact Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin _ _ _
    (fun index => (Segments.entry axes refined.original refined.segments index).lifted.original.row_integral_le)

end Refinement
end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

end
