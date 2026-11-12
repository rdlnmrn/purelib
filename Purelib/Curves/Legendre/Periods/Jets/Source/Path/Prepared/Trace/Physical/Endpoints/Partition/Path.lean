module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Partition
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Path
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.GetD

/-! # Actual six-channel lifted paths on retained source-crop intervals

Exact interval/index transports read the original child caches. The actual
partition walk supplies the ordered lifted cells; all six original uniform
certificates are attached to that one path. Root comparisons separately
consume the actual retained Point joins and direct Query names.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open PreparedParent
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest} {row : Row}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get}
variable {compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed}
variable {index : Fin parents.covered.parents.length}
variable {firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
  (parents.covered.parents[index.val]'index.isLt).edge.baseInside}
variable {lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
  1 (of_decide_eq_true rfl)}
variable (kept : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery)
variable {cuts : List Rational}

namespace Partition

variable {kept} {partition : AxisPartition 0 1 cuts} {comparisonRequest requested : AccuracyRequest}
variable (executed : kept.Partition partition comparisonRequest requested)

/-- Read the same original interval occurrence through the whole retained walk/list equation. -/
def walkIndex (position : Fin partition.walk.edges.length) : Fin partition.intervals.length :=
  ⟨position.val, Eq.mp (congrArg (fun length => position.val < length)
    (congrArg List.length partition.walk_edges)) position.isLt⟩

/-- The retained walk-to-bank occurrence changes only the bound proof, preserving the exact natural position. -/
theorem walkIndex_val (position : Fin partition.walk.edges.length) :
    (walkIndex (partition := partition) position).val = position.val := by
  unfold walkIndex
  rfl

/-- Both original bounded reads denote the identical complete retained interval. -/
theorem walkInterval_eq (position : Fin partition.walk.edges.length) :
    (partition.walk.edges[position.val]'position.isLt) =
      (partition.intervals[(walkIndex position).val]'(walkIndex position).isLt) :=
  getElem_congr partition.walk_edges (i := position.val) (j := (walkIndex position).val) rfl position.isLt

/-- Read an actual child model through its unchanged original finite occurrence. -/
private def walkModel (channel : Fin 6) (position : Fin partition.walk.edges.length) :=
  (executed.entry (walkIndex position)).models.cell channel

/-- The stored actual child starts at the exact original walk endpoint. -/
private theorem walkModel_start (channel : Fin 6) (position : Fin partition.walk.edges.length) :
    (executed.walkModel channel position).start =
      (parents.covered.parents[index.val]'index.isLt).edge.point
        (partition.walk.edges[position.val]'position.isLt).lower :=
  ((executed.entry (walkIndex position)).models.cell_start channel).trans
    (congrArg (parents.covered.parents[index.val]'index.isLt).edge.point
      (congrArg (fun interval : Interval => interval.lower) (walkInterval_eq position).symm))

/-- The stored actual child finishes at the exact original walk endpoint. -/
private theorem walkModel_finish (channel : Fin 6) (position : Fin partition.walk.edges.length) :
    (executed.walkModel channel position).finish =
      (parents.covered.parents[index.val]'index.isLt).edge.point
        (partition.walk.edges[position.val]'position.isLt).upper :=
  ((executed.entry (walkIndex position)).models.cell_finish channel).trans
    (congrArg (parents.covered.parents[index.val]'index.isLt).edge.point
      (congrArg (fun interval : Interval => interval.upper) (walkInterval_eq position).symm))

/-- Exact interval equality transports the SAME cached child certificate, retaining its original query operation. -/
private def walkCertificate (channel : Fin 6) (position : Fin partition.walk.edges.length) :
    UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (PreparedParent.croppedCell (frame := frame)
        (parent := parents.covered.parents[index.val]'index.isLt)
        (partition.walk.edges[position.val]'position.isLt).lower
        (partition.walk.edges[position.val]'position.isLt).upper)
      (executed.walkModel channel position) :=
  Eq.mp (congrArg (fun interval : Interval =>
    UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (PreparedParent.croppedCell (frame := frame)
        (parent := parents.covered.parents[index.val]'index.isLt) interval.lower interval.upper)
      (executed.walkModel channel position)) (walkInterval_eq position).symm)
    ((executed.certificates (walkIndex position)).get channel)

/-- Both ordered model tables read the identical retained child occurrence at each original natural position. -/
private theorem walkModels_eq (channel : Fin 6) :
    List.ofFn (executed.walkModel channel) = executed.cells channel :=
  (OfFn.Basic.ofFn_congr_size (congrArg List.length partition.walk_edges)
    (executed.walkModel channel) (fun position => (executed.entry position).models.cell channel)
    (fun _first _last same => congrArg
      (fun position => (executed.entry position).models.cell channel) (Fin.ext same))).trans
      (executed.cells_eq channel).symm

/-- Construct the six whole-path certificates from the actual child caches on one supplied retained path value. -/
def certifyAt
    (actual : LiftedPath 2
      (PreparedParent.startPoint (parents.covered.parents[index.val]'index.isLt))
      (PreparedParent.finishPoint (parents.covered.parents[index.val]'index.isLt)))
    (same : actual = Crop.partitionPath (parents.covered.parents[index.val]'index.isLt) partition) :
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (executed.cells channel) actual) :=
  DependentVector.ofFn (fun channel =>
    let raw := Crop.certifyWalk (parents.covered.parents[index.val]'index.isLt)
      channel partition.walk (executed.walkModel channel) (executed.walkModel_start channel)
      (executed.walkModel_finish channel) (executed.walkCertificate channel)
    let endpoints := UniformPathCertificates.castFinish
      (Crop.last_eq (parents.covered.parents[index.val]'index.isLt))
      (UniformPathCertificates.castStart
        (Crop.first_eq (parents.covered.parents[index.val]'index.isLt)) raw)
    let endpointsAt := Eq.mpr (congrArg (fun lifted =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (List.ofFn (executed.walkModel channel)) lifted)
      (Crop.partitionPath_eq (parents.covered.parents[index.val]'index.isLt) partition)) endpoints
    let original := Eq.mp (congrArg (fun cells =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        cells (Crop.partitionPath (parents.covered.parents[index.val]'index.isLt) partition))
      (executed.walkModels_eq channel)) endpointsAt
    Eq.mpr (congrArg (fun lifted =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (executed.cells channel) lifted) same) original)

/-- The exact original interval cache, its actual lifted path and all six whole-path uniform certificates. -/
@[expose] def Lifted :=
  Σ original : {value : kept.Partition partition comparisonRequest requested // value = executed},
  Σ actual : {value : LiftedPath 2
      (PreparedParent.startPoint (parents.covered.parents[index.val]'index.isLt))
      (PreparedParent.finishPoint (parents.covered.parents[index.val]'index.isLt)) //
    value = Crop.partitionPath (parents.covered.parents[index.val]'index.isLt) partition},
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (original.val.cells channel) actual.val)

/-- Build and retain one actual common lifted path without reacquiring a Query, Point, source or observation. -/
def lift : executed.Lifted :=
  let original := executed
  let actual := Crop.partitionPath (parents.covered.parents[index.val]'index.isLt) partition
  let certificates := original.certifyAt actual rfl
  ⟨⟨original, rfl⟩, ⟨actual, rfl⟩, certificates⟩

namespace Lifted

variable {executed} (lifted : executed.Lifted)

/-- Read the same completed original parent/interval cache unchanged. -/
abbrev original := lifted.1.val

/-- Read the actual once-constructed physical subdivision with its original sheet permutations. -/
abbrev path := lifted.2.1.val

/-- Read all six actual whole-path uniform integrand certificates on that exact retained path. -/
abbrev certificates := lifted.2.2

/-- The actual path retains its complete original ordered walk construction. -/
theorem path_eq : lifted.path = Crop.partitionPath
    (parents.covered.parents[index.val]'index.isLt) partition := lifted.2.1.property

/-- The geometric construction retains the whole original interval execution cache as data. -/
theorem original_eq : lifted.original = executed := lifted.1.property

end Lifted
end Partition

namespace Cropped

variable {kept} {lower upper : Rational}
variable {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
variable {comparisonRequest requested : AccuracyRequest}
variable (acquired : kept.Cropped lower upper lowerInside upperInside comparisonRequest requested)

/-- The actual lower Point is attached to the original parent root by the SAME retained query and stationary join. -/
def firstRoot : NamedEquivalent
    ((parents.covered.parents[index.val]'index.isLt).edge.rootName lower lowerInside)
    (ownerName acquired.acquisition.2.2.samples.1.val.owner) :=
  NamedEquivalent.transport acquired.acquisition.1.endpoints.1.direct.name_eq.symm rfl
    acquired.acquisition.2.2.joins.1.val.equivalent.symm

/-- The independent upper Point is attached through its original direct Query and SAME retained target join. -/
def lastRoot : NamedEquivalent
    ((parents.covered.parents[index.val]'index.isLt).edge.rootName upper upperInside)
    (ownerName acquired.acquisition.2.2.samples.2.val.owner) :=
  NamedEquivalent.transport acquired.acquisition.1.endpoints.2.direct.name_eq.symm rfl
    acquired.acquisition.2.2.joins.2.val.equivalent

/-- Compare independent actual adjacent Points through their SAME original parent root, never from coordinates alone. -/
def adjacent
    {nextLower nextUpper : Rational}
    {nextLowerInside : 0 ≤ nextLower ∧ nextLower ≤ 1} {nextUpperInside : 0 ≤ nextUpper ∧ nextUpper ≤ 1}
    (next : kept.Cropped nextLower nextUpper nextLowerInside nextUpperInside comparisonRequest requested)
    (sameFraction : upper = nextLower) :
    NamedEquivalent (ownerName acquired.acquisition.2.2.samples.2.val.owner)
      (ownerName next.acquisition.2.2.samples.1.val.owner) :=
  (NamedEquivalent.transport rfl
    ((parents.covered.parents[index.val]'index.isLt).edge.rootName_eq sameFraction)
    acquired.lastRoot.symm).trans next.firstRoot

end Cropped

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

end
