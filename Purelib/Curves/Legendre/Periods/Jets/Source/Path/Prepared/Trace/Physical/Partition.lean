module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Partition
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Occurrence
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Data.List.Flatten
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed

/-! # Executed crops on the ordered original physical source word

The original comparison and actual splitting spine remain runtime data.
Each original parent retains its two Queries and whole EndpointPoints;
every retained interval then executes the original selector and crop once.
The six differential lists preserve the original parent and interval order,
including repetitions and stationary physical segments. Their exact sums
attach to the unchanged original six-source programmes. Row increment
bounds do not assume cancellation of independently observed junctions.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
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
variable {gridAmbient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid (Fibre.frameCurve frame).polynomial gridAmbient}
variable {axes : PrimitiveAxes grid}

namespace Partition

/-- One exact original parent occurrence retains both Queries, its old source cache and every executed child. -/
@[expose] def Entry
    (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row retained parents prepared allocation observed)
    (splits : PrimitiveSplits axes parents.covered.parents)
    (comparisonRequest requested : AccuracyRequest) (index : Fin parents.covered.parents.length) :=
  Σ firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
      (parents.covered.parents[index.val]'index.isLt).edge.baseInside,
  Σ lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
      1 (of_decide_eq_true rfl),
  Σ endpoints : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery,
  Σ partition : {value : AxisPartition 0 1 (axes.parameters (parents.covered.parents[index.val]'index.isLt)) //
      value = splits.partitionAt index},
    endpoints.Partition partition.val comparisonRequest requested

/-- Execute one original parent and its actual cached interval partition without re-preparing any source. -/
private def acquireEntry
    (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row retained parents prepared allocation observed)
    (splits : PrimitiveSplits axes parents.covered.parents)
    (comparisonRequest requested : AccuracyRequest) (index : Fin parents.covered.parents.length) :
    Entry compared splits comparisonRequest requested index :=
  let first := PreparedEdge.Query.build (parents.covered.parents[index.val]'index.isLt).edge 0
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside
  let last := PreparedEdge.Query.build (parents.covered.parents[index.val]'index.isLt).edge 1
    (of_decide_eq_true rfl)
  let endpoints := compareSourcePoints compared index first last
  let partition := splits.partitionAt index
  let children := EndpointPoints.Partition.build endpoints partition comparisonRequest requested
  ⟨first, last, endpoints, ⟨partition, rfl⟩, children⟩

end Partition

/-- The actual comparison, original splitting spine and all completed crops on that exact ordered source word. -/
@[expose] def Partition
    (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row retained parents prepared allocation observed)
    (splits : PrimitiveSplits axes parents.covered.parents) (comparisonRequest requested : AccuracyRequest) :=
  Σ original : {values : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row retained parents prepared allocation observed ×
        PrimitiveSplits axes parents.covered.parents // values = (compared, splits)},
    DependentProduct parents.covered.parents
      (Partition.Entry original.val.1 original.val.2 comparisonRequest requested)

namespace Partition

/-- Acquire every requested original interval in original parent order, preserving all old source and closure caches. -/
def build
    (compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) row retained parents prepared allocation observed)
    (splits : PrimitiveSplits axes parents.covered.parents) (comparisonRequest requested : AccuracyRequest) :
    Partition compared splits comparisonRequest requested :=
  let original := (compared, splits)
  let entries := DependentProduct.ofFn parents.covered.parents
    (Partition.acquireEntry original.1 original.2 comparisonRequest requested)
  ⟨⟨original, rfl⟩, entries⟩

variable {compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed}
variable {splits : PrimitiveSplits axes parents.covered.parents} {comparisonRequest requested : AccuracyRequest}
variable (executed : Partition compared splits comparisonRequest requested)

/-- Read the exact retained original physical comparison and actual source-word splitting spine. -/
abbrev original := executed.1.val

/-- Read one complete original parent execution by its literal bounded occurrence. -/
abbrev entry (index : Fin parents.covered.parents.length) :=
  DependentProduct.get parents.covered.parents executed.2 index

/-- Read the original endpoint comparison cache, including its original whole source pair. -/
abbrev endpoints (index : Fin parents.covered.parents.length) := (executed.entry index).2.2.1

/-- Read the exact stored original partition and its factory equation on the original splitting spine. -/
abbrev partition (index : Fin parents.covered.parents.length) := (executed.entry index).2.2.2.1

/-- The actual retained parent partition has the exact original supplied splitting count at the same occurrence. -/
theorem partition_count (index : Fin parents.covered.parents.length) :
    (executed.partition index).val.intervals.length = (splits.partitionAt index).intervals.length :=
  (congrArg (fun actual : AxisPartition 0 1 (axes.parameters (parents.covered.parents[index.val]'index.isLt)) =>
      actual.intervals.length) (executed.partition index).property).trans
    (congrArg (fun actual : PrimitiveSplits axes parents.covered.parents =>
      (actual.partitionAt index).intervals.length) (congrArg Prod.snd executed.1.property))

/-- Read the actual completed interval product, preserving its original literal child tail. -/
abbrev children (index : Fin parents.covered.parents.length) := (executed.entry index).2.2.2.2

/-- Read the six cached child certificates at one original parent and interval occurrence, without replay. -/
abbrev certificates (index : Fin parents.covered.parents.length)
    (position : Fin (executed.partition index).val.intervals.length) :=
  (executed.children index).certificates position

/-- Flatten the actual six differential model lists in original parent and interval order, with no occurrence filter. -/
def cells (channel : Fin 6) : List Cell.Basic.CellModel :=
  (List.ofFn (fun index => (executed.children index).cells channel)).flatten

/-- The complete differential list is the literal original parent/interval flattening of its stored child caches. -/
theorem cells_eq (channel : Fin 6) : executed.cells channel =
    (List.ofFn (fun index => (executed.children index).cells channel)).flatten := by
  unfold cells
  rfl

/-- Flatten only the distinct row-relation model lists in the identical original occurrence order. -/
def relationCells : List Cell.Basic.CellModel :=
  (List.ofFn (fun index => (executed.children index).relationCells)).flatten

/-- Whole retained source-pair identities identify the original scalar source integral at the same parent occurrence. -/
private theorem endpoint_integralSample_eq
    {index : Fin parents.covered.parents.length}
    {firstQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge 0
      (parents.covered.parents[index.val]'index.isLt).edge.baseInside}
    {lastQuery : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge
      1 (of_decide_eq_true rfl)}
    (kept : EndpointPoints (frame := frame) (basis := basis) executed.original.1 index firstQuery lastQuery)
    (channel : Fin 6) :
    (kept.entry.preparation.cell.models.cell channel).integralSample =
      ((prepared.entry index).preparation.cell.models.cell channel).integralSample := by
  have entry := congrArg
    (fun entry : PreparedParent (kept.pair.1.entry index).val count floor
        (kept.pair.1.entry index).property targets =>
      (entry.preparation.cell.models.cell channel).integralSample) kept.entry_eq
  have original := congrArg
    (fun pair : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
        (targets := targets) parents.covered.parents =>
      ((pair.2.entry index).preparation.cell.models.cell channel).integralSample)
    (kept.pair_eq.trans executed.original.1.sourcePair_eq)
  exact entry.trans original

/-- The six ordered crop sums equal the original six-source samples at unchanged parent occurrences. -/
theorem integralSample_eq_sumFin (channel : Fin 6) :
    (PathModel.mk (executed.cells channel)).integralSample =
      sumFin (fun index : Fin parents.covered.parents.length =>
        ((prepared.entry index).preparation.cell.models.cell channel).integralSample) := by
  unfold cells
  rewrite [PathModel.integralSample_flatten_ofFn]
  exact Algebra.FiniteSum.Fin.sumFin_congr (fun index =>
    ((executed.children index).integralSample_eq channel).trans
      (endpoint_integralSample_eq executed (executed.endpoints index) channel))

/-- Each original six-program source list has exactly its corresponding ordered actual crop integral sum. -/
theorem integralSample_eq_original (channel : Fin 6) :
    (PathModel.mk (executed.cells channel)).integralSample =
      (PathModel.mk
        ((PreparedParents.sources parents.coveredParents prepared
          parents.covered.chain).cells channel)).integralSample :=
  (executed.integralSample_eq_sumFin channel).trans
    (PreparedParents.integralSample_eq_sumFin parents.coveredParents prepared parents.covered.chain channel).symm

/-- Sum the actual Point-owned row increments without assuming any junction cancellation or primitive normalization. -/
def rowSample : Canonical := sumFin (fun index => (executed.children index).rowSample)

/-- The whole row sample is the original ordered sum of its same retained parent interval banks. -/
theorem rowSample_eq : executed.rowSample = sumFin (fun index => (executed.children index).rowSample) := by
  unfold rowSample
  rfl

/-- The explicit finite row bound composes the retained original parent and interval counts and payments. -/
def rowBound : Rational :=
  (parents.covered.parents.length : Rational) * sumFin (fun index => (executed.children index).rowBound)

/-- Actual row increments pay the actual ordered row-integrand list through their internally derived finite bounds. -/
theorem row_integral_le : Norm.Basic.normSq
    (executed.rowSample - (PathModel.mk executed.relationCells).integralSample) ≤
      executed.rowBound := by
  unfold relationCells
  rewrite [PathModel.integralSample_flatten_ofFn]
  exact Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin _ _ _
    (fun index => (executed.children index).row_integral_le)

end Partition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

end
