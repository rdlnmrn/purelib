module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Crop
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Data.List.DependentProduct
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Tactic.Ring

/-! # Actual source crops in original partition order

Every retained interval executes the original physical selector and the
same crop acquisition once. The original ordered product stores complete
executions and all six child integrand certificates. Exact polynomial
integration recovers each original differential sample, while row and
new endpoint-observation bounds remain separate finite payments.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
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
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest} {row : Row}
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

/-- Complete selected crop executions and six certificate caches at every original partition occurrence. -/
@[expose] def Partition (partition : AxisPartition 0 1 cuts) (comparisonRequest requested : AccuracyRequest) :=
  DependentProduct partition.intervals (fun position =>
    let interval := partition.intervals[position.val]'position.isLt
    let bounded := partition.interval_bounds (List.getElem_mem position.isLt)
    Σ acquired : kept.Cropped interval.lower interval.upper
        ⟨bounded.1, interval.ordered.le.trans bounded.2⟩
        ⟨bounded.1.trans interval.ordered.le, bounded.2⟩ comparisonRequest requested,
      {certificates : _ // certificates = acquired.certificates})

namespace Partition

/-- Execute the selected source crop once per original retained interval, storing each whole cache in order. -/
def build (partition : AxisPartition 0 1 cuts) (comparisonRequest requested : AccuracyRequest) :
    kept.Partition partition comparisonRequest requested :=
  DependentProduct.ofFn partition.intervals (fun position =>
    let interval := partition.intervals[position.val]'position.isLt
    let bounded := partition.interval_bounds (List.getElem_mem position.isLt)
    let acquired := kept.acquireCrop interval.lower interval.upper
      ⟨bounded.1, interval.ordered.le.trans bounded.2⟩
      ⟨bounded.1.trans interval.ordered.le, bounded.2⟩ interval.ordered.le comparisonRequest requested
    let certificates := acquired.certificates
    ⟨acquired, ⟨certificates, rfl⟩⟩)

variable {kept} {partition : AxisPartition 0 1 cuts} {comparisonRequest requested : AccuracyRequest}
variable (executed : kept.Partition partition comparisonRequest requested)

/-- Read the same complete retained interval acquisition, with its original selector and deferred closure. -/
abbrev entry (position : Fin partition.intervals.length) :=
  (DependentProduct.get partition.intervals executed position).1

/-- Read the six actual cached uniform integrand certificates without constructing another source query family. -/
abbrev certificates (position : Fin partition.intervals.length) :=
  (DependentProduct.get partition.intervals executed position).2.val

/-- Each six-channel certificate cache is the certificate family of its identical completed acquisition. -/
theorem certificates_eq (position : Fin partition.intervals.length) :
    executed.certificates position = (executed.entry position).certificates :=
  (DependentProduct.get partition.intervals executed position).2.property

/-- Materialize one differential's actual child cells in original interval order, keeping every physical occurrence. -/
def cells (channel : Fin 6) : List Cell.Basic.CellModel :=
  List.ofFn (fun position => ((executed.entry position).models.cell channel))

/-- The whole displayed child list reads the identical retained interval model caches in original order. -/
theorem cells_eq (channel : Fin 6) : executed.cells channel =
    List.ofFn (fun position => (executed.entry position).models.cell channel) := by
  unfold cells
  rfl

/-- Materialize the independent row-relation cells in the same original order. -/
def relationCells : List Cell.Basic.CellModel :=
  List.ofFn (fun position => (executed.entry position).models.relation)

/-- Actual interval integrals telescope along the original finite covering walk. -/
private theorem walk_integralSample (cell : Cell.Basic.CellModel) {intervals : List Interval} :
    {first last : Rational} → (walk : AxisWalks.IncreasingWalk intervals first last) →
      Norm.Sum.Basic.gaussianSum (walk.edges.map (fun interval =>
        cell.displacement * Integral.definiteIntegral cell.polynomial
          (Cast.Path.ofCoordinate interval.lower) (Cast.Path.ofCoordinate interval.upper))) =
        cell.displacement * Integral.definiteIntegral cell.polynomial
          (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)
  | _, _, .nil _ => by
      change 0 = cell.displacement * Integral.definiteIntegral cell.polynomial _ _
      unfold Integral.definiteIntegral
      ring1
  | _, _, .cons interval _ tail => by
      change cell.displacement * Integral.definiteIntegral cell.polynomial _ _ +
        Norm.Sum.Basic.gaussianSum _ = _
      rewrite [walk_integralSample cell tail]
      change cell.displacement * Integral.definiteIntegral cell.polynomial
          (Cast.Path.ofCoordinate interval.lower) (Cast.Path.ofCoordinate interval.upper) +
        cell.displacement * Integral.definiteIntegral cell.polynomial
          (Cast.Path.ofCoordinate interval.upper) (Cast.Path.ofCoordinate _) = _
      calc
        _ = cell.displacement * (Integral.definiteIntegral cell.polynomial
            (Cast.Path.ofCoordinate interval.lower) (Cast.Path.ofCoordinate interval.upper) +
          Integral.definiteIntegral cell.polynomial (Cast.Path.ofCoordinate interval.upper)
            (Cast.Path.ofCoordinate _)) := by ring1
        _ = _ := congrArg (cell.displacement * ·)
          (Integral.definiteIntegral_concat cell.polynomial _ _ _).symm

/-- Each of the six ordered restricted source lists has exactly its retained original whole-parent integral sample. -/
theorem integralSample_eq (channel : Fin 6) :
    (PathModel.mk (executed.cells channel)).integralSample =
      (kept.entry.preparation.cell.models.cell channel).integralSample := by
  unfold cells
  rewrite [PathModel.integralSample_ofFn_eq_sumFin]
  have entries := Algebra.FiniteSum.Fin.sumFin_congr
    (fun position => (executed.entry position).integralSample_eq channel)
  have listed := Norm.Sum.Indexed.sumFin_map partition.intervals
    (fun interval => (kept.entry.preparation.cell.models.cell channel).displacement *
      Integral.definiteIntegral (kept.entry.preparation.cell.models.cell channel).polynomial
        (Cast.Path.ofCoordinate interval.lower) (Cast.Path.ofCoordinate interval.upper))
  have whole := walk_integralSample (kept.entry.preparation.cell.models.cell channel) partition.walk
  rewrite [partition.walk_edges] at whole
  exact entries.trans (listed.trans whole)

/-- The actual joined Point-owned row increments in retained interval order, without endpoint cancellation. -/
def rowSample : Canonical :=
  sumFin (fun position =>
    (executed.entry position).acquisition.2.2.joined.observed.last.value -
      (executed.entry position).acquisition.2.2.joined.observed.first.value)

/-- The whole row sample is the original ordered sum of the same retained child Point increments. -/
theorem rowSample_eq : executed.rowSample = sumFin (fun position =>
    (executed.entry position).acquisition.2.2.joined.observed.last.value -
      (executed.entry position).acquisition.2.2.joined.observed.first.value) := by
  unfold rowSample
  rfl

/-- The finite row bound retains each actual endpoint comparison and original primitive remainder payment. -/
def rowBound : Rational :=
  (partition.intervals.length : Rational) * sumFin (fun position =>
    8 * (Primitive.localRequest requested 3).tolerance +
      2 * (executed.entry position).acquisition.2.1.bound)

/-- Actual Point-owned row increments pay their actual restricted relation-cell list internally. -/
theorem row_integral_le : Norm.Basic.normSq
    (executed.rowSample - (PathModel.mk executed.relationCells).integralSample) ≤
      executed.rowBound := by
  unfold relationCells
  rewrite [PathModel.integralSample_ofFn_eq_sumFin]
  exact Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin _ _ _
    (fun position => (executed.entry position).acquisition.2.2.integral_le)

/-- Every interval's actual stationary target is paid by its preselected local request and genuine link count. -/
theorem stationary_error_lt (position : Fin partition.intervals.length) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum
      (executed.entry position).acquisition.2.2.payment.retained.jumps) < requested.tolerance :=
  (executed.entry position).stationary_error_lt

end Partition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

end
