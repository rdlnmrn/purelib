module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Partition.Path
public import Purelib.Riemann.Integration.PreparedConstantModels.Primitive
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Membership
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Sewing

/-! # Actual paid primitive sewing on the original retained parent partition

Every child reads its SAME cached crop and original Point-owned Spine.
The interval walk fixes exact ordered endpoint roles. Its handoffs and both
outer Query observations use the existing preselected local accuracy; all
new comparisons and their finite sum payment are constructed internally.
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
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge (RootedSpine)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine (Sewing)

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

namespace Cropped

variable {kept} {lower upper : Rational}
variable {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
variable {comparisonRequest requested : AccuracyRequest}
variable (acquired : kept.Cropped lower upper lowerInside upperInside comparisonRequest requested)

/-- View the actual unchanged child Point-owned Spine with its original signed parent-query root attachments. -/
def rootedSpine : RootedSpine (curve := Fibre.frameCurve frame) (differential := basis)
    (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) lower upper lowerInside upperInside
    (acquired.acquisition.2.2.joined.observed.last.value - acquired.acquisition.2.2.joined.observed.first.value) :=
  let sampled := acquired.acquisition.2.2.joined.observed
  ⟨acquired.acquisition.2.2.samples.1.val.owner, acquired.acquisition.2.2.samples.2.val.owner,
    sampled.first, sampled.last,
    Sewing.ofSpine (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) sampled,
    acquired.firstRoot (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
      (requested := requested), acquired.lastRoot (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
      (requested := requested)⟩

/-- The SAME original child Spine contributes zero new handoffs before primitive sewing. -/
theorem rootedSpine_count : acquired.rootedSpine.sewn.junctions.length = 0 := by
  unfold rootedSpine
  exact Sewing.ofSpine_count (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) acquired.acquisition.2.2.joined.observed

end Cropped

namespace Partition

variable {kept} {partition : AxisPartition 0 1 cuts} {comparisonRequest requested : AccuracyRequest}
variable (executed : kept.Partition partition comparisonRequest requested)

/-- Read the actual old Point-owned interval increment before any new primitive sewing. -/
private def intervalSample (position : Fin partition.intervals.length) : Canonical :=
  let sampled := (executed.entry position).acquisition.2.2.joined.observed
  sampled.last.value - sampled.first.value

/-- Read that same original scalar interval increment through the retained walk occurrence map. -/
private def walkSamples (position : Fin partition.walk.edges.length) : Canonical :=
  executed.intervalSample (walkIndex (partition := partition) position)

/-- Both admitted fractions come from the original retained partition bounds, even for stationary physical parents. -/
private theorem primitiveBounds : PreparedEdge.Primitive.Bounds partition.intervals :=
  fun interval member =>
    let bounded := partition.interval_bounds member
    ⟨⟨bounded.1, interval.ordered.le.trans bounded.2⟩,
      ⟨bounded.1.trans interval.ordered.le, bounded.2⟩⟩

/-- Materialize exact child-Spine views on the retained walk, without another crop or observation. -/
private def walkPieces : PreparedEdge.Primitive.Pieces (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
    (primitiveBounds (partition := partition)) partition.walk executed.walkSamples :=
  DependentProduct.ofFn partition.walk.edges (fun position =>
    let acquired := executed.entry (walkIndex (partition := partition) position)
    let actual := acquired.rootedSpine
    let intervalEq := walkInterval_eq (partition := partition) position
    actual.castFractions (edge := (parents.covered.parents[index.val]'index.isLt).edge)
      (expression := row.expression parameter) (accuracy := OwnerPath.Primitive.localRequest requested 3)
      (congrArg (fun interval : Interval => interval.lower) intervalEq.symm)
      (congrArg (fun interval : Interval => interval.upper) intervalEq.symm))

/-- Read one actual materialized child view's zero handoff count through its exact original fraction transport. -/
private theorem walkPieces_entry_count (position : Fin partition.walk.edges.length) :
    (RootedSpine.sewn (curve := Fibre.frameCurve frame) (differential := basis)
      (edge := (parents.covered.parents[index.val]'index.isLt).edge)
      (expression := row.expression parameter) (accuracy := OwnerPath.Primitive.localRequest requested 3)
      (DependentProduct.get partition.walk.edges executed.walkPieces position)).junctions.length = 0 := by
  let acquired := executed.entry (walkIndex (partition := partition) position)
  let intervalEq := walkInterval_eq (partition := partition) position
  let actual := acquired.rootedSpine
  let interval := partition.walk.edges[position.val]'position.isLt
  let inside := primitiveBounds (partition := partition) interval
    (partition.walk.edge_mem interval (List.getElem_mem position.isLt))
  unfold walkPieces
  rewrite [DependentProduct.get_ofFn]
  exact (RootedSpine.castFractions_count (curve := Fibre.frameCurve frame) (differential := basis)
    (edge := (parents.covered.parents[index.val]'index.isLt).edge) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) actual
    (nextLowerInside := inside.1) (nextUpperInside := inside.2)
    (congrArg (fun value : Interval => value.lower) intervalEq.symm)
    (congrArg (fun value : Interval => value.upper) intervalEq.symm)).trans acquired.rootedSpine_count

/-- The entire actual child bank retains zero existing-piece handoffs; no observation or crop is rerun. -/
private theorem walkPieces_pieceCount_zero :
    PreparedEdge.Primitive.pieceCount (parents.covered.parents[index.val]'index.isLt).edge
      (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
      (primitiveBounds (partition := partition)) partition.walk executed.walkSamples executed.walkPieces = 0 :=
  PreparedEdge.Primitive.pieceCount_eq_zero (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
    (primitiveBounds (partition := partition)) partition.walk executed.walkSamples executed.walkPieces
    executed.walkPieces_entry_count

/-- Original walk and interval occurrence equality preserves the exact scalar row sample. -/
private theorem walkSamples_sum : sumFin executed.walkSamples = executed.rowSample := by
  have walked := Fin.sumFin_congr_size (congrArg List.length partition.walk_edges)
    executed.walkSamples executed.intervalSample
    (fun first last equal => congrArg executed.intervalSample
      (Fin.ext ((walkIndex_val (partition := partition) first).trans equal)))
  have original : sumFin executed.intervalSample = executed.rowSample :=
    (Fin.sumFin_congr (fun _index => rfl)).trans executed.rowSample_eq.symm
  exact walked.trans original

/-- Construct the actual complete parent primitive Spine, retaining each old Point cache and every paid new handoff.

Both outer Vertices are newly observed at the SAME preselected child
accuracy on the original supplied zero/unit Query Owners. Existing child
observations are unchanged. The exact original walk and signed query names
supply all root and coordinate attachments; no primitive-offset equality is
inferred from a sheet label.
-/
def primitive : RootedSpine (curve := Fibre.frameCurve frame) (differential := basis)
    (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) 0 1
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl) executed.rowSample :=
  let initial := OwnerPath.Primitive.Vertex.build (row.expression parameter)
    ((parents.covered.parents[index.val]'index.isLt).edge.point 0) firstQuery.owner
    (OwnerPath.Primitive.localRequest requested 3)
    (Row.defined parameter ((parents.covered.parents[index.val]'index.isLt).edge.point 0) row firstQuery.owner)
  let terminal := OwnerPath.Primitive.Vertex.build (row.expression parameter)
    ((parents.covered.parents[index.val]'index.isLt).edge.point 1) lastQuery.owner
    (OwnerPath.Primitive.localRequest requested 3)
    (Row.defined parameter ((parents.covered.parents[index.val]'index.isLt).edge.point 1) row lastQuery.owner)
  let firstRoot := NamedEquivalent.transport rfl firstQuery.name_eq
    (NamedEquivalent.refl ((parents.covered.parents[index.val]'index.isLt).edge.rootName 0
      (parents.covered.parents[index.val]'index.isLt).edge.baseInside))
  let lastRoot := NamedEquivalent.transport rfl lastQuery.name_eq
    (NamedEquivalent.refl ((parents.covered.parents[index.val]'index.isLt).edge.rootName 1 (of_decide_eq_true rfl)))
  let actual := PreparedEdge.Primitive.sewWalk (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) (primitiveBounds (partition := partition))
    partition.walk executed.walkSamples executed.walkPieces
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl)
    firstQuery.owner lastQuery.owner firstRoot.symm lastRoot initial terminal
  let sewn := Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) executed.walkSamples_sum actual
  ⟨firstQuery.owner, lastQuery.owner, initial, terminal, sewn, firstRoot, lastRoot⟩

/-- Count the SAME parent assembly with abstract endpoint observations, leaving their factories opaque. -/
private theorem primitiveAt_count
    (initial : OwnerPath.Primitive.Vertex (row.expression parameter)
      ((parents.covered.parents[index.val]'index.isLt).edge.point 0) firstQuery.owner
      (OwnerPath.Primitive.localRequest requested 3))
    (terminal : OwnerPath.Primitive.Vertex (row.expression parameter)
      ((parents.covered.parents[index.val]'index.isLt).edge.point 1) lastQuery.owner
      (OwnerPath.Primitive.localRequest requested 3))
    (firstRoot : NamedEquivalent
      ((parents.covered.parents[index.val]'index.isLt).edge.rootName 0
        (parents.covered.parents[index.val]'index.isLt).edge.baseInside) (ownerName firstQuery.owner))
    (lastRoot : NamedEquivalent
      ((parents.covered.parents[index.val]'index.isLt).edge.rootName 1 (of_decide_eq_true rfl))
      (ownerName lastQuery.owner)) :
    RootedSpine.junctionCount (curve := Fibre.frameCurve frame) (differential := basis)
      (edge := (parents.covered.parents[index.val]'index.isLt).edge)
      (expression := row.expression parameter) (accuracy := OwnerPath.Primitive.localRequest requested 3)
      (lower := 0) (upper := 1)
      (lowerInside := (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
      (upperInside := (of_decide_eq_true rfl)) (sample := executed.rowSample)
      ⟨firstQuery.owner, lastQuery.owner, initial, terminal,
        Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
          (accuracy := OwnerPath.Primitive.localRequest requested 3) executed.walkSamples_sum
          (PreparedEdge.Primitive.sewWalk (curve := Fibre.frameCurve frame) (differential := basis)
            (parents.covered.parents[index.val]'index.isLt).edge
            (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
            (primitiveBounds (partition := partition)) partition.walk executed.walkSamples executed.walkPieces
            (parents.covered.parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl)
            firstQuery.owner lastQuery.owner firstRoot.symm lastRoot initial terminal), firstRoot, lastRoot⟩ =
      partition.intervals.length + 1 := by
  let actual := PreparedEdge.Primitive.sewWalk (curve := Fibre.frameCurve frame) (differential := basis)
    (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) (primitiveBounds (partition := partition))
    partition.walk executed.walkSamples executed.walkPieces
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl)
    firstQuery.owner lastQuery.owner firstRoot.symm lastRoot initial terminal
  change (Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) executed.walkSamples_sum actual).junctions.length = _
  have counted := PreparedEdge.Primitive.sewWalk_count (curve := Fibre.frameCurve frame) (differential := basis)
    (parents.covered.parents[index.val]'index.isLt).edge
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) (primitiveBounds (partition := partition))
    partition.walk executed.walkSamples executed.walkPieces
    (parents.covered.parents[index.val]'index.isLt).edge.baseInside (of_decide_eq_true rfl)
    firstQuery.owner lastQuery.owner firstRoot.symm lastRoot initial terminal
  have noOld := congrArg (fun count : Nat => count + partition.walk.edges.length + 1)
    executed.walkPieces_pieceCount_zero
  have zero := congrArg (fun count : Nat => count + 1) (Nat.zero_add partition.walk.edges.length)
  have lengths := congrArg (fun count : Nat => count + 1) (congrArg List.length partition.walk_edges)
  exact (Sewing.castSample_count (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) executed.walkSamples_sum actual).trans
      (counted.trans (noOld.trans (zero.trans lengths)))

/-- The actual parent sewing has exactly one new handoff per original interval plus its final comparison. -/
theorem primitive_count :
    RootedSpine.junctionCount (curve := Fibre.frameCurve frame) (differential := basis)
      (edge := (parents.covered.parents[index.val]'index.isLt).edge)
      (expression := row.expression parameter) (accuracy := OwnerPath.Primitive.localRequest requested 3)
      (lower := 0) (upper := 1)
      (lowerInside := (parents.covered.parents[index.val]'index.isLt).edge.baseInside)
      (upperInside := (of_decide_eq_true rfl)) (sample := executed.rowSample)
      (primitive (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
        (requested := requested) executed) = partition.intervals.length + 1 := by
  let initial := OwnerPath.Primitive.Vertex.build (row.expression parameter)
    ((parents.covered.parents[index.val]'index.isLt).edge.point 0) firstQuery.owner
    (OwnerPath.Primitive.localRequest requested 3)
    (Row.defined parameter ((parents.covered.parents[index.val]'index.isLt).edge.point 0) row firstQuery.owner)
  let terminal := OwnerPath.Primitive.Vertex.build (row.expression parameter)
    ((parents.covered.parents[index.val]'index.isLt).edge.point 1) lastQuery.owner
    (OwnerPath.Primitive.localRequest requested 3)
    (Row.defined parameter ((parents.covered.parents[index.val]'index.isLt).edge.point 1) row lastQuery.owner)
  let firstRoot := NamedEquivalent.transport rfl firstQuery.name_eq
    (NamedEquivalent.refl ((parents.covered.parents[index.val]'index.isLt).edge.rootName 0
      (parents.covered.parents[index.val]'index.isLt).edge.baseInside))
  let lastRoot := NamedEquivalent.transport rfl lastQuery.name_eq
    (NamedEquivalent.refl ((parents.covered.parents[index.val]'index.isLt).edge.rootName 1 (of_decide_eq_true rfl)))
  exact primitiveAt_count executed initial terminal firstRoot lastRoot

end Partition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison.EndpointPoints

end
