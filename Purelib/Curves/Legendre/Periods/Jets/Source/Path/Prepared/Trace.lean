module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Endpoints
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original primitive-row increments on a retained moving trace edge

The selected row reads the original inverse or cubic primitive caches.
The original prepared-parent source and both endpoint attachments remain
inputs. The old primitive observations belong to the literal moving source
and transported target Owners. Original patch/owner bridges derive their
signed channel relation, and exact request-index transport reuses both old
requests without changing their actual states or radii. The existing cached
source primitive comparison then pays the original moving row integral.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {accuracy : AccuracyRequest} {row : Row}

/-- The unchanged old selected-primitive vertex at the literal cached prepared source of this moving edge. -/
abbrev SourceVertex (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis) (accuracy : AccuracyRequest) :=
  Primitive.Vertex (row.expression parameter)
    (startPoint parent).coordinate parent.edge.cached.preparedOwner accuracy

/-- The unchanged old selected-primitive vertex at this SAME edge's literal transported target Owner. -/
abbrev TargetVertex (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis) (accuracy : AccuracyRequest) :=
  Primitive.Vertex (row.expression parameter)
    (finishPoint parent).coordinate
    (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
      parent.edge.owner parent.edge.request parent.edge.small) accuracy

/-- The endpoint allocation has exactly the same scalar radius target as the old spine request. -/
theorem endpointRequest_index_eq (accuracy : AccuracyRequest) {target : Rational}
    (allocation : target = 4 * accuracy.tolerance) :
    (Primitive.vertexRequest accuracy).tolerance = target / 256 := by
  change accuracy.tolerance / ((64 : Nat) : Rational) = target / 256
  rewrite [allocation]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  have scalar : ((64 : Nat) : Rational)⁻¹ = 4 * (256 : Rational)⁻¹ := by
    rewrite [Fraction.Cast.natCast_eq_fromInt 64]
    decide +kernel
  rewrite [scalar]
  ring1

/-- View the SAME complete old request at the proved equal original endpoint-allocation index.

The original state, value, possible reading, visible radius and process
request are transported together by the original Request.transportTarget. No
radius weakening or second observation producer is involved.
-/
@[expose] def endpointRequest {primitive : Expression (Paths.polynomial parameter)} {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval point)}
    (old : Primitive.Vertex primitive point owner accuracy) {target : Rational}
    (allocation : target = 4 * accuracy.tolerance) : Observation.Request old.original.channel (target / 256) :=
  old.requested.transportTarget (endpointRequest_index_eq accuracy allocation)

/-- The endpoint request view preserves the entire old reading and all of its actual observation data. -/
theorem endpointRequest_reading {primitive : Expression (Paths.polynomial parameter)} {point : Canonical}
    {owner : SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval point)}
    (old : Primitive.Vertex primitive point owner accuracy) {target : Rational}
    (allocation : target = 4 * accuracy.tolerance) :
    (endpointRequest old allocation).reading = old.observation :=
  old.requested.transportTarget_reading (endpointRequest_index_eq accuracy allocation)

/-- Compare an already cached source-query Point with this literal moving source Owner.

The original Readings cache is consumed directly. Only its affine-coordinate
index is transported; the original point Owner, root state and all six
observation caches are left in their original input.
-/
def sourceReadingEquivalent (prepared : PreparedParent patch count floor covered targets)
    (readings : CellModels.Readings prepared.preparation.models prepared.requests 0) :
    NamedEquivalent
      (ownerRootName parent.edge.cached.preparedOwner.parameterNonzero parent.edge.cached.preparedOwner)
      readings.sample.certificate.value.name := by
  have point_eq : (startPoint parent).coordinate = prepared.preparation.models.coordinate.point 0 := by
    rewrite [prepared.preparation.models.coordinate.point_eq]
    change (startPoint parent).coordinate = (startPoint parent).coordinate +
      (0 : Canonical) * ((finishPoint parent).coordinate - (startPoint parent).coordinate)
    rewrite [Basic.zero_mul, Basic.add_zero]
    rfl
  exact patch.sourceEquivalentAt count point_eq readings.sample

/-- Compare an already cached target-query Point with this literal transported moving endpoint Owner. -/
def targetReadingEquivalent (prepared : PreparedParent patch count floor covered targets)
    (readings : CellModels.Readings prepared.preparation.models prepared.requests 1) :
    NamedEquivalent
      (ownerRootName
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small).parameterNonzero
        (PreparedSheetContinuation.transported parent.edge.segment parent.edge.within parent.edge.left
          parent.edge.owner parent.edge.request parent.edge.small)) readings.sample.certificate.value.name := by
  have point_eq : (finishPoint parent).coordinate = prepared.preparation.models.coordinate.point 1 := by
    rewrite [prepared.preparation.models.coordinate.point_eq]
    change (finishPoint parent).coordinate = (startPoint parent).coordinate +
      (1 : Canonical) * ((finishPoint parent).coordinate - (startPoint parent).coordinate)
    ring1
  exact patch.targetEquivalentAt count covered point_eq readings.sample

/-- Derive the actual selected source-polynomial endpoint comparison against the unchanged old moving-source request.

The original attachment supplies the model reading, root precision and
finite stage payments. Its signed generator relation is derived from the
retained patch and literal moving source Owner, rather than supplied as an
endpoint-equivalence hypothesis.
-/
def sourceComparison (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (old : SourceVertex row parent accuracy) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
      (endpointRequest old allocation) := by
  let plan := prepared.firstPlan.val
  let attached := prepared.preparation.attached.firstAttachment
  have roots := (patch.sourceEquivalent count prepared.firstSample).symm
  exact (row.value attached).compare (endpointRequest old allocation) plan.precision attached.root
    attached.endpoint.reading_eq (row.coefficient_le plan) (row.request plan.requests) (start_inside patch count)
    ((row.stage_le plan.requests).trans attached.endpoint.stage_ge)
    ((row.denotation plan).equivalent old.original roots) targets.endpoint_positive

/-- Derive the actual last source-polynomial comparison against the SAME old transported-target request. -/
def targetComparison (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (old : TargetVertex row parent accuracy) (allocation : targets.endpoint = 4 * accuracy.tolerance) :
    PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
      (endpointRequest old allocation) := by
  let plan := prepared.lastPlan.val
  let attached := prepared.preparation.attached.lastAttachment
  have roots := (patch.targetEquivalent count covered prepared.lastSample).symm
  exact (row.value attached).compare (endpointRequest old allocation) plan.precision attached.root
    attached.endpoint.reading_eq (row.coefficient_le plan) (row.request plan.requests) (finish_inside patch count
      covered)
    ((row.stage_le plan.requests).trans attached.endpoint.stage_ge)
    ((row.denotation plan).equivalent old.original roots) targets.endpoint_positive

/-- The complete original source-endpoint comparison has its exact actual producer identity. -/
@[irreducible, expose] def SourceCache (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (old : SourceVertex row parent accuracy) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (compared : PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
      (endpointRequest old allocation)) : Prop := compared = sourceComparison row prepared old allocation

/-- The complete original finishing comparison has the corresponding exact actual producer identity. -/
@[irreducible, expose] def TargetCache (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (old : TargetVertex row parent accuracy) (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (compared : PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
      (endpointRequest old allocation)) : Prop := compared = targetComparison row prepared old allocation

/-- Both whole original endpoint comparisons on the SAME cached source and the two literal old moving vertices. -/
@[expose] def Comparisons (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (first : SourceVertex row parent accuracy) (last : TargetVertex row parent accuracy)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) :=
  { compared : PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
      (endpointRequest first allocation) // SourceCache row prepared first allocation compared } ×
    { compared : PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
      (endpointRequest last allocation) // TargetCache row prepared last allocation compared }

namespace Comparisons

/-- Construct each paid original endpoint comparison once and store its whole factory receipt. -/
def build (row : Row) (prepared : PreparedParent patch count floor covered targets)
    (first : SourceVertex row parent accuracy) (last : TargetVertex row parent accuracy)
    (allocation : targets.endpoint = 4 * accuracy.tolerance) : Comparisons row prepared first last allocation :=
  let source := sourceComparison row prepared first allocation
  let target := targetComparison row prepared last allocation
  ⟨⟨source, by unfold SourceCache; rfl⟩, ⟨target, by unfold TargetCache; rfl⟩⟩

/-- Read the exact factory equation of the retained source comparison without executing its producer again. -/
theorem source_eq {prepared : PreparedParent patch count floor covered targets}
    {first : SourceVertex row parent accuracy} {last : TargetVertex row parent accuracy}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    (retained : Comparisons row prepared first last allocation) :
    retained.1.val = sourceComparison row prepared first allocation := by
  have cached := retained.1.property
  unfold SourceCache at cached
  exact cached

/-- Read the independent original target-comparison factory receipt. -/
theorem target_eq {prepared : PreparedParent patch count floor covered targets}
    {first : SourceVertex row parent accuracy} {last : TargetVertex row parent accuracy}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    (retained : Comparisons row prepared first last allocation) :
    retained.2.val = targetComparison row prepared last allocation := by
  have cached := retained.2.property
  unfold TargetCache at cached
  exact cached

end Comparisons

/-- Three actual scalar errors pay an original oriented moving increment. -/
theorem moving_payment (first last sourceFirst sourceLast integral : Canonical) (target bound : Rational)
    (first_le : Norm.Basic.normSq (sourceFirst - first) ≤ target)
    (last_le : Norm.Basic.normSq (sourceLast - last) ≤ target)
    (integral_le : Norm.Basic.normSq (sourceLast - sourceFirst - integral) ≤ 2 * bound) :
    Norm.Basic.normSq ((last - first) - integral) ≤ 8 * target + 4 * bound := by
  have endpoints := (Norm.Bounds.normSq_sub_le_two (sourceLast - last) (sourceFirst - first)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct last_le first_le) (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  have decomposition : (last - first) - integral =
      (sourceLast - sourceFirst - integral) - ((sourceLast - last) - (sourceFirst - first)) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct integral_le endpoints)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

/-- The actual cached source row integral is paid by the oriented increment of both old moving-link values.

Only differences of the retained source polynomial occur, so its additive
constant cancels. Both endpoint errors come from the stored actual
comparisons, and the moving row uses the SAME original Cell.PrimitiveModels
cache via its whole-cell factory equality. No primitive-increment or final
integral estimate is supplied as an input.
-/
theorem increment_le {prepared : PreparedParent patch count floor covered targets}
    {first : SourceVertex row parent accuracy} {last : TargetVertex row parent accuracy}
    {allocation : targets.endpoint = 4 * accuracy.tolerance}
    (retained : Comparisons row prepared first last allocation) :
    Norm.Basic.normSq ((last.value - first.value) - (row.cell prepared.preparation.models).integralSample) ≤
      8 * targets.endpoint + 4 * prepared.preparation.cell.primitives.bound := by
  have sourceBound := retained.1.val.residual_le
  rewrite [retained.1.val.source_residual, endpointRequest_reading] at sourceBound
  have targetBound := retained.2.val.residual_le
  rewrite [retained.2.val.source_residual, endpointRequest_reading] at targetBound
  have integralBound : Norm.Basic.normSq
      ((row.spatial prepared.preparation.attached.source.models).eval (finishPoint parent).coordinate -
        (row.spatial prepared.preparation.attached.source.models).eval (startPoint parent).coordinate -
        (row.cell prepared.preparation.models).integralSample) ≤
      2 * prepared.preparation.cell.primitives.bound := by
    have original := row.integral_error_le prepared.preparation.cell.primitives
    rewrite [prepared.preparation.cell_eq] at original ⊢
    exact original
  exact moving_payment first.value last.value
    ((row.spatial prepared.preparation.attached.source.models).eval (startPoint parent).coordinate)
    ((row.spatial prepared.preparation.attached.source.models).eval (finishPoint parent).coordinate)
    (row.cell prepared.preparation.models).integralSample targets.endpoint prepared.preparation.cell.primitives.bound
    sourceBound targetBound integralBound

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
