module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Requested primitive observations on the actual prepared endpoint Points

Each primitive Vertex reuses the retained EndpointPlan's SAME coefficient
denotation and actual Point Owner. One new request is selected at the
source target's computed accuracy; no point, query, coefficient cache or
source model is rebuilt. The original source endpoint comparisons and
Row primitive cache derive the finite moving-integral error. Actual first
and last query-to-Point comparisons are stored separately for signed sewing.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Retain the SAME endpoint-plan coefficient denotation and request its primitive reading once at this actual Owner. -/
def vertex (row : Row) {size : Nat} {point : Canonical}
    {neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) size}
    {sample : ContinuedNeighborhood.Point neighborhood point} {sourceFloor : Nat} {allocation : Rational}
    (plan : EndpointPlan sample sourceFloor allocation) (accuracy : AccuracyRequest) :
    Primitive.Vertex (row.expression parameter) point sample.owner accuracy :=
  let denotation := row.denotation plan
  let requested := Observation.Request.build denotation.channel (Primitive.vertexRequest accuracy).tolerance
    (Primitive.vertexRequest accuracy).positive
  Primitive.Vertex.ofCompleted denotation requested

/-- The observed primitive retains the SAME complete original EndpointPlan denotation. -/
theorem vertex_original (row : Row) {size : Nat} {point : Canonical}
    {neighborhood : ContinuedNeighborhood (Paths.polynomial parameter) size}
    {sample : ContinuedNeighborhood.Point neighborhood point} {sourceFloor : Nat} {allocation : Rational}
    (plan : EndpointPlan sample sourceFloor allocation) (accuracy : AccuracyRequest) :
    (vertex row plan accuracy).original = row.denotation plan := by
  unfold vertex Primitive.Vertex.ofCompleted Primitive.Vertex.original
  rfl

variable (row : Row) (prepared : PreparedParent patch count floor covered targets)

/-- The exact original starting Point-owned observation type at the computed source accuracy. -/
@[expose] def First := Primitive.Vertex (row.expression parameter) (startPoint parent).coordinate
  prepared.firstSample.owner (PreparedParents.Trace.localAccuracy targets)

/-- The independent original finishing Point-owned observation type at that same computed source accuracy. -/
@[expose] def Last := Primitive.Vertex (row.expression parameter) (finishPoint parent).coordinate
  prepared.lastSample.owner (PreparedParents.Trace.localAccuracy targets)

/-- Compare a GIVEN actual source Point Vertex to its SAME retained spatial primitive endpoint. -/
def sourceComparison (first : First row prepared)
    (originalEq : first.original = row.denotation prepared.firstPlan.val) :
    PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
      (endpointRequest first (PreparedParents.Trace.localAccuracy_allocation targets)) := by
  let plan := prepared.firstPlan.val
  let attached := prepared.preparation.attached.firstAttachment
  have channels := congrArg (fun original : PrimitiveDenotation prepared.firstSample row.pairs
    (row.numerator parameter) => original.channel.name) originalEq
  have equivalent := NamedEquivalent.transport rfl channels.symm
    (NamedEquivalent.refl (row.denotation plan).channel.name)
  exact (row.value attached).compare (endpointRequest first (PreparedParents.Trace.localAccuracy_allocation targets))
    plan.precision attached.root attached.endpoint.reading_eq (row.coefficient_le plan) (row.request plan.requests)
    (start_inside patch count) ((row.stage_le plan.requests).trans attached.endpoint.stage_ge)
    equivalent targets.endpoint_positive

/-- Compare the GIVEN independent finish Point Vertex to its own actual retained spatial primitive endpoint. -/
def targetComparison (last : Last row prepared)
    (originalEq : last.original = row.denotation prepared.lastPlan.val) :
    PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
      (endpointRequest last (PreparedParents.Trace.localAccuracy_allocation targets)) := by
  let plan := prepared.lastPlan.val
  let attached := prepared.preparation.attached.lastAttachment
  have channels := congrArg (fun original : PrimitiveDenotation prepared.lastSample row.pairs
    (row.numerator parameter) => original.channel.name) originalEq
  have equivalent := NamedEquivalent.transport rfl channels.symm
    (NamedEquivalent.refl (row.denotation plan).channel.name)
  exact (row.value attached).compare (endpointRequest last (PreparedParents.Trace.localAccuracy_allocation targets))
    plan.precision attached.root attached.endpoint.reading_eq (row.coefficient_le plan) (row.request plan.requests)
    (finish_inside patch count covered) ((row.stage_le plan.requests).trans attached.endpoint.stage_ge)
    equivalent targets.endpoint_positive

/-- The complete new actual Point observations, original signed query bridges, comparisons and cached moving residual.

Both source Points and EndpointPlans remain the original supplied caches.
Every new primitive request and comparison has its exact producer equation.
The selected source-cell integral and moving residual are computed once;
large polynomial endpoint readbacks occur only in erased proofs.
-/
@[expose] def Compared :=
  (first : {value : First row prepared //
    value = vertex row prepared.firstPlan.val (PreparedParents.Trace.localAccuracy targets)}) ×
  (last : {value : Last row prepared //
    value = vertex row prepared.lastPlan.val (PreparedParents.Trace.localAccuracy targets)}) ×
  (_firstRoots : {value : NamedEquivalent (parent.edge.rootName 0 parent.edge.baseInside)
      (ownerName prepared.firstSample.owner) // value = prepared.firstQueryEquivalent}) ×
  (_lastRoots : {value : NamedEquivalent (parent.edge.rootName 1 (of_decide_eq_true rfl))
      (ownerName prepared.lastSample.owner) // value = prepared.lastQueryEquivalent}) ×
  (_firstCompared : {value : PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
      (endpointRequest first.val (PreparedParents.Trace.localAccuracy_allocation targets)) //
    value = sourceComparison row prepared first.val
      ((congrArg (fun observed : First row prepared => observed.original) first.property).trans
        (vertex_original row prepared.firstPlan.val (PreparedParents.Trace.localAccuracy targets)))}) ×
  (_lastCompared : {value : PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
      (endpointRequest last.val (PreparedParents.Trace.localAccuracy_allocation targets)) //
    value = targetComparison row prepared last.val
      ((congrArg (fun observed : Last row prepared => observed.original) last.property).trans
        (vertex_original row prepared.lastPlan.val (PreparedParents.Trace.localAccuracy targets)))}) ×
  (sample : {value : Canonical // value = (row.cell prepared.preparation.models).integralSample}) ×
  {error : Canonical // error = last.val.value - first.val.value - sample.val}

/-- Observe both original Point denotations once and retain their actual comparisons and SAME cached row integral. -/
def build : Compared row prepared :=
  let accuracy := PreparedParents.Trace.localAccuracy targets
  let first := vertex row prepared.firstPlan.val accuracy
  let last := vertex row prepared.lastPlan.val accuracy
  let firstRoots := prepared.firstQueryEquivalent
  let lastRoots := prepared.lastQueryEquivalent
  let source := sourceComparison row prepared first (vertex_original row prepared.firstPlan.val accuracy)
  let target := targetComparison row prepared last (vertex_original row prepared.lastPlan.val accuracy)
  let sample := (row.cell prepared.preparation.models).integralSample
  let error := last.value - first.value - sample
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩, ⟨firstRoots, rfl⟩, ⟨lastRoots, rfl⟩, ⟨source, rfl⟩, ⟨target, rfl⟩,
    ⟨sample, rfl⟩, ⟨error, rfl⟩⟩

namespace Compared

variable {row prepared} (retained : Compared row prepared)

/-- Read the actual new primitive Vertex at the SAME retained source Point Owner. -/
@[expose] def first : First row prepared := retained.1.val

/-- Read the separate new primitive Vertex at the SAME retained finishing Point Owner. -/
@[expose] def last : Last row prepared := retained.2.1.val

/-- Read the original signed child-query-to-source-Point comparison, without identifying those independent Owners. -/
@[expose] def firstRoots : NamedEquivalent (parent.edge.rootName 0 parent.edge.baseInside)
    (ownerName prepared.firstSample.owner) := retained.2.2.1.val

/-- Read the actual child-finish-query-to-finishing-Point comparison on the SAME prepared neighborhood. -/
@[expose] def lastRoots : NamedEquivalent (parent.edge.rootName 1 (of_decide_eq_true rfl))
    (ownerName prepared.lastSample.owner) := retained.2.2.2.1.val

/-- Read the actual source polynomial-to-new Point observation comparison. -/
@[expose] def source : PrimitiveValue.Comparison (row.value prepared.preparation.attached.firstAttachment)
    (endpointRequest retained.first (PreparedParents.Trace.localAccuracy_allocation targets)) := retained.2.2.2.2.1.val

/-- Read the independent actual finishing polynomial-to-new Point observation comparison. -/
@[expose] def target : PrimitiveValue.Comparison (row.value prepared.preparation.attached.lastAttachment)
    (endpointRequest retained.last (PreparedParents.Trace.localAccuracy_allocation targets)) := retained.2.2.2.2.2.1.val

/-- Read the once computed SAME selected source-cell integral. -/
@[expose] def sample : Canonical := retained.2.2.2.2.2.2.1.val

/-- Read the once computed actual oriented primitive-minus-source residual. -/
@[expose] def error : Canonical := retained.2.2.2.2.2.2.2.val

/-- The actual source observation has its whole original request factory on the retained plan denotation. -/
theorem first_eq : retained.first = vertex row prepared.firstPlan.val (PreparedParents.Trace.localAccuracy targets) :=
  retained.1.property

/-- The separate target observation retains its own whole original request factory. -/
theorem last_eq : retained.last = vertex row prepared.lastPlan.val (PreparedParents.Trace.localAccuracy targets) :=
  retained.2.1.property

/-- The signed source root bridge is the original prepared-query comparison on that actual Point. -/
theorem firstRoots_eq : retained.firstRoots = prepared.firstQueryEquivalent := retained.2.2.1.property

/-- The signed finishing root bridge is its independent original prepared-query comparison. -/
theorem lastRoots_eq : retained.lastRoots = prepared.lastQueryEquivalent := retained.2.2.2.1.property

/-- The cached integral is the SAME selected original row-cell sample. -/
theorem sample_eq : retained.sample = (row.cell prepared.preparation.models).integralSample :=
  retained.2.2.2.2.2.2.1.property

/-- The actual cached moving residual retains the orientation and both distinct Point observation values. -/
theorem error_eq : retained.error = retained.last.value - retained.first.value - retained.sample :=
  retained.2.2.2.2.2.2.2.property

/-- The actual source primitive cache and both original endpoint comparisons pay the SAME moving source integral. -/
theorem error_le : Norm.Basic.normSq retained.error ≤ 12 * targets.endpoint := by
  have firstBound := retained.source.residual_le
  rewrite [retained.source.source_residual, endpointRequest_reading] at firstBound
  have lastBound := retained.target.residual_le
  rewrite [retained.target.source_residual, endpointRequest_reading] at lastBound
  have integralBound : Norm.Basic.normSq
      ((row.spatial prepared.preparation.attached.source.models).eval (finishPoint parent).coordinate -
        (row.spatial prepared.preparation.attached.source.models).eval (startPoint parent).coordinate -
        (row.cell prepared.preparation.models).integralSample) ≤
      2 * prepared.preparation.cell.primitives.bound := by
    have original := row.integral_error_le prepared.preparation.cell.primitives
    rewrite [prepared.preparation.cell_eq] at original ⊢
    exact original
  have moving := PreparedParent.moving_payment retained.first.value retained.last.value
    ((row.spatial prepared.preparation.attached.source.models).eval (startPoint parent).coordinate)
    ((row.spatial prepared.preparation.attached.source.models).eval (finishPoint parent).coordinate)
    (row.cell prepared.preparation.models).integralSample targets.endpoint prepared.preparation.cell.primitives.bound
    firstBound lastBound integralBound
  have sourcePaid := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    prepared.bound_le_endpoint (of_decide_eq_true rfl : (0 : Rational) ≤ 4)
  have total := Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct
    (Data.Rat.Fraction.Order.Basic.le_refl (8 * targets.endpoint)) sourcePaid
  have scalar : Norm.Basic.normSq (retained.last.value - retained.first.value -
      (row.cell prepared.preparation.models).integralSample) ≤ 12 * targets.endpoint :=
    moving.trans (total.trans_eq (by ring1))
  have exactError : retained.error = retained.last.value - retained.first.value -
      (row.cell prepared.preparation.models).integralSample :=
    retained.error_eq.trans (congrArg (fun integral : Canonical =>
      retained.last.value - retained.first.value - integral) retained.sample_eq)
  exact (congrArg Norm.Basic.normSq exactError).trans_le scalar

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Points

end
