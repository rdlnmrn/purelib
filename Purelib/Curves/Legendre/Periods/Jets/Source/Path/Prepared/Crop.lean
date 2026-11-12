module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Models
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Endpoints
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Joins
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment.Retained
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Tactic.Ring

/-! # Actual source crops on an unchanged prepared parent

The supplied original crop operation remains a separate indexed owner.
Its genuine one-target geometry is retained explicitly, rather than inferred
from its endpoint type. Original rooted queries, seven polynomial restrictions,
new moving observations and both actual Point joins remain the same caches.
The retained six integrands and row-relation payment are separate channels.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
variable (prepared : PreparedParent patch count floor covered targets)
variable (lower upper : Rational)
variable (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
variable (operation : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside)

/-- The original supplied crop, its genuine vertex evidence and all actual source/model/moving caches. -/
@[expose] def Crop :=
  Σ original : {value : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside //
    value = operation ∧ ∀ first last, (value.2 first last).vertices = [parent.edge.point upper]},
  Σ queries : RootedQueries (frame := frame) prepared,
  Σ endpoints : {values : RootedQuery (frame := frame) prepared lower lowerInside ×
      RootedQuery (frame := frame) prepared upper upperInside //
    values = (queries lower lowerInside, queries upper upperInside)},
  Σ _models : CroppedModels prepared row lower upper,
  {moving : OwnerPath (Paths.polynomial parameter)
      (parent.edge.point lower) endpoints.val.1.direct.owner
      (parent.edge.point upper) endpoints.val.2.direct.owner //
    moving = original.val.2 endpoints.val.1.direct endpoints.val.2.direct}

namespace Crop

/-- Construct the actual source crop on the supplied original operation and its separately certified vertex law.

Both rooted endpoint answers execute once and retain the original source
bundle and direct Query Owner. Seven actual restrictions and the moving
path consume those exact caches. No View or source preparation is rebuilt.
-/
def build
    (vertices : ∀ first last, (operation.2 first last).vertices = [parent.edge.point upper]) :
    Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation :=
  let queries : RootedQueries (frame := frame) prepared :=
    fun fraction inside => RootedQuery.build prepared fraction inside
  let first := queries lower lowerInside
  let last := queries upper upperInside
  let models := CroppedModels.build prepared row lower upper
  let moving := operation.2 first.direct last.direct
  ⟨⟨operation, rfl, vertices⟩, queries, ⟨⟨first, last⟩, rfl⟩, models, ⟨moving, rfl⟩⟩

variable {prepared lower upper lowerInside upperInside operation}
variable (cropped : Crop (frame := frame) (basis := basis) (row := row)
  prepared lower upper lowerInside upperInside operation)

/-- Read the entire original supplied crop closure, including its retained endpoint-comparison functions. -/
abbrev physical := cropped.1.val

/-- Read the productive original source-query callback without preparing another model. -/
abbrev queries := cropped.2.1

/-- Read both complete actual endpoint answers with their separate source bundles, direct Queries and root evidence. -/
abbrev endpoints := cropped.2.2.1.val

/-- Read all seven actual cached polynomial restrictions unchanged. -/
abbrev models := cropped.2.2.2.1

/-- Read the actual once-executed moving crop with its two retained direct Query Owners. -/
abbrev moving := cropped.2.2.2.2.val

/-- The complete stored crop operation is the original supplied value, with no lookup or reconstruction. -/
theorem physical_eq : cropped.physical = operation := cropped.1.property.1

/-- The stored actual operation retains its genuine one-target occurrence certificate. -/
theorem physical_vertices : ∀ first last, (cropped.physical.2 first last).vertices = [parent.edge.point upper] :=
  cropped.1.property.2

/-- The original moving path retains exactly its certified target occurrence, including degenerate intervals. -/
theorem moving_vertices : cropped.moving.vertices = [parent.edge.point upper] :=
  (congrArg (fun path : OwnerPath (Paths.polynomial parameter)
    (parent.edge.point lower) cropped.endpoints.1.direct.owner
    (parent.edge.point upper) cropped.endpoints.2.direct.owner => path.vertices) cropped.2.2.2.2.property).trans
      (cropped.physical_vertices cropped.endpoints.1.direct cropped.endpoints.2.direct)

/-- Reindex an entire actual cached endpoint answer along equality of its original rational parameter. -/
private def endpointAt {fraction nextFraction : Rational}
    {inside : 0 ≤ fraction ∧ fraction ≤ 1} {nextInside : 0 ≤ nextFraction ∧ nextFraction ≤ 1}
    (equal : fraction = nextFraction)
    (queried : RootedQuery (frame := frame) prepared fraction inside) :
    RootedQuery (frame := frame) prepared nextFraction nextInside := by
  cases equal
  exact queried

/-- Endpoint reindexing retains the whole original bundle, direct Query, root comparisons and selected states. -/
private theorem endpointAt_heq {fraction nextFraction : Rational}
    {inside : 0 ≤ fraction ∧ fraction ≤ 1} {nextInside : 0 ≤ nextFraction ∧ nextFraction ≤ 1}
    (equal : fraction = nextFraction)
    (queried : RootedQuery (frame := frame) prepared fraction inside) :
    HEq (endpointAt (nextInside := nextInside) equal queried) queried := by
  cases equal
  rfl

/-- Retain both actual endpoint answers by child-parameter role and query only genuine interior fractions.

Zero reuses the whole lower answer and one reuses the independent whole
upper answer. This preserves both occurrences even for a degenerate parent
interval. Exact rational-parameter transport changes only indices; every
cached observation, direct Owner and root comparison remains unchanged.
-/
def queryAt (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    RootedQuery (frame := frame) prepared (Cell.Restriction.parameter lower upper input)
      (Cell.Restriction.parameter_inside lowerInside upperInside inside) :=
  if atFirst : input = 0 then
    endpointAt (by rewrite [atFirst]; unfold Cell.Restriction.parameter; ring1) cropped.endpoints.1
  else if atLast : input = 1 then
    endpointAt (by rewrite [atLast]; unfold Cell.Restriction.parameter; ring1) cropped.endpoints.2
  else
    cropped.queries (Cell.Restriction.parameter lower upper input)
      (Cell.Restriction.parameter_inside lowerInside upperInside inside)

/-- Querying child parameter zero reuses the entire retained lower endpoint execution. -/
theorem queryAt_zero_heq (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1) :
    HEq (cropped.queryAt 0 inside) cropped.endpoints.1 := by
  unfold queryAt
  rewrite [dif_pos rfl]
  exact endpointAt_heq _ _

/-- Querying child parameter one reuses the entire distinct retained upper endpoint execution. -/
theorem queryAt_one_heq (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1) :
    HEq (cropped.queryAt 1 inside) cropped.endpoints.2 := by
  unfold queryAt
  rewrite [dif_neg (of_decide_eq_true rfl : (1 : Rational) ≠ 0), dif_pos rfl]
  exact endpointAt_heq _ _

/-- Every genuine interior child parameter has its original same-callback factory, with no endpoint replacement. -/
theorem queryAt_strict (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (notFirst : input ≠ 0) (notLast : input ≠ 1) :
    cropped.queryAt input inside = cropped.queries (Cell.Restriction.parameter lower upper input)
      (Cell.Restriction.parameter_inside lowerInside upperInside inside) := by
  unfold queryAt
  rewrite [dif_neg notFirst, dif_neg notLast]
  rfl

/-- Construct the six actual child certificates from these same cached endpoint and interior query answers. -/
def certificates := cropped.models.certificates lowerInside upperInside cropped.queryAt

/-- One actual new moving observation and both internally derived source/query endpoint comparison caches. -/
@[expose] def Observation (comparisonRequest : AccuracyRequest) :=
  Σ sampled : {value : Primitive.Spine (row.expression parameter) accuracy cropped.moving //
    value = Primitive.Spine.build (accuracy := accuracy) cropped.moving (Trace.defined row cropped.moving)},
    Crop.EndpointComparison prepared row cropped.endpoints.1 sampled.val.first comparisonRequest ×
      Crop.EndpointComparison prepared row cropped.endpoints.2 sampled.val.last comparisonRequest

namespace Observation

/-- Observe the moving path once and compare its endpoints using both same retained rooted source answers. -/
def build (comparisonRequest : AccuracyRequest) : cropped.Observation (accuracy := accuracy) comparisonRequest :=
  let sampled := Primitive.Spine.build (accuracy := accuracy) cropped.moving (Trace.defined row cropped.moving)
  let first := Crop.EndpointComparison.build prepared row cropped.endpoints.1
    sampled.first comparisonRequest
  let last := Crop.EndpointComparison.build prepared row cropped.endpoints.2
    sampled.last comparisonRequest
  ⟨⟨sampled, rfl⟩, first, last⟩

variable {cropped} {comparisonRequest : AccuracyRequest}
variable (observed : cropped.Observation (accuracy := accuracy) comparisonRequest)

/-- Read the same complete moving observation execution. -/
abbrev sampled := observed.1.val

/-- Read both actual endpoint source/observation comparison caches without another finite comparison. -/
abbrev comparisons := observed.2

/-- The finite moving payment retains both endpoint residual/radius bounds and the squared subinterval length. -/
abbrev bound : Rational :=
  4 * (observed.comparisons.1.bound + observed.comparisons.2.bound) +
    4 * prepared.preparation.cell.primitives.bound * (upper - lower) ^ 2

/-- The moving increment pays the actual restricted row-cell integral from its retained finite evidence. -/
theorem integral_le : Norm.Basic.normSq
    ((observed.sampled.last.value - observed.sampled.first.value) - cropped.models.relation.integralSample) ≤
    observed.bound := by
  let sourceFirst := (row.spatial prepared.preparation.cell.request.models).eval
    (prepared.preparation.cell.models.coordinate.point lower)
  let sourceLast := (row.spatial prepared.preparation.cell.request.models).eval
    (prepared.preparation.cell.models.coordinate.point upper)
  have endpoints := (Norm.Bounds.normSq_sub_le_two
    (sourceLast - observed.sampled.last.value) (sourceFirst - observed.sampled.first.value)).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct observed.comparisons.2.error_le observed.comparisons.1.error_le)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  have primitive := cropped.models.primitive_error_le lowerInside upperInside
  have decomposition : (observed.sampled.last.value - observed.sampled.first.value) -
      cropped.models.relation.integralSample =
      (sourceLast - sourceFirst - cropped.models.relation.integralSample) -
        ((sourceLast - observed.sampled.last.value) - (sourceFirst - observed.sampled.first.value)) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct primitive endpoints)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

/-- Two actual physical Points, their independent direct-Query comparisons, both new joins and their actual payments. -/
@[expose] def Points (requested : AccuracyRequest) :=
  Σ samples :
      {value : ContinuedNeighborhood.Point (patch.neighborhood count)
          (parent.edge.point lower) //
        value = prepared.sampleAt lower lowerInside} ×
      {value : ContinuedNeighborhood.Point (patch.neighborhood count)
          (parent.edge.point upper) //
        value = prepared.sampleAt upper upperInside},
  Σ roots : NamedEquivalent (ownerName cropped.endpoints.1.direct.owner) samples.1.val.certificate.value.name ×
      NamedEquivalent (ownerName cropped.endpoints.2.direct.owner) samples.2.val.certificate.value.name,
  Σ joins :
      {value : OwnerJoin samples.1.val.owner cropped.endpoints.1.direct.owner //
        value = OwnerJoin.acquire samples.1.val.owner cropped.endpoints.1.direct.owner roots.1.symm} ×
      {value : OwnerJoin cropped.endpoints.2.direct.owner samples.2.val.owner //
        value = OwnerJoin.acquire cropped.endpoints.2.direct.owner samples.2.val.owner roots.2},
  Σ joined : Primitive.Spine.WithJoins observed.sampled joins.1.val joins.2.val,
    {payment : Primitive.Spine.Payment joined.observed requested
        (cropped.moving.withJoins joins.1.val joins.2.val).vertices.length //
      payment = Primitive.Spine.Payment.build joined.observed requested
        (cropped.moving.withJoins joins.1.val joins.2.val).vertices.length rfl}

namespace Points

/-- Retain complete Point, root, join and payment caches without reducing any of their acquisition factories. -/
private def pack (requested : AccuracyRequest)
    (first : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.point lower))
    (last : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.point upper))
    (firstEq : first = prepared.sampleAt lower lowerInside)
    (lastEq : last = prepared.sampleAt upper upperInside)
    (firstRoot : NamedEquivalent (ownerName cropped.endpoints.1.direct.owner) first.certificate.value.name)
    (lastRoot : NamedEquivalent (ownerName cropped.endpoints.2.direct.owner) last.certificate.value.name)
    (source : OwnerJoin first.owner cropped.endpoints.1.direct.owner)
    (target : OwnerJoin cropped.endpoints.2.direct.owner last.owner)
    (sourceEq : source = OwnerJoin.acquire first.owner cropped.endpoints.1.direct.owner firstRoot.symm)
    (targetEq : target = OwnerJoin.acquire cropped.endpoints.2.direct.owner last.owner lastRoot)
    (joined : Primitive.Spine.WithJoins observed.sampled source target)
    (payment : Primitive.Spine.Payment joined.observed requested
      (cropped.moving.withJoins source target).vertices.length)
    (paymentEq : payment = Primitive.Spine.Payment.build joined.observed requested
      (cropped.moving.withJoins source target).vertices.length rfl) :
    observed.Points requested :=
  ⟨⟨⟨first, firstEq⟩, ⟨last, lastEq⟩⟩, ⟨firstRoot, lastRoot⟩,
    ⟨⟨source, sourceEq⟩, ⟨target, targetEq⟩⟩, joined, ⟨payment, paymentEq⟩⟩

/-- Attach two retained Points and their actual root relations without unfolding their acquisition factories. -/
private def attach (requested : AccuracyRequest)
    (first : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.point lower))
    (last : ContinuedNeighborhood.Point (patch.neighborhood count)
      (parent.edge.point upper))
    (firstEq : first = prepared.sampleAt lower lowerInside)
    (lastEq : last = prepared.sampleAt upper upperInside)
    (firstRoot : NamedEquivalent (ownerName cropped.endpoints.1.direct.owner) first.certificate.value.name)
    (lastRoot : NamedEquivalent (ownerName cropped.endpoints.2.direct.owner) last.certificate.value.name) :
    observed.Points requested :=
  let source := OwnerJoin.acquire first.owner cropped.endpoints.1.direct.owner firstRoot.symm
  let target := OwnerJoin.acquire cropped.endpoints.2.direct.owner last.owner lastRoot
  let joined := Primitive.Spine.withJoins observed.sampled source target
    (Row.defined parameter _ row first.owner) (Row.defined parameter _ row last.owner)
  let payment := Primitive.Spine.Payment.build joined.observed requested
    (cropped.moving.withJoins source target).vertices.length rfl
  pack observed requested first last firstEq lastEq firstRoot lastRoot source target rfl rfl joined payment rfl

/-- Construct both genuine fractional Points and paid joins around the retained moving observations.

Strict fractions acquire their own actual Points on the original patch.
Each comparison consumes its same retained direct Query. Both new joins,
their new outer observations and stationary comparison payments are kept;
the actual vertex count drives the existing paid/unpaid allocation outcome.
-/
def build (requested : AccuracyRequest) : observed.Points requested :=
  let first := prepared.sampleAt lower lowerInside
  let last := prepared.sampleAt upper upperInside
  let firstRoot := NamedEquivalent.transport cropped.endpoints.1.direct.name_eq rfl
    (patch.retainedQueryEquivalent count lower lowerInside cropped.endpoints.1.direct rfl
      (PreparedParent.sample_inside (frame := frame) (basis := basis) (covered := covered) lowerInside) first)
  let lastRoot := NamedEquivalent.transport cropped.endpoints.2.direct.name_eq rfl
    (patch.retainedQueryEquivalent count upper upperInside cropped.endpoints.2.direct rfl
      (PreparedParent.sample_inside (frame := frame) (basis := basis) (covered := covered) upperInside) last)
  attach observed requested first last rfl rfl firstRoot lastRoot

variable {observed} {requested : AccuracyRequest}
variable (points : observed.Points requested)

/-- Read both actual independent physical Point caches with their original sampleAt equations. -/
abbrev samples := points.1

/-- Read the retained actual Query/Point root comparisons unchanged. -/
abbrev roots := points.2.1

/-- Read the two complete new endpoint joins and both acquisition equations. -/
abbrev joins := points.2.2.1

/-- Read the actual Point-owned complete Spine containing the same original moving observation cache. -/
abbrev joined := points.2.2.2.1

/-- Read the actual stationary-error allocation outcome, including its original unpaid result. -/
abbrev payment := points.2.2.2.2.val

/-- Both actual endpoint joins and the genuine moving occurrence give exactly three retained path links. -/
theorem count_eq_three :
    (cropped.moving.withJoins points.joins.1.val points.joins.2.val).vertices.length = 3 := by
  have vertices := cropped.moving.withJoins_vertices points.joins.1.val points.joins.2.val
  have targets := congrArg
    (fun values : List Canonical => parent.edge.point lower :: (values ++ [parent.edge.point upper]))
    cropped.moving_vertices
  exact congrArg List.length (vertices.trans targets)

/-- Both actual new join payments compose with the retained restricted source-integral payment. -/
theorem integral_le : Norm.Basic.normSq
    ((points.joined.observed.last.value - points.joined.observed.first.value) -
      cropped.models.relation.integralSample) ≤ 8 * accuracy.tolerance + 2 * observed.bound := by
  have decomposition : (points.joined.observed.last.value - points.joined.observed.first.value) -
      cropped.models.relation.integralSample =
      ((points.joined.observed.last.value - points.joined.observed.first.value) -
        (observed.sampled.last.value - observed.sampled.first.value)) +
      ((observed.sampled.last.value - observed.sampled.first.value) -
        cropped.models.relation.integralSample) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct points.joined.increment_error_le observed.integral_le)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end Points

end Observation

variable (prepared lower upper lowerInside upperInside operation)

/-- The actual crop, real restricted models, moving observations and separately paid physical endpoint attachments. -/
@[expose] def Acquisition (comparisonRequest requested : AccuracyRequest) :=
  Σ cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation,
  Σ observed : cropped.Observation (accuracy := accuracy) comparisonRequest,
    observed.Points requested

namespace Acquisition

/-- Execute the actual strict-crop construction once inside the original selected-parent consumer.

Each following stage consumes the exact preceding cached value. The final
existing allocation outcome retains success or an unpaid request; neither
an integral estimate nor a primitive-constant relation is supplied.
-/
def build
    (vertices : ∀ first last, (operation.2 first last).vertices = [parent.edge.point upper])
    (comparisonRequest requested : AccuracyRequest) :
    Acquisition (frame := frame) (basis := basis) (row := row) (accuracy := accuracy)
      prepared lower upper lowerInside upperInside operation comparisonRequest requested :=
  let cropped := Crop.build (frame := frame) (basis := basis) (row := row)
    prepared lower upper lowerInside upperInside operation vertices
  let observed := Observation.build (accuracy := accuracy) cropped comparisonRequest
  let points := Observation.Points.build observed requested
  ⟨cropped, observed, points⟩

end Acquisition

end Crop

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
