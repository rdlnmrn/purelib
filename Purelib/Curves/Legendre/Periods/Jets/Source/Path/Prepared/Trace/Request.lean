module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Subdivision
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Original vertex requests for a retained subdivision comparison

New observation acquisitions compute the actual local accuracy from the
existing source endpoint target. The SAME supplied trace is observed once;
only its exact whole-cache index crosses the original trace-factory equality.
No trace, Owner, original center or source preparation is reconstructed.
Existing observations may instead enter unchanged through explicit equality
of their actual request allocation, as in the original comparison fold.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : Endpoint}

/-- Compute the actual positive old-vertex request scale from the original cached endpoint allocation. -/
@[expose] def localAccuracy (targets : CellEndpoints.Targets original stage) : AccuracyRequest :=
  ⟨targets.endpoint / 4, Order.Field.div_pos_direct targets.endpoint_positive
    (of_decide_eq_true rfl : (0 : Rational) < 4)⟩

/-- The computed local request pays the exact same source endpoint-request index. -/
theorem localAccuracy_allocation (targets : CellEndpoints.Targets original stage) :
    targets.endpoint = 4 * (localAccuracy targets).tolerance := by
  change targets.endpoint = 4 * (targets.endpoint / 4)
  rewrite [Field.mul_comm]
  exact (Field.div_mul_cancel_of_ne targets.endpoint 4 (of_decide_eq_true rfl : (4 : Rational) ≠ 0)).symm

/-- The selected original primitive is defined at every literal vertex of the supplied SAME original trace. -/
theorem defined (row : Row) : ∀ {firstPoint lastPoint : Canonical}
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint)}
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint)}
    (path : OwnerPath (Paths.polynomial parameter) firstPoint firstOwner lastPoint lastOwner),
    Primitive.Defined
      (row.expression parameter) path
  | _, _, _, _, .nil point owner => Row.defined parameter point row owner
  | firstPoint, _, firstOwner, _, .cons _ tail => ⟨Row.defined parameter firstPoint row firstOwner, defined row tail⟩

namespace Request

variable (row : Row)

variable (budget : PreparedTraceBudget segment left right)
variable {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable (subdivision : Subdivision segment within current owner)
variable (fits : budget.RequestsFit current subdivision.requests)
variable {accuracy : AccuracyRequest}
variable (path : OwnerPath (Paths.polynomial parameter) (segment.pointAt current.parameter) owner
  (segment.pointAt subdivision.endpoint.parameter) subdivision.terminalOwner)
variable (path_eq : path = PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)

/-- Transport the complete SAME observation spine through its original whole-trace factory equality.

The actual input path is consumed as data; the factory expression appears
only in dependent indices and the retained equality. The original spine,
requests, stationary comparison outcomes and source/target values cross
together without running either a trace or an observation producer.
-/
@[expose] def castObserved
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy path) :
    Primitive.Spine
      (row.expression parameter)
      accuracy (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits) :=
  path_eq ▸ observed

/-- The original whole observation spine is retained heterogeneously by the exact path-index transport. -/
theorem castObserved_heq
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy path) : HEq (castObserved row budget subdivision fits path path_eq observed) observed := by
  cases path_eq
  rfl

/-- The complete source comparison transport agrees with the original generic Spine path transport. -/
theorem castObserved_eq_castPath
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy path) : castObserved row budget subdivision fits path path_eq observed =
        Primitive.Spine.castPath path_eq observed := by
  cases path_eq
  rfl

/-- Compare an existing old spine after its exact original path-index transport and explicit request allocation.

Every old request remains unchanged. Its target allocation is an intrinsic
index admission, not a final sample or integral bound. The original Source
and complete observation inputs are retained by the existing Compared cache.
-/
def fromObserved
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor) (sheet
      := sheet) subdivision)
    (allocation : targets.endpoint = 4 * accuracy.tolerance)
    (observed : Primitive.Spine
      (row.expression parameter)
      accuracy path) :
    Compared row (frame := frame) (basis := basis) budget allocation subdivision sources fits
      (castObserved row budget subdivision fits path path_eq observed) :=
  compare row (frame := frame) (basis := basis) budget allocation subdivision sources fits (castObserved row budget
    subdivision fits path path_eq observed)

/-- The SAME original path's new observation factory and its exact newly computed comparison cache.

The positive local accuracy is computed internally from the actual source
allocation. The retained observation factory consumes the supplied original
path, then every original moving comparison consumes that literal old spine.
The sources remain the original completed input family throughout.
-/
@[expose] def Acquisition
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor) (sheet
      := sheet) subdivision) :=
  Σ observed : { retained : Primitive.Spine
        (row.expression parameter)
        (localAccuracy targets) path //
      retained = Primitive.Spine.build (accuracy := localAccuracy targets) path (defined row path) },
    Compared row (frame := frame) (basis := basis) budget (localAccuracy_allocation targets) subdivision sources fits
      (castObserved row budget subdivision fits path path_eq observed.val)

/-- Construct one genuinely shrinking observation spine on the SAME original trace and compare each actual moving head.

All denominator guards and the exact endpoint-allocation match are derived
internally. The only supplied path relation is its original whole factory
equality. No new trace, Owner, source selection or aggregate error is given.
-/
def acquire
    (sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor) (sheet
      := sheet) subdivision) :
    Acquisition row (frame := frame) (basis := basis) budget subdivision fits path path_eq sources :=
  let observed := Primitive.Spine.build (accuracy := localAccuracy targets) path (defined row path)
  let compared := fromObserved row (frame := frame) (basis := basis) budget subdivision fits path path_eq sources
    (localAccuracy_allocation targets) observed
  ⟨⟨observed, rfl⟩, compared⟩

namespace Acquisition

variable {row : Row}

variable {sources : Sources (frame := frame) (basis := basis) (targets := targets) (count := count) (floor := floor)
  (sheet := sheet) subdivision}
variable (retained : Acquisition row (frame := frame) (basis := basis) budget subdivision fits path path_eq sources)

/-- Read the complete actual primitive-observation execution on the SAME supplied original path. -/
@[expose] def observed : Primitive.Spine
    (row.expression parameter)
    (localAccuracy targets) path := retained.1.val

/-- Read the whole ordered comparison cache on that exact retained observation execution. -/
@[expose] def compared : Compared row (frame := frame) (basis := basis) budget (localAccuracy_allocation targets)
  subdivision sources fits
    (castObserved row budget subdivision fits path path_eq retained.observed) := retained.2

/-- The retained observation spine is the actual original factory at the internally computed positive request. -/
theorem observed_eq : retained.observed =
    Primitive.Spine.build (accuracy := localAccuracy targets) path (defined row path) := retained.1.property

/-- There is exactly one actual moving error for each request of the SAME retained subdivision. -/
theorem errors_length : retained.compared.errors.length = subdivision.requests.length :=
  retained.compared.errors_length

/-- The original request count and computed allocation pay the sum of the SAME actual moving errors. -/
theorem error_sum_le : Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum retained.compared.errors) ≤
      (subdivision.requests.length : Rational) * ((subdivision.requests.length : Rational) * (12 * targets.endpoint)) :=
  retained.compared.error_sum_le

end Acquisition

end Request

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

end
