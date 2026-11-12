module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Cached.Entry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Materialized
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Refined source integrals on the actual materialized old trace and Spine

The GIVEN original trace and old Spine remain data. Each actual request
reads its three old heads once, retains both old endpoint-query Owners,
and passes the identical actual following trace and old Spine to the tail.
No canonical ownerPath, endpoint transport or old observation factory is
executed to extract a runtime Owner. Both old stationary roles remain.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates edgeOfStep)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- One actual cached-Owner source-refinement entry per old request on the SAME materialized Trace and Spine.

Recursion follows the literal original Subdivision. Every head retains its
actual View, three old Head splits, query Owners and whole source/geometry
factories. The tail consumes the unchanged actual suffix read by that head.
-/
@[expose] def Cache (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    Primitive.Spine (row.expression parameter) accuracy trace.path → Type 2
  | _, _, .stop _ _, _, _, _, _ => PUnit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace, observed =>
      Σ head : {value : Cached.Entry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request //
        value = Cached.Entry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request},
      Cache row diameter positive request budget remaining centers.2 fits.2.2
        head.val.nextTrace head.val.nextObserved
termination_by structural _ _ subdivision _ _ _ _ => subdivision

namespace Cache

/-- Consume the actual stored inherited Owner in each original constructor and pass its literal suffix caches onward. -/
def build (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
      Cache
        (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget subdivision centers fits trace observed
  | _, _, .stop _ _, _, _, _, _ => PUnit.unit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace, observed =>
      let head := Cached.Entry.build (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
        (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
        (remaining := remaining) (fits := fits) (trace := trace)
        centers.1 row observed diameter positive request
      let following := build row diameter positive request budget remaining centers.2 fits.2.2
        head.nextTrace head.nextObserved
      ⟨⟨head, rfl⟩, following⟩
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Read all actual child source integrals in the original moving-request and refined-child order. -/
@[expose] def integrals (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed → List Canonical
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained =>
      retained.1.val.integrals ++ integrals row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Read both original stationary errors and every actual refined-source residual without deleting occurrences. -/
@[expose] def errors (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed → List Canonical
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained =>
      retained.1.val.errors ++ errors row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Read the exact total actual refined child count over all original old request occurrences. -/
@[expose] def childCount (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed → Nat
  | _, _, .stop _ _, _, _, _, _, _ => 0
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained =>
      retained.1.val.childCount + childCount row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Sum the actual source/join charges and both unchanged old stationary allowances per occurrence. -/
@[expose] def charge (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed → Rational
  | _, _, .stop _ _, _, _, _, _, _ => 0
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained =>
      retained.1.val.charge + charge row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Two residuals per actual child and three retained old roles per request give the literal full word length. -/
theorem errors_length (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed) →
      (errors
        (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget subdivision centers fits trace observed retained).length =
        2 * childCount
          (count := count) (floor := floor) (targets := targets)
            row diameter positive request budget subdivision centers fits trace observed retained +
          3 * subdivision.requests.length
  | _, _, .stop _ _, _, _, _, _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained => by
      have head := retained.1.val.errors_length
      have following := errors_length row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
      have append := Data.List.Append.length_append retained.1.val.errors
        (errors
          (count := count) (floor := floor) (targets := targets)
            row diameter positive request budget remaining centers.2 fits.2.2
          retained.1.val.nextTrace retained.1.val.nextObserved retained.2)
      have scalar (head tail requests : Nat) :
          (2 * head + 3) + (2 * tail + 3 * requests) = 2 * (head + tail) + 3 * (requests + 1) := by omega0
      exact (append.trans (congrArg₂ (fun first last : Nat => first + last) head following)).trans
        (scalar _ _ _)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Exact cached-Owner moving and stationary contributions telescope to the unchanged old final-minus-first value. -/
theorem sum_errors (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed) →
      gaussianSum (errors
        (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget subdivision centers fits trace observed retained) =
        observed.last.value - observed.first.value -
          gaussianSum (integrals
            (count := count) (floor := floor) (targets := targets)
              row diameter positive request budget subdivision centers fits trace observed retained)
  | _, _, .stop _ _, _, _, trace, observed, _ => by
      have last := Primitive.Spine.castPath_last_value trace.path_eq observed
      have first := Primitive.Spine.castPath_first_value trace.path_eq observed
      have same : observed.last.value = observed.first.value := last.symm.trans first
      change (0 : Canonical) = observed.last.value - observed.first.value - 0
      rewrite [same]
      ring1
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, observed, retained => by
      have scalar (first middle last head tail : Canonical) :
          (middle - first - head) + (last - middle - tail) = last - first - (head + tail) := by ring1
      have following := sum_errors row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
      have head := retained.1.val.sum_errors
      have last := congrArg Primitive.Vertex.value retained.1.val.nextObserved_last
      change gaussianSum (retained.1.val.errors ++ errors
        (count := count) (floor := floor) (targets := targets) row diameter positive request budget remaining centers.2
        fits.2.2 retained.1.val.nextTrace retained.1.val.nextObserved retained.2) = _
      rewrite [Norm.Sum.Basic.gaussianSum_append, head, following, last]
      calc
        _ = observed.last.value - observed.first.value -
            (gaussianSum retained.1.val.integrals + gaussianSum
              (integrals
                (count := count) (floor := floor) (targets := targets)
                  row diameter positive request budget remaining centers.2 fits.2.2
                retained.1.val.nextTrace retained.1.val.nextObserved retained.2)) := scalar _ _ _ _ _
        _ = _ := (congrArg (fun total : Canonical => observed.last.value - observed.first.value - total)
          (Norm.Sum.Basic.gaussianSum_append _ _)).symm
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Actual retained old requests and SAME source/Point/join caches pay the full finite norm sum. -/
theorem normSum_le (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    (retained : Cache
      (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed) →
      gaussianNormSqSum (errors
        (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget subdivision centers fits trace observed retained) ≤
        charge
          (count := count) (floor := floor) (targets := targets)
            row diameter positive request budget subdivision centers fits trace observed retained
  | _, _, .stop _ _, _, _, _, _, _ => Data.Rat.Fraction.Order.Basic.le_refl 0
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, _observed, retained => by
      have following := normSum_le row diameter positive request budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.1.val.nextObserved retained.2
      have paid := Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct retained.1.val.normSum_le following
      change gaussianNormSqSum (retained.1.val.errors ++ errors
        (count := count) (floor := floor) (targets := targets) row diameter positive request budget remaining
        centers.2 fits.2.2 retained.1.val.nextTrace retained.1.val.nextObserved retained.2) ≤ _
      rewrite [Norm.Sum.Basic.gaussianNormSqSum_append]
      exact paid
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

end Cache

/-- The complete actual source comparison retains the GIVEN trace, centre states and old Spine as runtime data.

The exact whole trace equality transports the same old Spine if its stored
index changes. No canonical ownerPath execution is used. Every original
Vertex, observation request, denotation and stationary comparison survives.
-/
@[expose] def Compared (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) {current : PreparedSheetContinuation.Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) :=
  Σ keptCenters : {value : CenterStates (Fibre.frameCurve frame) basis sheet subdivision // value = centers},
  Σ keptTrace : {value : PreparedTraceBudget.Trace budget subdivision fits // value = trace},
  Σ keptObserved : {value : Primitive.Spine (row.expression parameter) accuracy keptTrace.val.path //
    value = Primitive.Spine.castPath (congrArg PreparedTraceBudget.Trace.path keptTrace.property).symm observed},
  {value : Cache (count := count) (floor := floor) (targets := targets) row diameter positive request budget
      subdivision keptCenters.val fits keptTrace.val keptObserved.val //
    value = Cache.build (count := count) (floor := floor) (targets := targets) row diameter positive request budget
      subdivision keptCenters.val fits keptTrace.val keptObserved.val}

/-- Refine the SAME actual materialized old trace and retain its complete unchanged old observation execution. -/
def compare (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) {current : PreparedSheetContinuation.Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) :
    Compared (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed :=
  let retained := Cache.build (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed
  ⟨⟨centers, rfl⟩, ⟨trace, rfl⟩, ⟨observed, rfl⟩, ⟨retained, rfl⟩⟩

namespace Compared

variable {row : Row} {diameter : Rational} {positive : 0 < diameter} {request : AccuracyRequest}
variable {budget : PreparedTraceBudget segment left right} {current : PreparedSheetContinuation.Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {originalCenters : CenterStates (Fibre.frameCurve frame) basis sheet subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {trace : PreparedTraceBudget.Trace budget subdivision fits}
variable {observed : Primitive.Spine (row.expression parameter) accuracy trace.path}
variable (retained : Compared (count := count) (floor := floor) (targets := targets)
  row diameter positive request budget subdivision originalCenters fits trace observed)

/-- Read the SAME supplied centre states without rebuilding any centre preparation. -/
@[expose] def centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision := retained.1.val

/-- Read the SAME supplied materialized original Trace and all its actual OwnerPath caches. -/
@[expose] def actualTrace : PreparedTraceBudget.Trace budget subdivision fits := retained.2.1.val

/-- The whole original centre product remains unchanged. -/
theorem centers_eq : retained.centers = originalCenters := retained.1.property

/-- The whole supplied materialized trace remains unchanged. -/
theorem actualTrace_eq : retained.actualTrace = trace := retained.2.1.property

/-- Read the SAME entire old observation execution at its exactly retained trace index. -/
@[expose] def observations : Primitive.Spine (row.expression parameter) accuracy retained.actualTrace.path :=
  retained.2.2.1.val

/-- The old observations only cross the exact whole trace-index equality. -/
theorem observations_eq : retained.observations =
    Primitive.Spine.castPath (congrArg PreparedTraceBudget.Trace.path retained.actualTrace_eq).symm observed :=
  retained.2.2.1.property

/-- The whole old Vertex/request/observation execution remains the SAME supplied data heterogeneously. -/
theorem observations_heq : HEq retained.observations observed :=
  (heq_of_eq retained.observations_eq).trans (Primitive.Spine.castPath_heq _ _)

/-- Read the actual ordered cached-endpoint source executions without replaying any parent or observation. -/
@[expose] def completed : Cache
  (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision retained.centers fits
    retained.actualTrace retained.observations := retained.2.2.2.val

/-- Every actual source execution has its exact original factory on the retained old trace/Spine data. -/
theorem completed_eq : retained.completed = Cache.build
  (count := count) (floor := floor) (targets := targets) row diameter positive request budget subdivision
    retained.centers fits retained.actualTrace retained.observations := retained.2.2.2.property

/-- Read actual source samples in original request/child order. -/
@[expose] def integrals : List Canonical := Cache.integrals
  (count := count) (floor := floor) (targets := targets) row diameter positive request budget subdivision
  retained.centers fits retained.actualTrace retained.observations retained.completed

/-- Read the actual signed residuals, including both original stationary roles per request. -/
@[expose] def errors : List Canonical := Cache.errors
  (count := count) (floor := floor) (targets := targets) row diameter positive request budget subdivision
  retained.centers fits retained.actualTrace retained.observations retained.completed

/-- Read the exact total number of SAME actual refined children. -/
@[expose] def childCount : Nat := Cache.childCount
  (count := count) (floor := floor) (targets := targets) row diameter positive request budget subdivision
  retained.centers fits retained.actualTrace retained.observations retained.completed

/-- Read the actual derived old/new request charge without claiming an arbitrary requested global target. -/
@[expose] def charge : Rational := Cache.charge
  (count := count) (floor := floor) (targets := targets) row diameter positive request budget subdivision
  retained.centers fits retained.actualTrace retained.observations retained.completed

/-- Read the exact full residual count from SAME child and original request occurrences. -/
@[expose] def residualCount : Nat := 2 * retained.childCount + 3 * subdivision.requests.length

/-- The actual residual count retains every real stationary or repeated original request. -/
theorem residualCount_eq : retained.residualCount =
    2 * retained.childCount + 3 * subdivision.requests.length := rfl

/-- Full original request and child occurrences determine the exact finite residual count. -/
theorem errors_length : retained.errors.length = retained.residualCount :=
  Cache.errors_length
    (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision retained.centers fits
    retained.actualTrace retained.observations retained.completed

/-- The unchanged old first reading survives the exact whole-trace index transport. -/
theorem first_value : retained.observations.first.value = observed.first.value :=
  (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy retained.actualTrace.path =>
    old.first.value) retained.observations_eq).trans (Primitive.Spine.castPath_first_value _ _)

/-- The independent unchanged old terminal reading survives the same exact trace transport. -/
theorem last_value : retained.observations.last.value = observed.last.value :=
  (congrArg (fun old : Primitive.Spine (row.expression parameter) accuracy retained.actualTrace.path =>
    old.last.value) retained.observations_eq).trans (Primitive.Spine.castPath_last_value _ _)

/-- Actual source residuals preserve the literal old terminal-minus-first contribution. -/
theorem sum_errors : gaussianSum retained.errors = observed.last.value - observed.first.value -
    gaussianSum retained.integrals :=
  (Cache.sum_errors
    (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision retained.centers fits
    retained.actualTrace retained.observations retained.completed).trans
      (congrArg₂ (fun first last : Canonical => last - first - gaussianSum retained.integrals)
        retained.first_value retained.last_value)

/-- All actual old stationary and new source/join caches pay the finite norm sum. -/
theorem normSum_le : gaussianNormSqSum retained.errors ≤ retained.charge :=
  Cache.normSum_le
    (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision retained.centers fits
    retained.actualTrace retained.observations retained.completed

/-- The actual old primitive increment differs from the actual refined source sum by a fully derived finite charge. -/
theorem integral_error_le : Norm.Basic.normSq
    (observed.last.value - observed.first.value - gaussianSum retained.integrals) ≤
      ((2 * retained.childCount + 3 * subdivision.requests.length : Nat) : Rational) * retained.charge := by
  have cauchy := (Norm.Basic.normSq_eq_canonical (gaussianSum retained.errors)).trans_le
    (Norm.Sum.Basic.normSq_gaussianSum_le retained.errors)
  have normEq := congrArg Norm.Basic.normSq retained.sum_errors
  have paid := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct retained.normSum_le
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le retained.errors.length))
  have bound := normEq.symm.trans_le (cauchy.trans paid)
  exact bound.trans_eq (congrArg (fun length : Nat => (length : Rational) * retained.charge) retained.errors_length)

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

end
