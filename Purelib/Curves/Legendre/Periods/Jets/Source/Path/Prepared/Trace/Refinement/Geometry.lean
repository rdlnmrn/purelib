module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine

/-! # Actual rooted child geometry before observing one original materialized trace

The original Subdivision retains each actual View, endpoint query pair and
primitive-cover acquisition before any source or primitive request. The
later numerical fold consumes exactly these geometry caches and the given
old Spine. Whole Trace equality changes only a retained tail's index;
no View, query, root, mesh, cover or observation is rebuilt to extract data.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Actual geometry for every original request in order, independent of old observations and numerical targets.

Each certified head retains its exact original Geometry.build factory.
The next entry is indexed by that SAME head's actual stored suffix Trace.
Zero-width requests retain their own head and both endpoint roles even
though their acquired inner child word is empty.
-/
@[expose] def Geometry (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    PreparedTraceBudget.Trace budget subdivision fits → Type 2
  | _, _, .stop _ _, _, _, _ => PUnit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace =>
      Σ head : {value : Cached.Entry.Geometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (budget := budget) (current := current) (inherited := inherited)
          (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace) centers.1 diameter positive //
        value = Cached.Entry.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (budget := budget) (current := current) (inherited := inherited)
          (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace) centers.1 diameter positive},
      Geometry diameter positive budget remaining centers.2 fits.2.2 head.val.nextTrace
termination_by structural _ _ subdivision _ _ _ => subdivision

namespace Geometry

/-- Acquire each actual original request's rooted primitive-cover geometry once before numerical selection. -/
def build (diameter : Rational) (positive : 0 < diameter) (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
      Geometry (count := count) diameter positive budget subdivision centers fits trace
  | _, _, .stop _ _, _, _, _ => PUnit.unit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace =>
      let head : {value : Cached.Entry.Geometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (budget := budget) (current := current) (inherited := inherited)
          (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace) centers.1 diameter positive //
        value = Cached.Entry.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (budget := budget) (current := current) (inherited := inherited)
          (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace) centers.1 diameter positive} :=
        ⟨Cached.Entry.Geometry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (budget := budget) (current := current) (inherited := inherited)
          (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace) centers.1 diameter positive, rfl⟩
      let following := build diameter positive budget remaining centers.2 fits.2.2 head.val.nextTrace
      ⟨head, following⟩
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Sum literal actual child counts while retaining every original stationary or repeated outer occurrence. -/
@[expose] def childCount (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    Geometry (count := count) diameter positive budget subdivision centers fits trace → Nat
  | _, _, .stop _ _, _, _, _, _ => 0
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, retained =>
      retained.1.val.childCount + childCount diameter positive budget remaining centers.2 fits.2.2
        retained.1.val.nextTrace retained.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

variable {diameter : Rational} {positive : 0 < diameter} {budget : PreparedTraceBudget segment left right}
variable {current : PreparedSheetContinuation.Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {firstTrace lastTrace : PreparedTraceBudget.Trace budget subdivision fits}

/-- Transport the same geometry product through an exact whole Trace identity, without executing any producer. -/
def castTrace (same : firstTrace = lastTrace)
    (retained : Geometry (count := count) diameter positive budget subdivision centers fits firstTrace) :
    Geometry (count := count) diameter positive budget subdivision centers fits lastTrace :=
  Eq.mp (congrArg (fun actual : PreparedTraceBudget.Trace budget subdivision fits =>
    Geometry (count := count) diameter positive budget subdivision centers fits actual) same) retained

/-- Identity transport retains the complete original geometry product without exposing its implementation. -/
theorem castTrace_refl
    (retained : Geometry (count := count) diameter positive budget subdivision centers fits firstTrace) :
    castTrace (Eq.refl firstTrace) retained = retained := by
  unfold castTrace
  rfl

/-- Exact whole Trace transport preserves the literal retained child count. -/
theorem castTrace_childCount (same : firstTrace = lastTrace)
    (retained : Geometry (count := count) diameter positive budget subdivision centers fits firstTrace) :
    childCount diameter positive budget subdivision centers fits lastTrace (castTrace same retained) =
      childCount diameter positive budget subdivision centers fits firstTrace retained := by
  cases same
  rfl

end Geometry

variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {floor : Nat} {accuracy : AccuracyRequest}

/-- Consume retained geometry and the actual old Spine without preparing another View, query or covered block.

Each new source entry uses Entry.fromGeometry and derives its original
Entry.build specification from the retained geometry factory. The actual
old Head split supplies the literal nextObserved. Only exact whole Trace
identity transports the already retained geometry tail to that same suffix.
-/
def fromGeometry (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    Geometry (count := count) diameter positive budget subdivision centers fits trace →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
      Cache (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed
  | _, _, .stop _ _, _, _, _, _, _ => PUnit.unit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace, geometry, observed =>
      let head : {value : Cached.Entry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request //
        value = Cached.Entry.build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request} :=
        ⟨Cached.Entry.fromGeometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request geometry.1.val,
        Cached.Entry.fromGeometry_eq_build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request geometry.1.val geometry.1.property⟩
      have nextTrace : head.val.nextTrace = geometry.1.val.nextTrace :=
        Cached.Entry.fromGeometry_nextTrace (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          (center := centers.1) (row := row) (old := observed) (diameter := diameter)
          (positive := positive) (comparisonRequest := request) geometry.1.val
      let followingGeometry := Geometry.castTrace nextTrace.symm geometry.2
      let following := fromGeometry row diameter positive request budget remaining centers.2 fits.2.2
        head.val.nextTrace followingGeometry head.val.nextObserved
      ⟨head, following⟩
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- The actual numerical fold retains precisely the total child count computed before observing the old trace. -/
theorem fromGeometry_childCount
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
      childCount (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed
        (fromGeometry (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget subdivision centers fits trace geometry observed) =
      Geometry.childCount diameter positive budget subdivision centers fits trace geometry
  | _, _, .stop _ _, _, _, _, _, _ => rfl
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace, geometry, observed => by
      let head := Cached.Entry.fromGeometry (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
        (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
        (remaining := remaining) (fits := fits) (trace := trace)
        centers.1 row observed diameter positive request geometry.1.val
      have nextTrace : head.nextTrace = geometry.1.val.nextTrace :=
        Cached.Entry.fromGeometry_nextTrace (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          (center := centers.1) (row := row) (old := observed) (diameter := diameter)
          (positive := positive) (comparisonRequest := request) geometry.1.val
      let followingGeometry := Geometry.castTrace nextTrace.symm geometry.2
      have firstCount : head.childCount = geometry.1.val.childCount :=
        Cached.Entry.fromGeometry_childCount (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          (center := centers.1) (row := row) (old := observed) (diameter := diameter)
          (positive := positive) (comparisonRequest := request) geometry.1.val
      have followingCount := fromGeometry_childCount
        row diameter positive request budget remaining centers.2 fits.2.2
        head.nextTrace followingGeometry head.nextObserved
      have transportedCount := Geometry.castTrace_childCount (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (diameter := diameter) (positive := positive) (budget := budget)
        (subdivision := remaining) (centers := centers.2) (fits := fits.2.2) nextTrace.symm geometry.2
      change head.childCount + childCount (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget remaining centers.2 fits.2.2 head.nextTrace head.nextObserved
        (fromGeometry (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget remaining centers.2 fits.2.2
          head.nextTrace followingGeometry head.nextObserved) =
        geometry.1.val.childCount +
          Geometry.childCount diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2
      exact congrArg₂ Nat.add firstCount (followingCount.trans transportedCount)
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Cache

end
