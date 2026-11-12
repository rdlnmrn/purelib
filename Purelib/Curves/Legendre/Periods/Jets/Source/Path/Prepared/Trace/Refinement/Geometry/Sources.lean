module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Comparison
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Integrals

/-! # One six-channel source bank on the literal given raw geometry

Sources are prepared once per actual refined head after targets exist and
before primitive observations. All row consumers read the same full bank;
old View splits, cached endpoint Owners and literal Trace suffixes survive.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

open Cached.Entry.Geometry renaming Sources -> CachedSources
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {left right : PreparedSheetContinuation.Endpoint} {accuracy : AccuracyRequest}

namespace Cache
namespace Geometry

/-- The SAME certified source product at every literal given geometry head, independent of all row observations.

Both stationary outer roles remain positions of the geometry product;
their source component is unit. Each strict head owns its actual full
six-channel source product on the exact retained successful inspection.
-/
@[expose] def Sources (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    Geometry (count := count) diameter positive budget subdivision centers fits trace → Type 2
  | _, _, .stop _ _, _, _, _, _ => PUnit
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      CachedSources (count := count) (floor := floor) (targets := targets) geometry.1.val ×
        Sources diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

namespace Sources

/-- Prepare every actual six-channel source product once on the GIVEN ordered geometry without observing any row. -/
def build (diameter : Rational) (positive : 0 < diameter) (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
      Sources (count := count) (floor := floor) (targets := targets)
        diameter positive budget subdivision centers fits trace geometry
  | _, _, .stop _ _, _, _, _, _ => PUnit.unit
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry =>
      let head := CachedSources.build
        (count := count) (floor := floor) (targets := targets) geometry.1.val
      let following := build diameter positive budget remaining centers.2 fits.2.2
        geometry.1.val.nextTrace geometry.2
      ⟨head, following⟩
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Flatten one literal differential-cell list in original request and refined-child order. -/
@[expose] def cells (channel : Fin 6) (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry →
      List CellModel
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry, shared =>
      CachedSources.cells (count := count) (floor := floor) (targets := targets)
        geometry.1.val channel shared.1 ++
      cells channel diameter positive budget remaining centers.2 fits.2.2 geometry.1.val.nextTrace geometry.2 shared.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Read the literal supplied row-model samples in original request/child order without observing any Point. -/
@[expose] def integrals (row : Row) (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry → List Canonical
  | _, _, .stop _ _, _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry, shared =>
      CachedSources.integrals (count := count) (floor := floor) (targets := targets)
          geometry.1.val row shared.1 ++
        integrals row diameter positive budget remaining centers.2 fits.2.2
          geometry.1.val.nextTrace geometry.2 shared.2
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

/-- Every actual raw row sum is the exact original linear combination of its SAME six stored cell lists. -/
theorem combine_eq (row : Row) (diameter : Rational) (positive : 0 < diameter)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry) →
    gaussianSum (integrals row diameter positive budget subdivision centers fits trace geometry shared) =
      Row.combine parameter row (fun channel =>
        (PathModel.mk (cells channel diameter positive budget subdivision centers fits
          trace geometry shared)).integralSample)
  | _, _, .stop _ _, _, _, _, _, _ => (Row.combine_zero parameter row).symm
  | _, _, .next _ _ _ _ _ _ remaining, centers, fits, _trace, geometry, shared => by
      have first := CachedSources.combine_eq
        (count := count) (floor := floor) (targets := targets) geometry.1.val row shared.1
      have last := combine_eq row diameter positive budget remaining centers.2 fits.2.2
        geometry.1.val.nextTrace geometry.2 shared.2
      have added := Row.combine_add parameter row
        (fun channel => (PathModel.mk (CachedSources.cells
          (count := count) (floor := floor) (targets := targets) geometry.1.val channel shared.1)).integralSample)
        (fun channel => (PathModel.mk (cells channel diameter positive budget remaining centers.2 fits.2.2
          geometry.1.val.nextTrace geometry.2 shared.2)).integralSample)
      have lists := Row.combine_congr parameter row _ _ (fun channel =>
        (PathModel.integralSample_mk_append
          (CachedSources.cells (count := count) (floor := floor) (targets := targets)
            geometry.1.val channel shared.1)
          (cells channel diameter positive budget remaining centers.2 fits.2.2
            geometry.1.val.nextTrace geometry.2 shared.2)).symm)
      exact (gaussianSum_append _ _).trans
        ((congrArg₂ (fun first last : Canonical => first + last) first last).trans (added.symm.trans lists))
termination_by structural _ _ subdivision _ _ _ _ _ => subdivision

variable {diameter : Rational} {positive : 0 < diameter} {budget : PreparedTraceBudget segment left right}
variable {current : PreparedSheetContinuation.Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {firstTrace lastTrace : PreparedTraceBudget.Trace budget subdivision fits}

/-- Whole Trace equality transports the SAME bank with its actual geometry; it prepares no source or owner. -/
def castTrace (same : firstTrace = lastTrace)
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits firstTrace)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits firstTrace geometry) :
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits lastTrace (Geometry.castTrace same geometry) := by
  cases same
  exact Eq.mpr (congrArg (fun actualGeometry :
      Geometry (count := count) diameter positive budget subdivision centers fits firstTrace =>
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits firstTrace actualGeometry)
    (Geometry.castTrace_refl geometry)) shared

/-- Whole Trace transport preserves the SAME actual source-bank row integral list. -/
theorem castTrace_integrals (same : firstTrace = lastTrace)
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits firstTrace)
    (shared : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits firstTrace geometry) (row : Row) :
    integrals row diameter positive budget subdivision centers fits lastTrace (Geometry.castTrace same geometry)
        (castTrace (count := count) (floor := floor) (targets := targets) same geometry shared) =
      integrals row diameter positive budget subdivision centers fits firstTrace geometry shared := by
  have transport : ∀ (first last : Geometry (count := count)
      diameter positive budget subdivision centers fits firstTrace) (equal : first = last)
      (values : Sources (count := count) (floor := floor) (targets := targets)
        diameter positive budget subdivision centers fits firstTrace last),
      integrals row diameter positive budget subdivision centers fits firstTrace first
        (Eq.mpr (congrArg (fun actual => Sources (count := count) (floor := floor) (targets := targets)
          diameter positive budget subdivision centers fits firstTrace actual) equal) values) =
      integrals row diameter positive budget subdivision centers fits firstTrace last values := by
    intro first last equal values
    cases equal
    rfl
  cases same
  unfold castTrace
  exact transport _ _ (Geometry.castTrace_refl geometry) shared

end Sources
end Geometry

/-- Consume the GIVEN complete source bank for one original row, preserving its literal old suffixes and factories.

The new fold reads no source factory. Each actual original Entry consumes
its given source head, and exact Trace equality transports the same stored
tail to its retained nextObserved. Both stationary old roles survive.
-/
def fromSources (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
      Cache (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace observed
  | _, _, .stop _ _, _, _, _, _, _, _ => PUnit.unit
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace,
      geometry, shared, observed =>
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
        ⟨Cached.Entry.fromSources (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request geometry.1.val shared.1,
        (Cached.Entry.fromSources_eq_fromGeometry (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request geometry.1.val shared.1).trans
        (Cached.Entry.fromGeometry_eq_build (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          centers.1 row observed diameter positive request geometry.1.val geometry.1.property)⟩
      have nextTrace : head.val.nextTrace = geometry.1.val.nextTrace :=
        Cached.Entry.fromSources_nextTrace (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          (center := centers.1) (row := row) (old := observed) (diameter := diameter)
          (positive := positive) (comparisonRequest := request) geometry.1.val shared.1
      let followingGeometry := Geometry.castTrace nextTrace.symm geometry.2
      let followingSources := Geometry.Sources.castTrace nextTrace.symm geometry.2 shared.2
      let following := fromSources row diameter positive request budget remaining centers.2 fits.2.2
        head.val.nextTrace followingGeometry followingSources head.val.nextObserved
      ⟨head, following⟩
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

/-- The actual given-bank numerical row cache reads its literal supplied model-integral list in order. -/
theorem fromSources_integrals (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right) :
    {current : PreparedSheetContinuation.Endpoint} →
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))} →
    (subdivision : Subdivision segment within current owner) →
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision) →
    (fits : budget.RequestsFit current subdivision.requests) →
    (trace : PreparedTraceBudget.Trace budget subdivision fits) →
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace) →
    (shared : Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry) →
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) →
    integrals (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed
      (fromSources (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace geometry shared observed) =
      Geometry.Sources.integrals row diameter positive budget subdivision centers fits trace geometry shared
  | _, _, .stop _ _, _, _, _, _, _, _ => rfl
  | _, _, .next current inherited step cached ordered small remaining, centers, fits, trace,
      geometry, shared, observed => by
      let head := Cached.Entry.fromSources (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
        (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
        (remaining := remaining) (fits := fits) (trace := trace)
        centers.1 row observed diameter positive request geometry.1.val shared.1
      have nextTrace : head.nextTrace = geometry.1.val.nextTrace :=
        Cached.Entry.fromSources_nextTrace (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
          (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
          (remaining := remaining) (fits := fits) (trace := trace)
          (center := centers.1) (row := row) (old := observed) (diameter := diameter)
          (positive := positive) (comparisonRequest := request) geometry.1.val shared.1
      let followingGeometry := Geometry.castTrace nextTrace.symm geometry.2
      let followingSources := Geometry.Sources.castTrace nextTrace.symm geometry.2 shared.2
      have first := Cached.Entry.fromSources_integrals (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (floor := floor) (targets := targets) (budget := budget) (current := current)
        (inherited := inherited) (request := step) (cached := cached) (ordered := ordered) (small := small)
        (remaining := remaining) (fits := fits) (trace := trace)
        (center := centers.1) (row := row) (old := observed) (diameter := diameter)
        (positive := positive) (comparisonRequest := request) geometry.1.val shared.1
      have last := fromSources_integrals row diameter positive request budget remaining centers.2 fits.2.2
        head.nextTrace followingGeometry followingSources head.nextObserved
      have transported := Geometry.Sources.castTrace_integrals
        (count := count) (floor := floor) (targets := targets) nextTrace.symm geometry.2 shared.2 row
      change head.integrals ++ integrals (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget remaining centers.2 fits.2.2 head.nextTrace head.nextObserved
        (fromSources (count := count) (floor := floor) (targets := targets)
          row diameter positive request budget remaining centers.2 fits.2.2
          head.nextTrace followingGeometry followingSources head.nextObserved) = _
      exact congrArg₂ List.append first (last.trans transported)
termination_by structural _ _ subdivision _ _ _ _ _ _ => subdivision

/-- The GIVEN-bank numerical fold retains exactly the child count of the SAME pre-observation geometry.

The existing complete Entry factories identify two typed raw caches in an
erased proof. Only their scalar count projection is transported; no old
source producer is executed and no desired count is assumed.
-/
theorem fromSources_childCount
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (budget : PreparedTraceBudget segment left right)
    {current : PreparedSheetContinuation.Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
    (fits : budget.RequestsFit current subdivision.requests)
    (trace : PreparedTraceBudget.Trace budget subdivision fits)
    (geometry : Geometry (count := count) diameter positive budget subdivision centers fits trace)
    (sourceBank : Geometry.Sources (count := count) (floor := floor) (targets := targets)
      diameter positive budget subdivision centers fits trace geometry)
    (observed : Primitive.Spine (row.expression parameter) accuracy trace.path) :
    childCount (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed
      (fromSources (count := count) (floor := floor) (targets := targets)
        row diameter positive request budget subdivision centers fits trace geometry sourceBank observed) =
      Geometry.childCount diameter positive budget subdivision centers fits trace geometry := by
  have same := eq_of_factories (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed
    (fromSources (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry sourceBank observed)
    (fromGeometry (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry observed)
  have read := congrArg (fun actual : Cache (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed =>
    childCount (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed actual) same
  exact read.trans (fromGeometry_childCount (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry observed)

end Cache

variable (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
variable (budget : PreparedTraceBudget segment left right) {current : PreparedSheetContinuation.Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable (subdivision : Subdivision segment within current owner)
variable (centers : CenterStates (Fibre.frameCurve frame) basis sheet subdivision)
variable (fits : budget.RequestsFit current subdivision.requests)
variable (trace : PreparedTraceBudget.Trace budget subdivision fits)
variable (geometry : Cache.Geometry (count := count) diameter positive budget subdivision centers fits trace)
variable (shared : Cache.Geometry.Sources (count := count) (floor := floor) (targets := targets)
  diameter positive budget subdivision centers fits trace geometry)
variable (observed : Primitive.Spine (row.expression parameter) accuracy trace.path)

/-- Retain the original complete comparison using the GIVEN source bank without running an independent source fold. -/
def compareFromSources : Compared (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed :=
  let retained := Cache.fromSources (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry shared observed
  have factory := Cache.eq_of_factories (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed retained
    (Cache.build (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace observed)
  ⟨⟨centers, rfl⟩, ⟨trace, rfl⟩, ⟨observed, rfl⟩, ⟨retained, factory⟩⟩

/-- The original Compared wrapper reads exactly the integral list of its SAME given source bank. -/
theorem compareFromSources_integrals :
    (compareFromSources (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry shared observed).integrals =
      Cache.Geometry.Sources.integrals row diameter positive budget subdivision centers fits trace geometry shared := by
  change Cache.integrals (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed
    (Cache.fromSources (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry shared observed) = _
  exact Cache.fromSources_integrals (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry shared observed

/-- The original Compared result reads exactly the child count of its SAME actual supplied geometry bank. -/
theorem compareFromSources_childCount :
    (compareFromSources (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry shared observed).childCount =
      Cache.Geometry.childCount diameter positive budget subdivision centers fits trace geometry := by
  change Cache.childCount (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace observed
    (Cache.fromSources (count := count) (floor := floor) (targets := targets)
      row diameter positive request budget subdivision centers fits trace geometry shared observed) = _
  exact Cache.fromSources_childCount (count := count) (floor := floor) (targets := targets)
    row diameter positive request budget subdivision centers fits trace geometry shared observed

/-- Three independent original row observations consume ONE complete supplied raw source bank.

All row-specific primitive observations and signed joins remain independent.
The actual geometry, successful cover, six-model source products and raw
Trace suffixes are shared; no source preparation occurs in this consumer.
-/
def rowsFromSources
    (observations : (row : Row) → Primitive.Spine (row.expression parameter) accuracy trace.path) :
    Compared (count := count) (floor := floor) (targets := targets)
        (Row.connection 0) diameter positive request budget subdivision centers fits trace
          (observations (Row.connection 0)) ×
      Compared (count := count) (floor := floor) (targets := targets)
        (Row.connection 1) diameter positive request budget subdivision centers fits trace
          (observations (Row.connection 1)) ×
      Compared (count := count) (floor := floor) (targets := targets)
        Row.scalar diameter positive request budget subdivision centers fits trace (observations Row.scalar) :=
  let zero := compareFromSources (count := count) (floor := floor) (targets := targets)
    (Row.connection 0) diameter positive request budget subdivision centers fits trace geometry shared
    (observations (Row.connection 0))
  let one := compareFromSources (count := count) (floor := floor) (targets := targets)
    (Row.connection 1) diameter positive request budget subdivision centers fits trace geometry shared
    (observations (Row.connection 1))
  let scalar := compareFromSources (count := count) (floor := floor) (targets := targets)
    Row.scalar diameter positive request budget subdivision centers fits trace geometry shared (observations Row.scalar)
  ⟨zero, one, scalar⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement

end
