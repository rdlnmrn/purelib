module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Endpoints
public import Purelib.Riemann.Paths.PreparedTraceEdges.Queries
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Literal accepted-parent lookup for an original query-to-query crop

One structural lookup follows the actual stored View.tailTrace and the
identical center tail. Its selected accepted parent supplies the original
fit certificates to the intrinsic query crop. No new subdivision, trace,
source preparation, query or parent selection is executed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

namespace PreparedTraceBudget.Trace

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint StepRequest CachedSource)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenteredEdge CenterStates centeredEdges centeredEdges_length edgeOfStep)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedTraceEdges
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}

/-- The exact two supplied Query Owners and original physical parent index determine the crop's endpoint contract. -/
@[expose] def CropOperation (parent : CenteredEdge curve differential) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) :=
  (source : PreparedEdge.Query parent.edge lower lowerInside) →
    (target : PreparedEdge.Query parent.edge upper upperInside) →
      OwnerPath curve.polynomial (parent.edge.point lower) source.owner (parent.edge.point upper) target.owner

/-- The original endpoint comparison cache and new crop operation share the same selected actual View. -/
@[expose] def CropComparisons (parent : CenteredEdge curve differential) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) :=
  EndpointComparisons parent × CropOperation parent lower upper lowerInside upperInside

/-- Original query-to-query crop operations from one fixed fractional source on the same retained parent. -/
abbrev CropFamily (parent : CenteredEdge curve differential) (lower : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) :=
  (upper : Rational) → (upperInside : 0 ≤ upper ∧ upper ≤ 1) → lower ≤ upper →
    CropOperation parent lower upper lowerInside upperInside

namespace CropFamily

/-- A retained operation family with the literal one-target incidence of each actual cropped path. -/
abbrev Checked (parent : CenteredEdge curve differential) (lower : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) :=
  {paths : CropFamily parent lower lowerInside //
    ∀ upper upperInside ordered source target,
      (paths upper upperInside ordered source target).vertices = [parent.edge.point upper]}

/-- Checked original-parent crops with every admitted fractional source retained as an executable family. -/
abbrev All (parent : CenteredEdge curve differential) :=
  (lower : Rational) → (lowerInside : 0 ≤ lower ∧ lower ≤ 1) → Checked parent lower lowerInside

end CropFamily

section Accepted

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {accepted : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached accepted small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached accepted small remaining) fits}

namespace View

variable (view : View budget current inherited request cached accepted small remaining fits trace)
variable (center : PreparedEdge.CenterState
  (edgeOfStep curve differential segment within current inherited request cached accepted small sheet))

/-- Construct the endpoint product and crop operation from this same already-selected accepted View.

The original budget and actual fit certificates determine the query path.
The operation does not select another View or execute either endpoint
comparison or query path. Its body is exposed for the original cropAt head
equation, whose whole constructor expression is preserved.
-/
@[expose] def cropComparisons
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper) :
    CropComparisons
      (⟨edgeOfStep curve differential segment within current inherited request cached accepted small sheet,
        center⟩ : CenteredEdge curve differential) lower upper lowerInside upperInside :=
  ⟨view.endpointComparisons center,
    fun source target => PreparedTraceEdges.PreparedTraceBudget.queryPath
      (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
      budget fits.1 fits.2.1 lower upper lowerInside upperInside ordered source target⟩

/-- Every execution of this same retained crop operation has its literal one-target occurrence list. -/
theorem cropComparisons_vertices
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper)
    (source : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
      lower lowerInside)
    (target : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
      upper upperInside) :
    ((view.cropComparisons center lower upper lowerInside upperInside ordered).2 source target).vertices =
      [(edgeOfStep curve differential segment within
        current inherited request cached accepted small sheet).point upper] :=
  PreparedTraceEdges.PreparedTraceBudget.queryPath_vertices
    (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
    budget fits.1 fits.2.1 lower upper lowerInside upperInside ordered source target

/-- Retain the SAME selected View as a productive family of actual later query crops.

The supplied query Owners are consumed directly by the original queryPath
operation. Constructing this closure executes no Query, path, source model
or endpoint comparison. Each later call constructs its actual one-target
path using that same retained View's original budget and fit certificates.
-/
def cropFrom (lower : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) :
    CropFamily.Checked
      (⟨edgeOfStep curve differential segment within current inherited request cached accepted small sheet,
        center⟩ : CenteredEdge curve differential) lower lowerInside :=
  ⟨fun upper upperInside ordered =>
      (view.cropComparisons center lower upper lowerInside upperInside ordered).2,
    fun upper upperInside ordered source target =>
      view.cropComparisons_vertices center lower upper lowerInside upperInside ordered source target⟩

/-- An actual retained family application is the original crop operation of that SAME selected View. -/
theorem cropFrom_apply (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (source : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
      lower lowerInside)
    (target : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
      upper upperInside) :
    (view.cropFrom center lower lowerInside).val upper upperInside ordered source target =
      (view.cropComparisons center lower upper lowerInside upperInside ordered).2 source target := by
  unfold cropFrom
  rfl

/-- Retain the SAME selected View for actual crops between any two admitted ordered child fractions.

This closure selects no new View and executes no Query or path. A later
application supplies its two literal retained Query Owners directly to the
original cropFrom/queryPath operation with the same budget and fit proofs.
-/
def cropFamilies : CropFamily.All
    (⟨edgeOfStep curve differential segment within current inherited request cached accepted small sheet,
      center⟩ : CenteredEdge curve differential) :=
  fun lower lowerInside => view.cropFrom center lower lowerInside

/-- Each retained source-family application is the original same-View cropFrom cache constructor. -/
theorem cropFamilies_apply (lower : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) :
    view.cropFamilies center lower lowerInside = view.cropFrom center lower lowerInside := by
  unfold cropFamilies
  rfl

end View

end Accepted

/-- Construct the accepted child's actual query-to-query crop through one finite lookup on the SAME physical Trace.

Each visited prefix extracts its actual View once. A successor passes its
unchanged tailTrace with centers.2; the selected head retains the SAME
endpoint-comparison product and derives the query crop from its original
request-fit bounds and cached prepared source.
-/
def cropAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper) :
    CropComparisons ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt)
      lower upper lowerInside upperInside :=
  atParent
    (fun parent => CropComparisons parent lower upper lowerInside upperInside)
    (fun view center => view.cropComparisons center lower upper lowerInside upperInside ordered)
    trace centers index

section Readbacks

variable {current : Endpoint}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {accepted : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached accepted small remaining).requests}
variable (trace : Trace budget (Subdivision.next current inherited request cached accepted small remaining) fits)
variable (centers : CenterStates curve differential sheet
  (Subdivision.next current inherited request cached accepted small remaining))
variable (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
variable (ordered : lower ≤ upper)

/-- The actual head crop is the complete intrinsic factory on the same accepted request and supplied Queries. -/
theorem cropAt_head : cropAt trace centers ⟨0, Nat.zero_lt_succ _⟩ lower upper lowerInside upperInside ordered =
    ⟨(View.build trace).endpointComparisons centers.1,
      fun source target => PreparedTraceEdges.PreparedTraceBudget.queryPath
        (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
        budget fits.1 fits.2.1 lower upper lowerInside upperInside ordered source target⟩ := by
  unfold cropAt
  rewrite [atParent_head]
  rfl

/-- A successor crop passes the SAME literal tailTrace and original center tail without reconstructing either. -/
theorem cropAt_succ (index : Fin (centeredEdges curve differential sheet remaining centers.2).length) :
    cropAt trace centers index.succ lower upper lowerInside upperInside ordered =
      cropAt (View.build trace).tailTrace centers.2 index lower upper lowerInside upperInside ordered := by
  unfold cropAt
  rewrite [atParent_succ]
  rfl

end Readbacks

/-- The crop lookup retains the complete original endpoint product, including all actual Owner witnesses.

The proof follows the same literal tailTrace. It compares whole products,
not scalar names or extensional projections of the comparison functions.
No endpoint comparison is executed to construct the crop.
-/
theorem cropAt_endpoints {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper) :
    (cropAt trace centers index lower upper lowerInside upperInside ordered).1 = endpointsAt trace centers index :=
  Subdivision.rec
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      (cropAt trace centers index lower upper lowerInside upperInside ordered).1 = endpointsAt trace centers index)
    (fun current inherited _fits _trace centers index => by
      have count := (centeredEdges_length curve differential sheet
        (Subdivision.stop (segment := segment) (within := within) current inherited) centers).trans
          (Subdivision.stepCount_stop current inherited)
      exact Fin.elim0 (Fin.cast count index))
    (fun current inherited request cached accepted small remaining ih fits trace centers index => by
      change PreparedEdge.CenterState
          (edgeOfStep curve differential segment within current inherited request cached accepted small sheet) ×
        CenterStates curve differential sheet remaining at centers
      exact Fin.cases (n := (centeredEdges curve differential sheet remaining centers.2).length)
        (motive := fun index =>
          (cropAt trace centers index lower upper lowerInside upperInside ordered).1 =
            endpointsAt trace centers index)
        (by
          have first := congrArg Prod.fst
            (cropAt_head trace centers lower upper lowerInside upperInside ordered)
          exact first.trans (endpointsAt_head trace centers).symm)
        (fun next => by
          have first := congrArg Prod.fst
            (cropAt_succ trace centers lower upper lowerInside upperInside ordered next)
          have middle := ih fits.2.2 (View.build trace).tailTrace centers.2 next
          exact first.trans (middle.trans (endpointsAt_succ trace centers next).symm)) index)
    subdivision fits trace centers index

namespace CropComparisons

/-- Reindex the same complete crop cache along an exact equality of its original parent.

Only the nominal parent index changes. The endpoint comparisons and the
query-crop closure remain the supplied values, without another lookup.
-/
def cast {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} {first last : CenteredEdge curve differential}
    {lower upper : Rational} {lowerInside : 0 ≤ lower ∧ lower ≤ 1}
    {upperInside : 0 ≤ upper ∧ upper ≤ 1} (same : first = last)
    (physical : CropComparisons first lower upper lowerInside upperInside) :
    CropComparisons last lower upper lowerInside upperInside :=
  Eq.mp (congrArg (fun parent : CenteredEdge curve differential =>
    CropComparisons parent lower upper lowerInside upperInside) same) physical

/-- Whole original parent reindexing preserves a supplied literal crop vertex law.

The equality eliminates independent whole parent indices. It neither
selects a child nor executes either endpoint comparison or query crop.
-/
theorem cast_vertices {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} {first last : CenteredEdge curve differential}
    {lower upper : Rational} {lowerInside : 0 ≤ lower ∧ lower ≤ 1}
    {upperInside : 0 ≤ upper ∧ upper ≤ 1} (same : first = last)
    (physical : CropComparisons first lower upper lowerInside upperInside)
    (vertices : ∀ source target, (physical.2 source target).vertices = [first.edge.point upper])
    (source : PreparedEdge.Query last.edge lower lowerInside)
    (target : PreparedEdge.Query last.edge upper upperInside) :
    ((cast same physical).2 source target).vertices = [last.edge.point upper] := by
  unfold cast
  cases same
  exact vertices source target

end CropComparisons

/-- The selected crop keeps its literal target occurrence through every original View tail.

Only the selected intrinsic crop's vertex readback is used. The proof
follows the same stored tailTrace and center tail; no operational endpoint
comparison or second physical selection is executed to construct data.
-/
theorem cropAt_vertices {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision)
    (index : Fin (centeredEdges curve differential sheet subdivision centers).length)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper)
    (source : PreparedEdge.Query
      ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge lower lowerInside)
    (target : PreparedEdge.Query
      ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge upper upperInside) :
    ((cropAt trace centers index lower upper lowerInside upperInside ordered).2 source target).vertices =
      [((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge.point upper] :=
  Subdivision.rec
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length) →
      (source : PreparedEdge.Query
        ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge lower lowerInside) →
      (target : PreparedEdge.Query
        ((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge upper upperInside) →
      ((cropAt trace centers index lower upper lowerInside upperInside ordered).2 source target).vertices =
        [((centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt).edge.point upper])
    (fun current inherited _fits _trace centers index => by
      have count := (centeredEdges_length curve differential sheet
        (Subdivision.stop (segment := segment) (within := within) current inherited) centers).trans
          (Subdivision.stepCount_stop current inherited)
      exact Fin.elim0 (Fin.cast count index))
    (fun current inherited request cached accepted small remaining ih fits trace centers index => by
      change PreparedEdge.CenterState
          (edgeOfStep curve differential segment within current inherited request cached accepted small sheet) ×
        CenterStates curve differential sheet remaining at centers
      exact Fin.cases (n := (centeredEdges curve differential sheet remaining centers.2).length)
        (motive := fun index =>
          (source : PreparedEdge.Query
            ((centeredEdges curve differential sheet
              (Subdivision.next current inherited request cached accepted small remaining)
                centers)[index.val]'index.isLt).edge lower lowerInside) →
          (target : PreparedEdge.Query
            ((centeredEdges curve differential sheet
              (Subdivision.next current inherited request cached accepted small remaining)
                centers)[index.val]'index.isLt).edge upper upperInside) →
          ((cropAt trace centers index lower upper lowerInside upperInside ordered).2 source target).vertices =
            [((centeredEdges curve differential sheet
              (Subdivision.next current inherited request cached accepted small remaining)
                centers)[index.val]'index.isLt).edge.point upper])
        (fun source target => by
          have first := cropAt_head trace centers lower upper lowerInside upperInside ordered
          have actual := congrArg (fun compared : CropComparisons
              (⟨edgeOfStep curve differential segment within current inherited request cached accepted small sheet,
                centers.1⟩ : CenteredEdge curve differential) lower upper lowerInside upperInside =>
            (compared.2 source target).vertices) first
          have geometry := PreparedTraceEdges.PreparedTraceBudget.queryPath_vertices
            (edgeOfStep curve differential segment within current inherited request cached accepted small sheet)
            budget fits.1 fits.2.1 lower upper lowerInside upperInside ordered source target
          exact actual.trans geometry)
        (fun next source target => by
          have first := cropAt_succ trace centers lower upper lowerInside upperInside ordered next
          have actual := congrArg (fun compared : CropComparisons
              ((centeredEdges curve differential sheet remaining centers.2)[next.val]'next.isLt)
                lower upper lowerInside upperInside =>
            (compared.2 source target).vertices) first
          have geometry := ih fits.2.2 (View.build trace).tailTrace centers.2 next source target
          exact actual.trans geometry) index)
    subdivision fits trace centers index source target

end PreparedTraceBudget.Trace

end Purelib.Riemann.Paths.PreparedSubdivisionTrace

end
