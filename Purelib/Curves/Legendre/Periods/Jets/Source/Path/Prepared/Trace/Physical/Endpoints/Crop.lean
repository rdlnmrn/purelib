module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Observed
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Sources.Selection
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Executed source crops on the actual selected physical parent

The original selector retains its complete SourcePair as the result index.
Its actual View constructs one crop operation and its genuine vertex law.
The completed generic crop acquisition is transported only along the same
whole source-pair equation. Original selector closure and completed runtime
cache remain separate values, with a pointwise factory equation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Data.List
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Branches
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest}

namespace PreparedParents.Trace.Sources

open Physical.Comparison (SourcePair)

/-- The actual supplied crop operation and complete acquisition on this SAME selected original source pair. -/
@[expose] def Cropped {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (source : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) [parent])
    (row : Row) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (comparisonRequest requested : AccuracyRequest) :=
  Σ physical : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside,
    PreparedParent.Crop.Acquisition (frame := frame) (basis := basis) (row := row)
      (accuracy := Primitive.localRequest requested 3) (source.2.entry 0)
      lower upper lowerInside upperInside physical comparisonRequest requested ×
      PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside ×
      PreparedTraceBudget.Trace.CropFamily.All parent

/-- Acquire one real source crop from the selected original View, preserving the already retained SourcePair.

The original singleton equation changes only the source index of the
completed cache. The selected pair remains the result owner. New local
observation accuracy is chosen before observation for the actual three
moving/endpoint occurrences; the old row Spine and its requests are not
retargeted or reused as strict-fraction observations.
-/
def cropConsumer {left right : PreparedSheetContinuation.Endpoint} {budget : PreparedTraceBudget segment left right}
    (row : Row) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (comparisonRequest requested : AccuracyRequest) :
    Consumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy) row
      (fun {_} source => Cropped source row lower upper lowerInside upperInside comparisonRequest requested) :=
  fun view center patch inside prepared _selected selectedEq _old _parts =>
    let physical := view.cropComparisons center lower upper lowerInside upperInside ordered
    let acquired := PreparedParent.Crop.Acquisition.build (frame := frame) (basis := basis) (row := row)
      (accuracy := Primitive.localRequest requested 3) prepared lower upper lowerInside upperInside physical
      (view.cropComparisons_vertices center lower upper lowerInside upperInside ordered)
      comparisonRequest requested
    let prefixes := view.cropFrom center lower lowerInside
    let families := view.cropFamilies center
    let completed : Cropped (singleton patch inside prepared) row lower upper
        lowerInside upperInside comparisonRequest requested := ⟨physical, acquired, prefixes, families⟩
    Eq.mpr (congrArg (fun source => Cropped source row lower upper
      lowerInside upperInside comparisonRequest requested) selectedEq) completed

/-- Whole-source transport keeps the independent physical-operation projection unchanged. -/
private theorem transportPhysical {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (row : Row) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (comparisonRequest requested : AccuracyRequest)
    {first last : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (targets := targets) [parent]} (same : first = last)
    (data : Cropped last row lower upper lowerInside upperInside comparisonRequest requested) :
    (Eq.mpr (congrArg (fun source => Cropped source row lower upper
      lowerInside upperInside comparisonRequest requested) same) data).1 = data.1 := by
  cases same
  rfl

/-- The executed consumer retains the actual original View crop operation as a whole, before any later selector cast. -/
theorem cropConsumer_physical
    {left right : PreparedSheetContinuation.Endpoint} {budget : PreparedTraceBudget segment left right}
    {current : PreparedSheetContinuation.Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {request : PreparedSheetContinuation.StepRequest}
    {cached : PreparedSheetContinuation.CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : PreparedSheetContinuation.Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (PreparedSheetContinuation.Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : PreparedTraceBudget.Trace budget
      (PreparedSheetContinuation.Subdivision.next current inherited request cached ordered small remaining) fits}
    (view : PreparedTraceBudget.Trace.View budget current inherited request cached ordered small remaining fits trace)
    (center : PreparedEdge.CenterState
      (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
    (patch : UniformPrimitiveSheetCompatibility.PreparedPatch
      (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
        center⟩ : CenteredEdge (Fibre.frameCurve frame) basis))
    (inside : (patch.neighborhood count).box.Contains
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet).point 1))
    (prepared : PreparedParent patch count floor inside targets)
    (selected : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      [⟨edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet, center⟩])
    (selectedEq : selected = singleton patch inside prepared)
    (row : Row) (old : Primitive.Spine (row.expression parameter) accuracy trace.path)
    (parts : view.Observations old) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (cropOrdered : lower ≤ upper)
    (comparisonRequest requested : AccuracyRequest) :
    (cropConsumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy)
      row lower upper lowerInside upperInside cropOrdered comparisonRequest requested
      view center patch inside prepared selected selectedEq old parts).1 =
        view.cropComparisons center lower upper lowerInside upperInside cropOrdered := by
  unfold cropConsumer
  exact transportPhysical row lower upper lowerInside upperInside comparisonRequest requested selectedEq _

/-- The all-source closure is the complete original cropFamilies value of this SAME selected accepted View. -/
theorem cropConsumer_families
    {left right : PreparedSheetContinuation.Endpoint} {budget : PreparedTraceBudget segment left right}
    {current : PreparedSheetContinuation.Endpoint}
    {inherited : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {request : PreparedSheetContinuation.StepRequest}
    {cached : PreparedSheetContinuation.CachedSource segment current inherited request}
    {ordered : current.parameter ≤ request.endpoint.parameter}
    {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
    {remaining : PreparedSheetContinuation.Subdivision segment within request.endpoint
      (PreparedSheetContinuation.advance segment within current inherited request small)}
    {fits : budget.RequestsFit current
      (PreparedSheetContinuation.Subdivision.next current inherited request cached ordered small remaining).requests}
    {trace : PreparedTraceBudget.Trace budget
      (PreparedSheetContinuation.Subdivision.next current inherited request cached ordered small remaining) fits}
    (view : PreparedTraceBudget.Trace.View budget current inherited request cached ordered small remaining fits trace)
    (center : PreparedEdge.CenterState
      (edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet))
    (patch : UniformPrimitiveSheetCompatibility.PreparedPatch
      (⟨edgeOfStep (Fibre.frameCurve frame) basis segment within current inherited request cached ordered small sheet,
        center⟩ : CenteredEdge (Fibre.frameCurve frame) basis))
    (inside : (patch.neighborhood count).box.Contains
      ((edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet).point 1))
    (prepared : PreparedParent patch count floor inside targets)
    (selected : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      [⟨edgeOfStep (Fibre.frameCurve frame) basis segment within
        current inherited request cached ordered small sheet, center⟩])
    (selectedEq : selected = singleton patch inside prepared)
    (row : Row) (old : Primitive.Spine (row.expression parameter) accuracy trace.path)
    (parts : view.Observations old) (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (cropOrdered : lower ≤ upper)
    (comparisonRequest requested : AccuracyRequest) :
    (cropConsumer (frame := frame) (basis := basis) (count := count) (floor := floor)
      (within := within) (sheet := sheet) (targets := targets) (budget := budget) (accuracy := accuracy)
      row lower upper lowerInside upperInside cropOrdered comparisonRequest requested
      view center patch inside prepared selected selectedEq old parts).2.2.2 =
        view.cropFamilies center := by
  cases selectedEq
  rfl

end PreparedParents.Trace.Sources

namespace PreparedParents.Trace.Physical.Comparison.EndpointPoints

variable {row : Row}
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

/-- The same original endpoint cache, selected source/closure and its complete actual crop execution. -/
@[expose] def Cropped (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (comparisonRequest requested : AccuracyRequest) :=
  Σ original : {value : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery //
      value = kept},
  Σ selected : original.val.ParentResult
      (fun {_} source => Sources.Cropped source row lower upper lowerInside upperInside comparisonRequest requested),
    selected.Executed

/-- Select the physical parent once and execute its real source-crop acquisition once.

The original endpoint cache, complete selected SourcePair and deferred
closure remain runtime data beside the completed cache. The same existing
selector performs all owner/source index transports. No row conclusion,
period equality, replacement source preparation or strict old Vertex is
an input to this constructor.
-/
def acquireCrop (lower upper : Rational)
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) (ordered : lower ≤ upper)
    (comparisonRequest requested : AccuracyRequest) :
    kept.Cropped lower upper lowerInside upperInside comparisonRequest requested :=
  let original := kept
  let selected := original.withParent
    (fun {_} source => Sources.Cropped source row lower upper lowerInside upperInside comparisonRequest requested)
    (Sources.cropConsumer row lower upper lowerInside upperInside ordered comparisonRequest requested)
  let executed := selected.execute
  ⟨⟨original, rfl⟩, selected, executed⟩

namespace Cropped

variable {kept lower upper lowerInside upperInside comparisonRequest requested}
variable (acquired : kept.Cropped lower upper lowerInside upperInside comparisonRequest requested)

/-- Read the complete original endpoint cache without reconstructing its source pair or queries. -/
abbrev original := acquired.1.val

/-- Read the original selected source pair and its unchanged deferred callback. -/
abbrev selected := acquired.2.1

/-- Read the separately retained completed selected-parent execution. -/
abbrev executed := acquired.2.2

/-- Read the actual supplied same-View crop operation from that completed execution. -/
abbrev physical := acquired.executed.value.1

/-- Read the complete intrinsic crop acquisition on the exact selected original source entry. -/
abbrev acquisition := acquired.executed.value.2.1

/-- Read the actual same-View family accepting the retained lower Query and each later actual Query. -/
abbrev prefixes := acquired.executed.value.2.2.1

/-- Read the retained SAME-View family for both genuinely new strict-child endpoint Queries. -/
abbrev families := acquired.executed.value.2.2.2

/-- The retained same-View prefix path has exactly its actual later query target occurrence.

Both Queries are supplied original caches. The family constructs the path
between those exact nominal Owners; this incidence law supplies no Point
or sheet equality from their coordinates.
-/
theorem prefix_vertices (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (ordered : lower ≤ fraction)
    (source : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge lower lowerInside)
    (target : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge fraction inside) :
    (acquired.prefixes.val fraction inside ordered source target).vertices =
      [(parents.covered.parents[index.val]'index.isLt).edge.point fraction] :=
  acquired.prefixes.property fraction inside ordered source target

/-- The actual two supplied child Query owners determine a singleton crop on the same retained parent.

Both fractions and their admitted bounds are original inputs. This reads
only the retained all-source family; it never selects another parent or
reconstructs either Query, Point, primitive model or old observation.
-/
theorem family_vertices (first last : Rational)
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) (ordered : first ≤ last)
    (source : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge first firstInside)
    (target : PreparedEdge.Query (parents.covered.parents[index.val]'index.isLt).edge last lastInside) :
    ((acquired.families first firstInside).val last lastInside ordered source target).vertices =
      [(parents.covered.parents[index.val]'index.isLt).edge.point last] :=
  (acquired.families first firstInside).property last lastInside ordered source target

/-- Read all seven original-source restrictions, keeping the six differential models separate from the row. -/
abbrev models := acquired.acquisition.1.models

/-- Read the six actual uniform child certificates from the same cached source query family. -/
def certificates := acquired.acquisition.1.certificates

/-- The entire selected preparation is the original endpoint cache's same whole source entry. -/
theorem entry_heq : HEq (acquired.selected.source.2.entry 0) kept.entry := by
  exact acquired.selected.entry_heq.trans
    (acquired.original.entry_heq.trans kept.entry_heq.symm)

/-- The completed cache belongs to the original deferred execution, rather than a substituted factory. -/
theorem execution_eq : acquired.executed.value = acquired.selected.run () := acquired.executed.factory_eq

/-- The genuine moving vertex and both new endpoint joins give their actual retained count of three. -/
theorem count_eq_three :
    (acquired.acquisition.1.moving.withJoins acquired.acquisition.2.2.joins.1.val
      acquired.acquisition.2.2.joins.2.val).vertices.length = 3 := acquired.acquisition.2.2.count_eq_three

/-- Fresh observations chosen before acquisition pay the actual three-link stationary target internally. -/
theorem stationary_error_lt :
    Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum acquired.acquisition.2.2.payment.retained.jumps) <
        requested.tolerance := by
  exact acquired.acquisition.2.2.payment.retained.jumps_error_lt
    requested.positive acquired.count_eq_three.le
    (Data.Rat.Fraction.Order.Basic.le_refl _)

/-- The actual child integral reads the SAME original retained source polynomial on its displayed interval. -/
theorem integralSample_eq (channel : Fin 6) :
    (acquired.models.cell channel).integralSample =
      (kept.entry.preparation.cell.models.cell channel).displacement *
        Polynomial.Ascending.Gaussian.Integral.definiteIntegral
          (kept.entry.preparation.cell.models.cell channel).polynomial
          (Data.Gaussian.Cast.Path.ofCoordinate lower) (Data.Gaussian.Cast.Path.ofCoordinate upper) := by
  have retained := Integration.Polynomial.Gaussian.Cell.Restriction.integralSample_eq
    ((acquired.selected.source.2.entry 0).preparation.cell.models.cell channel)
    (acquired.models.channelCache channel)
  have selected := congrArg
    (fun source : SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
        (targets := targets) [parents.covered.parents[index.val]'index.isLt] =>
      (source.2.entry 0).preparation.cell.models.cell channel)
    acquired.selected.source_eq
  have original :
      (((Sources.entryPair acquired.original.pair.1 acquired.original.pair.2
          index).2.entry 0).preparation.cell.models.cell channel) =
        (acquired.original.entry.preparation.cell.models.cell channel) := by
    rewrite [Sources.entryPair_eq]
    unfold Sources.singleton
    change ((acquired.original.pair.2.entry index).preparation.cell.models.cell channel) = _
    exact congrArg
      (fun original : PreparedParent (acquired.original.pair.1.entry index).val count floor
          (acquired.original.pair.1.entry index).property targets =>
        original.preparation.cell.models.cell channel)
      acquired.original.entry_eq.symm
  have sameOriginal := congrArg
    (fun original : EndpointPoints (frame := frame) (basis := basis) compared index firstQuery lastQuery =>
      original.entry.preparation.cell.models.cell channel)
    acquired.1.property
  have sameModel := selected.trans (original.trans sameOriginal)
  exact retained.trans (congrArg (fun model : Integration.Polynomial.Gaussian.Cell.Basic.CellModel =>
    model.displacement * Polynomial.Ascending.Gaussian.Integral.definiteIntegral model.polynomial
      (Data.Gaussian.Cast.Path.ofCoordinate lower) (Data.Gaussian.Cast.Path.ofCoordinate upper)) sameModel)

end Cropped

end PreparedParents.Trace.Physical.Comparison.EndpointPoints

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
