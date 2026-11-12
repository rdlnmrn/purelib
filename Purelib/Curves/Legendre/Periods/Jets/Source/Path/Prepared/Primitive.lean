module
public import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Primitive
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
public import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

/-! # Retained primitive requests on the original prepared source cells

The complete source Cell factory determines its exact count/patch view.
Only that dependent index transports the existing PrimitiveModel; the
original source, request, model and polynomial are not reconstructed.
Controlled local requests use the same operation on their retained model.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {count floor : Nat}
    {patch : PreparedPatch parent} {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- The whole original Cell factory identifies its dependent count and continued patch together. -/
private theorem packaged_queryPatch_eq (prepared : PreparedParent patch count floor covered targets) :
    (⟨prepared.preparation.cell.count, prepared.preparation.cell.patch⟩ :
      (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size) =
        ⟨count, patch.neighborhood count⟩ :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) =>
    (⟨cell.count, cell.patch⟩ : (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size))
    prepared.preparation.cell_eq

/-- The whole original Cell factory identifies its dependent count and continued patch together. -/
theorem queryPatch_eq (prepared : PreparedParent patch count floor covered targets) :
    (⟨prepared.preparation.cell.count, prepared.preparation.cell.patch⟩ :
      (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size) =
        ⟨count, patch.neighborhood count⟩ := packaged_queryPatch_eq prepared

/-- View the same retained primitive under the actual source Cell's coupled count and patch indices. -/
def primitiveView (prepared : PreparedParent patch count floor covered targets) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    PrimitiveModel prepared.preparation.cell.patch index (differentialNumerator basis) :=
  Eq.mpr (congrArg (fun owner : (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size =>
    PrimitiveModel owner.2 index (differentialNumerator basis)) prepared.queryPatch_eq) model

/-- The source-index view retains the complete original primitive model heterogeneously. -/
private theorem packaged_primitiveView_heq (prepared : PreparedParent patch count floor covered targets) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    HEq (prepared.primitiveView model) model := by
  have transport
      (first last : (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size) (same : first = last)
      (value : PrimitiveModel last.2 index (differentialNumerator basis)) :
      HEq (Eq.mpr (congrArg (fun owner => PrimitiveModel owner.2 index (differentialNumerator basis)) same) value)
        value := by cases same; rfl
  exact transport _ _ prepared.queryPatch_eq model

/-- The source-index view retains the complete original primitive model heterogeneously. -/
theorem primitiveView_heq (prepared : PreparedParent patch count floor covered targets) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    HEq (prepared.primitiveView model) model :=
  packaged_primitiveView_heq prepared model

/-- The coupled index view keeps the identical original primitive polynomial. -/
private theorem packaged_primitiveView_value (prepared : PreparedParent patch count floor covered targets) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    (prepared.primitiveView model).primitive.value = model.primitive.value := by
  have transport
      (first last : (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size) (same : first = last)
      (value : PrimitiveModel last.2 index (differentialNumerator basis)) :
      (Eq.mpr (congrArg (fun owner => PrimitiveModel owner.2 index (differentialNumerator basis)) same)
        value).primitive.value = value.primitive.value := by cases same; rfl
  exact transport _ _ prepared.queryPatch_eq model

/-- The coupled index view keeps the identical original primitive polynomial. -/
theorem primitiveView_value (prepared : PreparedParent patch count floor covered targets) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    (prepared.primitiveView model).primitive.value = model.primitive.value :=
  packaged_primitiveView_value prepared model

/-- Compare the actual prepared source with the same retained primitive, transporting only its original owner index. -/
def primitiveComparison (prepared : PreparedParent patch count floor covered targets)
    (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    Primitive.Comparison prepared.preparation.cell.models.valueZero.model :=
  prepared.preparation.query.valueZero_primitiveComparison frame basis zero (prepared.primitiveView model)

/-- The retained primitive and actual source integral satisfy the derived finite coefficient bound. -/
theorem primitive_error_le (prepared : PreparedParent patch count floor covered targets)
    (zero : basis.exponent = 0) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator basis)) :
    Norm.Basic.normSq (model.primitive.value.eval (parent.edge.point 1) -
      model.primitive.value.eval (parent.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
        16 * (targets.localBound + quarterRadius (patch.neighborhood count).inverseErrorScale index) * cost parent := by
  have bound := prepared.preparation.query.valueZero_primitive_error_le frame basis zero (prepared.primitiveView model)
  have scaleEq := congrArg (fun owner : (size : Nat) × ContinuedNeighborhood (Paths.polynomial parameter) size =>
    owner.2.inverseErrorScale) prepared.queryPatch_eq
  have displacement : prepared.preparation.cell.models.valueZero.model.displacement =
      (finishPoint parent).coordinate - (startPoint parent).coordinate := by
    change prepared.preparation.cell.models.valueZero.model.finish -
      prepared.preparation.cell.models.valueZero.model.start = _
    rewrite [prepared.preparation.cell.models.valueZero.start_eq,
      prepared.preparation.cell.models.valueZero.finish_eq]
    rfl
  have allowanceEq := prepared.preparation.cell.models.valueZero.allowance_eq.trans prepared.allowance_eq
  rewrite [prepared.primitiveView_value model, allowanceEq, scaleEq, displacement] at bound
  rewrite [parent.edge.point_one, parent.edge.point_zero]
  exact bound

/-- The same original local primitive and prepared source retain their independent actual error indices.

The request belongs to the source's original patch. Its whole neighborhood
factory transports the cached model; neither request nor source is built.
-/
theorem local_primitive_error_le {target : Rational} (request : LocalRequest parent count target)
    {covered : (request.patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (prepared : PreparedParent request.patch count floor covered targets) (zero : basis.exponent = 0) :
    Norm.Basic.normSq (request.request.model.primitive.value.eval (parent.edge.point 1) -
      request.request.model.primitive.value.eval (parent.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + quarterRadius request.neighborhood.inverseErrorScale request.request.index) *
        cost parent := by
  have bound := prepared.primitive_error_le zero request.patchPrimitive
  have scaleEq := congrArg (fun neighborhood => neighborhood.inverseErrorScale) request.neighborhood_eq
  rewrite [request.patchPrimitive_value, ← scaleEq] at bound
  exact bound

/-- Transport the retained controlled request's complete primitive to its own original patch-neighborhood index. -/
def controlledPrimitive {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum) :
    PrimitiveModel (request.localRequest.patch.neighborhood count) request.localRequest.request.index
      (differentialNumerator basis) :=
  request.localRequest.patchPrimitive

/-- The patch-index view retains the whole originally selected controlled primitive. -/
private theorem packaged_controlledPrimitive_heq {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum) :
    HEq (controlledPrimitive request) request.localRequest.request.model :=
  request.localRequest.patchPrimitive_heq

/-- The patch-index view retains the whole originally selected controlled primitive. -/
theorem controlledPrimitive_heq {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum) :
    HEq (controlledPrimitive request) request.localRequest.request.model :=
  packaged_controlledPrimitive_heq request

/-- The controlled patch-index view retains its original cached primitive polynomial. -/
private theorem packaged_controlledPrimitive_value {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum) :
    (controlledPrimitive request).primitive.value = request.localRequest.request.model.primitive.value :=
  request.localRequest.patchPrimitive_value

/-- The controlled patch-index view retains its original cached primitive polynomial. -/
theorem controlledPrimitive_value {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum) :
    (controlledPrimitive request).primitive.value = request.localRequest.request.model.primitive.value :=
  packaged_controlledPrimitive_value request

/-- The actual controlled primitive and source cell have a derived finite error, using both original selected indices.

The source preparation belongs to this request's exact original patch.
The whole neighborhood factory equality changes only the primitive index
view; neither source preparation nor controlled acquisition is replayed.
-/
theorem controlled_primitive_error_le {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum)
    {covered : (request.localRequest.patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (prepared : PreparedParent request.localRequest.patch count floor covered targets) (zero : basis.exponent = 0) :
    Norm.Basic.normSq (request.localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      request.localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + quarterRadius request.localRequest.neighborhood.inverseErrorScale
        request.localRequest.request.index) * cost parent :=
  local_primitive_error_le request.localRequest prepared zero

/-- The controlled request's actual coefficient payment also bounds the source primitive discrepancy.

For the zero exponent, the original numerator is exactly one, so the
retained numerator bound is at least one. The stored coefficient accuracy
therefore pays the same inverse-error term without an additional premise.
-/
theorem controlled_primitive_paid_le {target coefficientTarget : Rational} {minimum : Nat}
    (request : ControlledLocalRequest parent count target coefficientTarget minimum)
    {covered : (request.localRequest.patch.neighborhood count).box.Contains (parent.edge.point 1)}
    (prepared : PreparedParent request.localRequest.patch count floor covered targets) (zero : basis.exponent = 0) :
    Norm.Basic.normSq (request.localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      request.localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + coefficientTarget) * cost parent := by
  have inside : request.localRequest.neighborhood.box.Contains (parent.edge.point 0) := by
    rewrite [request.localRequest.neighborhood_eq]
    exact request.localRequest.patch.start_inside count
  have numeratorBound := request.localRequest.request.numerator_le (parent.edge.point 0) inside
  rewrite [Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator_eval, zero, pow_zero] at numeratorBound
  change (1 : Rational) ≤ request.localRequest.request.numeratorBound at numeratorBound
  have scaled := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel : (1 : Rational) ≤ 4) request.localRequest.request.numerator_nonnegative
  have enlarged : request.localRequest.request.numeratorBound ≤
      4 * request.localRequest.request.numeratorBound := by
    exact (show request.localRequest.request.numeratorBound =
      1 * request.localRequest.request.numeratorBound by ring1).trans_le scaled
  have oneLe : (1 : Rational) ≤ 4 * request.localRequest.request.numeratorBound := numeratorBound.trans enlarged
  have inverseNonnegative := Approximation.Rational.Geometric.Basic.quarterRadius_nonneg
    request.localRequest.neighborhood.inverseErrorScale_positive.le request.localRequest.request.index
  have inverseLe : quarterRadius request.localRequest.neighborhood.inverseErrorScale
      request.localRequest.request.index ≤
        Riemann.Readings.PreparedPrimitiveChargeBounds.localCoefficient request.localRequest := by
    change _ ≤ 4 * request.localRequest.request.numeratorBound * _
    calc
      _ = 1 * quarterRadius request.localRequest.neighborhood.inverseErrorScale
          request.localRequest.request.index := by ring1
      _ ≤ _ := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe inverseNonnegative
  have inversePaid := inverseLe.trans request.coefficient_accurate.le
  have original := controlled_primitive_error_le request prepared zero
  exact original.trans (Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (Data.Rat.Fraction.Order.Basic.le_refl targets.localBound) inversePaid) (by decide +kernel))
    (cost_nonnegative parent))

section RectangularComparison

open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece GridCuts SegmentSplit)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (traced_parent_reached)
open Purelib.Riemann.Integration.PreparedParentSplitting (prepared_point_eq)

/-- An actual retained six-channel source primitive obeys the common-cell fragment estimate.

Operational alignment at the actual first fragment point supplies the
source-root relation. The fragment supplies both cell endpoints, while
the original covered parent proves containment in its source neighborhood.
The same stored source request, final stage, model and coefficient table
are used at every channel; no owner, comparison or primitive request is
acquired by this proof.
-/
theorem rectangular_fragment_le (prepared : PreparedParent patch count floor covered targets)
    {box prefixAmbient : Box}
    {clearance : Clearance (Paths.polynomial parameter) box} {comparisonBounds : Bounds clearance}
    {pathStart : Canonical} {sourceOwner : Owner ((Paths.polynomial parameter).eval pathStart)}
    {prefixPath : ClearPath (Paths.polynomial parameter) prefixAmbient pathStart box.anchor}
    {entered : TracedPath prefixPath sourceOwner} (prefixInside : InBox box prefixPath)
    (reference : WindingOneLoop (Paths.polynomial parameter) pathStart)
    {columns rows : Nat} {geometry : Geometry columns rows}
    (common : RectangularPatch comparisonBounds entered.finishOwner geometry)
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    (channel : Fin 6) (index : Nat)
    (aligned : RootAligned ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
      piece.firstPoint (parent.edge.rootName piece.interval.lower
        ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩))
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented (common.sheets.refine index).transitions
      (common.sheets.refine index).gauge)
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    (overlap : PrimitiveOverlapBounds
      (clearance.restrict (common.cell_refines piece.column piece.row))
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)) :
    let actual := prepared.preparation.attached.source
    Norm.Basic.normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      ((actual.primitive channel).primitive.value.eval piece.lastPoint -
        (actual.primitive channel).primitive.value.eval piece.firstPoint)) ≤
      12 * (((common.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
        ((patch.neighborhood count).base.refine actual.selection.stage).bound) *
          overlap.weight (Specification.Table.forms parameter channel).denominatorPairs *
            Norm.Basic.normSq (piece.lastPoint - piece.firstPoint) := by
  let actual := prepared.preparation.attached.source
  have degreePositive : 0 < (Fibre.frameCurve frame).polynomial.natDegree := by
    rewrite [Fibre.frameCurve_polynomial, Paths.polynomial_natDegree]
    exact (of_decide_eq_true rfl : 0 < 3)
  have firstEq : piece.firstPoint = parent.edge.point piece.interval.lower :=
    piece.first_eq.trans (prepared_point_eq parent _).symm
  have lastEq : piece.lastPoint = parent.edge.point piece.interval.upper :=
    piece.last_eq.trans (prepared_point_eq parent _).symm
  have firstInside : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  have lastInside : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  have localInside (fraction : Rational) (unit : 0 ≤ fraction ∧ fraction ≤ 1) :
      (patch.neighborhood count).box.Contains (parent.edge.point fraction) := by
    rewrite [prepared_point_eq parent fraction, PreparedSegmentCuts.point_eq_line]
    exact Box.contains_line (patch.start_inside count) covered unit
  have alignedAt : RootAligned
      ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
      (parent.edge.point piece.interval.lower) (parent.edge.rootName piece.interval.lower firstInside) :=
    @Eq.mp _ _ (congrArg (fun point => RootAligned
      ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
      point (parent.edge.rootName piece.interval.lower firstInside)) firstEq) @aligned
  have coefficient := RectangularPatch.primitive_coefficient_eq
    (curve := Fibre.frameCurve frame) (index := index) common prefixInside basis degreePositive reference
    primitives piece.column piece.row
  have bounded :=
    (common.transported.cell piece.column piece.row).prepared_subedge_primitive_increment_le
      (curve := Fibre.frameCurve frame)
      (numerator := (Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (pairs := (Specification.Table.forms parameter channel).denominatorPairs)
      basis parent piece.interval.lower piece.interval.upper
      firstInside (firstEq ▸ piece.first_inside) patch count index actual.selection.stage @alignedAt
      (primitives.dense piece.column piece.row)
      coefficient
      (actual.primitive channel) overlap (lastEq ▸ piece.last_inside)
      (localInside _ firstInside) (localInside _ lastInside)
  rewrite [← firstEq, ← lastEq] at bounded
  exact bounded

/-- The retained rectangular split bounds the actual integral sample of its original six-channel source.

Each original piece uses its own containing cell and overlap payment at the
same numerical bank index and retains its actual endpoint alignment.
Finite summation charges the split's saved count
once, and the source primitive telescopes to the unchanged parent endpoints.
The original exact cell-integral law identifies the same source primitive
increment with its retained cell sample, preserving the source request,
polynomial cache and selected stage.
-/
theorem rectangular_split_le (prepared : PreparedParent patch count floor covered targets)
    {box prefixAmbient : Box}
    {clearance : Clearance (Paths.polynomial parameter) box} {comparisonBounds : Bounds clearance}
    {pathStart : Canonical} {sourceOwner : Owner ((Paths.polynomial parameter).eval pathStart)}
    {prefixPath : ClearPath (Paths.polynomial parameter) prefixAmbient pathStart box.anchor}
    {entered : TracedPath prefixPath sourceOwner} (prefixInside : InBox box prefixPath)
    (reference : WindingOneLoop (Paths.polynomial parameter) pathStart)
    {columns rows : Nat} {geometry : Geometry columns rows}
    (common : RectangularPatch comparisonBounds entered.finishOwner geometry)
    {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1))
    (channel : Fin 6) (index : Nat)
    (aligned : ∀ piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1),
      piece ∈ split.pieces →
      RootAligned ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
        piece.firstPoint (parent.edge.rootName piece.interval.lower
          ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩))
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented (common.sheets.refine index).transitions
      (common.sheets.refine index).gauge)
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    (overlaps : ∀ piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1),
      PrimitiveOverlapBounds
      (clearance.restrict (common.cell_refines piece.column piece.row))
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)) :
    let actual := prepared.preparation.attached.source
    Norm.Basic.normSq
      (sumFin (fun position : Fin split.pieces.length =>
        let piece := split.pieces[position.val]'position.isLt
        primitives.value piece.column piece.row piece.lastPoint -
          primitives.value piece.column piece.row piece.firstPoint) -
        (prepared.preparation.models.cell channel).integralSample) ≤
      (split.count : Rational) * sumFin (fun position : Fin split.pieces.length =>
        let piece := split.pieces[position.val]'position.isLt
        12 * (((common.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
          ((patch.neighborhood count).base.refine actual.selection.stage).bound) *
            (overlaps piece).weight (Specification.Table.forms parameter channel).denominatorPairs *
              Norm.Basic.normSq (piece.lastPoint - piece.firstPoint)) := by
  let actual := prepared.preparation.attached.source
  have integralEq : (prepared.preparation.models.cell channel).integralSample =
      (actual.primitive channel).primitive.value.eval (parent.edge.point 1) -
        (actual.primitive channel).primitive.value.eval (parent.edge.point 0) := by
    rewrite [parent.edge.point_one, parent.edge.point_zero]
    exact prepared.preparation.models.cell_integralSample_primitive channel
  rewrite [integralEq]
  apply split.comparison_le
    (fun piece => primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint)
    ((actual.primitive channel).primitive.value.eval)
    (fun piece =>
      12 * (((common.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
        ((patch.neighborhood count).base.refine actual.selection.stage).bound) *
          (overlaps piece).weight (Specification.Table.forms parameter channel).denominatorPairs *
            Norm.Basic.normSq (piece.lastPoint - piece.firstPoint))
  intro piece member
  exact prepared.rectangular_fragment_le prefixInside reference common piece channel index
    (@aligned piece member) primitives (overlaps piece)

end RectangularComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
