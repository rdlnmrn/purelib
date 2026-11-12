module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces.SharedMesh.Bounds
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces.SharedMesh.Requests
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.Transport
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Nat.Order

/-! # Actual requested numerical crops on retained physical and allocation owners

The source preparation, Point acquisitions, domain, split, all-cell bounds
and both original paid selections are retained inputs. Exact scalar/cache
readbacks identify their original pre-stage coefficients. One transported
request then constructs one fine oriented bank, one primitive/anchor/offset
chain and one shared reading cache. The same actual retained-bounds outcome
supplies its own complete target factory and every comparison/payment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularRefinementSigns (SheetCache)
open Purelib.Riemann.Readings.RectangularPointReadings.Chord (MeshReadings)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

universe u

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count sourceFloor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish}
    {goal : AccuracyRequest} {sourceScale residualScale : Rational} {residualFloor : Nat}
    (source : Selection sourceScale sourceFloor (goal.tolerance / 4))
    (residual : Selection residualScale residualFloor (goal.tolerance / 4))
    {targets : CellEndpoints.Targets originalPath source.stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count (Nat.max 2 sourceFloor) covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    (points : observed.Points requested)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    (shared : Face.DomainBanks.FaceDomains rootFrames face)
    (prefixes : PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside)
    (ordered : lower ≤ upper) (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition shared.models firstInside points.samples.1.val.owner)
    (domain : PeriodDomain shared.models acquired.entry.sheet)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    {numerator : Polynomial} {ambientBounds : PrimitiveOverlapBounds face.clearance numerator}
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    {channel : Fin 6} {gap : AccuracyRequest}
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ 1)
    {target : Rational}

namespace UniformPieces.Chord.SharedMesh

/-- The exact actual retained-bounds outcome on a supplied original primitive cache and request. -/
abbrev NumericalOutcome (request : GridPrimitiveAccuracy ambientBounds domain.steps target)
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      numerator) : Type _ :=
  PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel)
    (oldBank := RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
    (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (pieceCoefficients request primitives split)

/-- Complete actual numerical caches and the derived requested crop payment, on unchanged original owners. -/
abbrev NumericalConsumer (request : GridPrimitiveAccuracy ambientBounds domain.steps target)
    (Result : Type u) : Type _ :=
  (oriented : Bank (Paths.polynomial parameter) domain.geometry) →
  (_bank_factory : oriented = RectangularSheetGauge.Transitions.oriented
    (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge) →
  (primitives : Primitives (RectangularSheetGauge.Transitions.oriented
    (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
    numerator) →
  (_primitives_factory : HEq primitives (Primitives.build oriented numerator)) →
  (anchors : PrimitiveAnchors primitives) →
  (_anchors_factory : anchors = PrimitiveAnchors.build primitives) →
  (offsets : Offsets anchors.edges) → (_offsets_factory : offsets = anchors.offsets) →
  (cached : MeshReadings split anchors offsets) →
  (_readings_factory : cached = MeshReadings.build split anchors offsets) →
  (targetCompiled : ∀ position (point : Canonical), (pieceCoefficients request primitives split position).eval point =
    numerator.eval point *
      ((RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge).ready
          (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval point ^ 1) →
  (outcome : NumericalOutcome (source := source) (points := points) (shared := shared)
    (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (gap := gap) request primitives) →
  (_outcome_factory : outcome = preparePiecesWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (channel := channel)
    (oldBank := RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
    (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (pieceCoefficients request primitives split) rfl originalSource parentEvaluation sourceCompiled targetCompiled
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    cachedBounds) →
  (accepted : {value : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel)
    (oldBank := RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
    (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (pieceCoefficients request primitives split) // outcome = .ok value}) →
  (_compared : Comparisons (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (channel := channel) request primitives anchors offsets split accepted.val cached) →
  normSq ((cropped.models.cell channel).integralSample - sample request primitives anchors offsets split cached) <
    goal.tolerance → Result

/-- Construct the actual one-bank numerical crop and derive its requested accuracy from retained allocation data.

The original grid request is transported through the exact retained domain
step equality, with its actual index and bounds unchanged. New models,
primitives and readings execute only after those original selections. The
same once-bound retained-bounds outcome supplies all targets, successful
caches and comparisons. Its impossible SourceFloor branch is discharged
by the literal max-two construction floor; the whole outcome remains data.
No final numerical comparison or newly paid old-model stage is supplied.
-/
def withNumerics
    {originalSteps : Nat}
    (glue original : GridPrimitiveAccuracy ambientBounds originalSteps target)
    (originalFactory : original = glue.after residual.stage)
    (steps_eq : originalSteps = domain.steps)
    (sourceScale_eq : sourceScale = Budget.Aggregate.countCoordinate split.count *
      normSq (parent.edge.point upper - parent.edge.point lower) *
        (96 + 32 * (prepared.preparation.cell.patch.base.model.bound /
          (2 * prepared.preparation.cell.patch.inverseErrorScale)) * Rectangular.powerScale cachedBounds.val 1))
    (residualScale_eq : residualScale = 128 * Budget.Aggregate.countCoordinate split.count *
      Rectangular.powerScale cachedBounds.val 1 * normSq (parent.edge.point upper - parent.edge.point lower) / 256)
    (target_eq : target = Budget.Aggregate.perTerm (goal.tolerance / 4) split.count / 32)
    {Result : Type u}
    (consume :
      (request : GridPrimitiveAccuracy ambientBounds domain.steps target) →
      request = GridPrimitiveAccuracy.castColumns steps_eq original → HEq request original →
      request.index = original.index → request.globalBound = original.globalBound →
      NumericalConsumer (source := source) (points := points) (shared := shared)
        (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (cachedBounds := cachedBounds) (channel := channel) (gap := gap)
        originalSource parentEvaluation sourceCompiled request Result) : Result :=
  let request := GridPrimitiveAccuracy.castColumns steps_eq original
  let glueView := GridPrimitiveAccuracy.castColumns steps_eq glue
  have requestFactory : request = glueView.after residual.stage :=
    (congrArg (GridPrimitiveAccuracy.castColumns steps_eq) originalFactory).trans
      (GridPrimitiveAccuracy.castColumns_after steps_eq glue residual.stage)
  let fineModels := domain.patch.models.refine request.index
  let sheets : SheetCache fineModels := domain.patch.sheets.refine request.index
  let oriented := RectangularSheetGauge.Transitions.oriented (bank := fineModels) sheets.transitions sheets.gauge
  let primitives : Primitives (RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      numerator := Primitives.build oriented numerator
  let anchors := PrimitiveAnchors.build primitives
  let offsets := anchors.offsets
  let cached := MeshReadings.build (models := oriented) split anchors offsets
  have targetCompiled : ∀ position (point : Canonical), (pieceCoefficients request primitives split position).eval
      point = numerator.eval point *
        (oriented.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point ^ 1 :=
    fun position point => by
      simpa only [pieceCoefficients, pow_one, -eq_self, -iff_self] using
        primitives.coefficient_eq (auxiliaryPiece split position).column (auxiliaryPiece split position).row point
  let outcome := preparePiecesWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (channel := channel)
    (oldBank := oriented) (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (pieceCoefficients request primitives split) rfl originalSource parentEvaluation sourceCompiled targetCompiled
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    cachedBounds
  let accepted := PiecePreparation.success (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oriented)
    (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (targetSources := pieceCoefficients request primitives split) outcome (Data.Nat.Order.le_max_left 2 sourceFloor)
  let compared := Comparisons.withBounds (points := points) (shared := shared) (prefixes := prefixes)
    (ordered := ordered) (firstInside := firstInside) (acquired := acquired) (domain := domain)
    (channel := channel) (gap := gap) request primitives anchors offsets split
    originalSource parentEvaluation sourceCompiled targetCompiled cachedBounds outcome rfl
    accepted.val accepted.property cached
  have displacementBound := totalDisplacementCost_le (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (channel := channel) (gap := gap) request primitives split accepted.val
  have powerBound := totalPowerCost_le (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (channel := channel) (gap := gap)
    request primitives split accepted.val originalSource parentEvaluation sourceCompiled targetCompiled
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    cachedBounds outcome rfl accepted.property
  have paid := requested_costs_lt originalPath goal split.count
    (prepared.preparation.cell.patch.base.model.bound / (2 * prepared.preparation.cell.patch.inverseErrorScale))
    (Rectangular.powerScale cachedBounds.val 1) (normSq (parent.edge.point upper - parent.edge.point lower))
    (by
      exact (PreparedParent.initialRatio_nonnegative prepared).trans_eq (PreparedParent.initialRatio_eq prepared))
    source residual sourceScale_eq residualScale_eq targets glueView request requestFactory target_eq
    displacementBound powerBound
  have countEq : (split.pieces.length : Rational) = Budget.Aggregate.countCoordinate split.count :=
    (congrArg (fun value : Nat => (value : Rational)) split.count_eq.symm).trans
      (Budget.Aggregate.countCoordinate_eq split.count).symm
  have formula := congrArg (fun size : Rational => targets.localBound * size *
    (96 * totalDisplacementCost request primitives split accepted.val +
      32 * (prepared.preparation.cell.patch.base.model.bound /
        (2 * prepared.preparation.cell.patch.inverseErrorScale)) *
        totalPowerCost request primitives split accepted.val) +
    128 * size * totalPowerCost request primitives split accepted.val * Geometric.Basic.quarterRadius (1 / 256)
      request.index + 32 * size ^ 2 * request.globalBound) countEq
  have bound := (Comparisons.integral_difference_le_paid (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (channel := channel) (gap := gap) (completed := accepted.val)
    request primitives anchors offsets split cached compared).trans_lt (formula.trans_lt paid)
  consume request rfl (GridPrimitiveAccuracy.castColumns_heq steps_eq original)
    (GridPrimitiveAccuracy.castColumns_index steps_eq original)
    (GridPrimitiveAccuracy.castColumns_globalBound steps_eq original)
    oriented rfl primitives (HEq.refl primitives) anchors rfl offsets rfl cached rfl targetCompiled outcome rfl
    accepted compared bound

end UniformPieces.Chord.SharedMesh

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
