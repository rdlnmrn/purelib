module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces.SharedMesh.Numerics
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Preparation
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Curves.Legendre.Periods.Jets.Models
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Bounds
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.Transport
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Requested value crops on the same retained original geometric owners

Actual pre-stage allocations precede one fresh source/crop acquisition and
one numerical executor. Whole Point factories identify the original Entry;
its exact sheet/domain/cache transports identify the original coefficients.
Both Legendre value channels use their actual cached source tables and the
displayed full numerators. All outcomes, owners and factory values remain
available to the continuation; no final accuracy or Owner identity is input.
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
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic (constantOnePolynomial coordinatePolynomial)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Curves.Legendre.Periods.Jets.Specification (valueSpecification)
open Purelib.Curves.Legendre.Periods.Jets.Specification.Table (valueIndex)

universe u

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count oldFloor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {oldStage : Nat}
    {oldTargets : CellEndpoints.Targets originalPath oldStage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count oldFloor covered oldTargets} {lower upper : Rational}
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
    (coordinate : Fin 2)
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines
        (valueSpecification parameter coordinate).numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines
        (valueSpecification parameter coordinate).numerator})
    (ambientBounds : PrimitiveOverlapBounds face.clearance (valueSpecification parameter coordinate).numerator)
    (sourceFloor gridFloor : Nat) (goal newComparisonRequest newRequested gap : AccuracyRequest)

namespace UniformPieces.Chord.SharedMesh

/-- The actual whole domain factory and certified cache identity preserve its original power-scale sum. -/
private theorem view_powerScale_eq {firstSheet lastSheet : Fin 2} (equal : firstSheet = lastSheet)
    (originalDomain : PeriodDomain shared.models firstSheet) (view : PeriodDomain shared.models lastSheet)
    (factory : view = PeriodDomain.castSheet equal originalDomain) {numerator : Polynomial}
    (originalBounds : {value : Rectangular face.clearance originalDomain.geometry
        originalDomain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance originalDomain.geometry originalDomain.patch.cell_refines numerator})
    (viewBounds : {value : Rectangular face.clearance view.geometry view.patch.cell_refines numerator //
      value = Rectangular.build face.clearance view.geometry view.patch.cell_refines numerator})
    (same : HEq viewBounds originalBounds) :
    Rectangular.powerScale viewBounds.val 1 = Rectangular.powerScale originalBounds.val 1 := by
  cases equal
  have sameDomain : view = originalDomain := factory.trans (PeriodDomain.castSheet_refl originalDomain)
  cases sameDomain
  have sameBounds : viewBounds = originalBounds := eq_of_heq same
  exact congrArg (fun bounds : {value : Rectangular face.clearance originalDomain.geometry
      originalDomain.patch.cell_refines numerator //
    value = Rectangular.build face.clearance originalDomain.geometry originalDomain.patch.cell_refines numerator} =>
      Rectangular.powerScale bounds.val 1) sameBounds

/-- Each actual selected value table evaluates the SAME cached source coefficient in its original spatial coordinate. -/
private theorem value_parentEvaluation {nextFloor nextStage : Nat}
    {nextTargets : CellEndpoints.Targets originalPath nextStage}
    (next : PreparedParent patch count nextFloor covered nextTargets) (coordinate : Fin 2) (input : Rational) :
    Evaluation.eval (next.preparation.cell.models.cell (valueIndex coordinate)).polynomial ⟨input, 0⟩ =
      (next.preparation.cell.request.models.value coordinate).eval
        (next.preparation.cell.models.coordinate.point input) := by
  refine Fin.cases ?_ ?_ coordinate
  · change Evaluation.eval next.preparation.cell.models.valueZero.model.polynomial ⟨input, 0⟩ =
      next.preparation.cell.request.models.valueZero.eval (next.preparation.cell.models.coordinate.point input)
    exact next.preparation.cell.models.valueZero.eval_point input
  · intro index
    refine Fin.cases ?_ (fun index => Fin.elim0 index) index
    change Evaluation.eval next.preparation.cell.models.valueOne.model.polynomial ⟨input, 0⟩ =
      next.preparation.cell.request.models.valueOne.eval (next.preparation.cell.models.coordinate.point input)
    exact next.preparation.cell.models.valueOne.eval_point input

/-- Both actual value coefficients retain their displayed full numerator and SAME selected inverse model. -/
private theorem value_sourceCompiled {nextFloor nextStage : Nat}
    {nextTargets : CellEndpoints.Targets originalPath nextStage}
    (next : PreparedParent patch count nextFloor covered nextTargets) (coordinate : Fin 2) (point : Canonical) :
    (next.preparation.cell.request.models.value coordinate).eval point =
      (valueSpecification parameter coordinate).numerator.eval point *
        (next.preparation.cell.request.model.value.eval point) ^ 1 := by
  refine Fin.cases ?_ ?_ coordinate
  · change next.preparation.cell.request.models.valueZero.eval point = constantOnePolynomial.eval point *
      (next.preparation.cell.request.model.value.eval point) ^ 1
    simpa only [pow_one, -eq_self, -iff_self] using
      IntegrandRequests.valueZero_readback next.preparation.cell.request.models point
  · intro index
    refine Fin.cases ?_ (fun index => Fin.elim0 index) index
    change next.preparation.cell.request.models.valueOne.eval point = coordinatePolynomial.eval point *
      (next.preparation.cell.request.model.value.eval point) ^ 1
    simpa only [pow_one, -eq_self, -iff_self] using
      IntegrandRequests.valueOne_readback next.preparation.cell.request.models point

/-- All actual allocations, source/Point/domain views and numerical outcomes of one requested value crop.

The final NumericalConsumer is the existing original numerical cache
interface. Private coefficient proof implementations do not occur in this
public type: both actual pointwise witnesses are forwarded as proof values.
-/
abbrev RequestedConsumer (Result : Type u) : Type _ :=
  let numerator := (valueSpecification parameter coordinate).numerator
  let ratio := PreparedParent.initialRatio prepared
  let scale := Rectangular.powerScale cachedBounds.val 1
  let size := Budget.Aggregate.countCoordinate split.count
  let movement := normSq (parent.edge.point upper - parent.edge.point lower)
  let sourceScale := size * movement * (96 + 32 * ratio * scale)
  let residualScale := 128 * size * scale * movement / 256
  let share := goal.tolerance / 4
  let target := Budget.Aggregate.perTerm share split.count / 32
  (source : Selection sourceScale sourceFloor share) →
  (_source_factory : source = Selection.build sourceScale source.scaleNonnegative sourceFloor
    share source.targetPositive) →
  (residual : Selection residualScale gridFloor share) →
  (_residual_factory : residual = Selection.build residualScale residual.scaleNonnegative gridFloor
    share residual.targetPositive) →
  (gluingPositive : 0 < target) →
  (glue : GridPrimitiveAccuracy ambientBounds domain.steps target) →
  (_glue_factory : glue = GridPrimitiveAccuracy.build ambientBounds domain.steps target gluingPositive) →
  (original : GridPrimitiveAccuracy ambientBounds domain.steps target) →
  (_original_factory : original = glue.after residual.stage) →
  (_grid_floor : gridFloor ≤ original.index) →
  (newTargets : CellEndpoints.Targets originalPath source.stage) →
  (_targets_factory : newTargets = CellEndpoints.Targets.build originalPath source.stage) →
  (next : PreparedParent patch count (Nat.max 2 sourceFloor) covered newTargets) →
  (_prepared_factory : next = prepareParent (frame := frame) patch count
    (Nat.max 2 sourceFloor) covered newTargets) →
  (_floor_two : 2 ≤ Nat.max 2 sourceFloor) →
  (_requested_floor : sourceFloor ≤ Nat.max 2 sourceFloor) →
  (vertices : ∀ first last, (operation.2 first last).vertices = [parent.edge.point upper]) →
  (fresh : Crop.Acquisition (frame := frame) (basis := basis) (row := row)
    (accuracy := Primitive.localRequest newRequested 3) next lower upper lowerInside upperInside operation
    newComparisonRequest newRequested) →
  (_acquisition_factory : fresh = Crop.Acquisition.build (frame := frame) (basis := basis) (row := row)
    (accuracy := Primitive.localRequest newRequested 3) next lower upper lowerInside upperInside operation
    vertices newComparisonRequest newRequested) →
  (_first_point : points.samples.1.val = fresh.2.2.samples.1.val) →
  (_last_point : points.samples.2.val = fresh.2.2.samples.2.val) →
  (firstOwner : points.samples.1.val.owner = fresh.2.2.samples.1.val.owner) →
  (_last_owner : points.samples.2.val.owner = fresh.2.2.samples.2.val.owner) →
  (viewAcquired : Entry.Acquisition shared.models firstInside fresh.2.2.samples.1.val.owner) →
  (_acquired_factory : viewAcquired = Entry.Acquisition.castPoint
    (models := shared.models) (lastInside := firstInside) rfl (heq_of_eq firstOwner) acquired) →
  HEq viewAcquired acquired → (sameSheet : viewAcquired.entry.sheet = acquired.entry.sheet) →
  (view : PeriodDomain shared.models viewAcquired.entry.sheet) →
  (_domain_factory : view = PeriodDomain.castSheet sameSheet.symm domain) →
  HEq view domain → (stepsSame : view.steps = domain.steps) →
  (viewSplit : SegmentSplit view.cuts (parent.edge.point lower) (parent.edge.point upper)) →
  HEq viewSplit split → viewSplit.count = split.count →
  (viewBounds : {value : Rectangular face.clearance view.geometry view.patch.cell_refines numerator //
    value = Rectangular.build face.clearance view.geometry view.patch.cell_refines numerator}) →
  HEq viewBounds cachedBounds →
  (_source_scale_eq : sourceScale = Budget.Aggregate.countCoordinate viewSplit.count * movement *
    (96 + 32 * (next.preparation.cell.patch.base.model.bound /
      (2 * next.preparation.cell.patch.inverseErrorScale)) * Rectangular.powerScale viewBounds.val 1)) →
  (_residual_scale_eq : residualScale = 128 * Budget.Aggregate.countCoordinate viewSplit.count *
    Rectangular.powerScale viewBounds.val 1 * movement / 256) →
  (_target_eq : target = Budget.Aggregate.perTerm share viewSplit.count / 32) →
  (parentEvaluation : ∀ input : Rational,
    Evaluation.eval (next.preparation.cell.models.cell (valueIndex coordinate)).polynomial ⟨input, 0⟩ =
      (next.preparation.cell.request.models.value coordinate).eval
        (next.preparation.cell.models.coordinate.point input)) →
  (sourceCompiled : ∀ point : Canonical, (next.preparation.cell.request.models.value coordinate).eval point =
    numerator.eval point * (next.preparation.cell.request.model.value.eval point) ^ 1) →
  (request : GridPrimitiveAccuracy ambientBounds view.steps target) →
  (_request_factory : request = GridPrimitiveAccuracy.castColumns stepsSame.symm original) → HEq request original →
  request.index = original.index → request.globalBound = original.globalBound →
  NumericalConsumer (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (sourceFloor := sourceFloor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (goal := goal)
    (source := source) (targets := newTargets) (row := row) (accuracy := Primitive.localRequest newRequested 3)
    (prepared := next) (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := fresh.1) (comparisonRequest := newComparisonRequest)
    (requested := newRequested) (observed := fresh.2.1) (points := fresh.2.2)
    (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames) (face := face)
    (shared := shared) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := viewAcquired) (domain := view) (split := viewSplit) (numerator := numerator)
    (ambientBounds := ambientBounds) (cachedBounds := viewBounds) (channel := valueIndex coordinate) (gap := gap)
    (next.preparation.cell.request.models.value coordinate) parentEvaluation sourceCompiled request Result

/-- Allocate before acquisition, refresh the actual source once, and derive requested value accuracy on the SAME caches.

The source/residual scales are rewritten only as rational scalar identities
using the original initial-patch and whole domain/cache factory readbacks.
Neither Selection nor any model is reindexed. The actual Point/crop/payment
outcomes are retained before the numerical executor runs once. Both value
coordinates use original cached coefficient/table witnesses constructed
internally, without source/Owner/normalization/error conclusions as inputs.
-/
def withRequested
    (preparedFactory : prepared = prepareParent (frame := frame) patch count oldFloor covered oldTargets)
    {Result : Type u}
    (consume : RequestedConsumer (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      coordinate cachedBounds ambientBounds sourceFloor gridFloor goal newComparisonRequest newRequested gap Result) :
    Result :=
  let numerator := (valueSpecification parameter coordinate).numerator
  withAllocation (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (oldFloor := oldFloor) (covered := covered)
    (start := baseStart) (finish := baseFinish) (original := originalPath) (oldStage := oldStage)
    (oldTargets := oldTargets)
    (branches := branches) (higher := higher) (bank := bank) (frames := rootFrames) (face := face)
    (models := shared.models) (sheet := acquired.entry.sheet)
    (numerator := numerator)
    prepared domain lower upper split cachedBounds ambientBounds sourceFloor gridFloor goal
    (fun source sourceFactory residual residualFactory gluingPositive glue glueFactory original originalFactory
        gridPaid newTargets targetsFactory _sourceTwo _sourceFloor _sourcePaid _residualPaid _gluingPaid _costsPaid =>
      withPreparation (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
        (patch := patch) (count := count) (floor := oldFloor) (covered := covered)
        (baseStart := baseStart) (baseFinish := baseFinish) (original := originalPath) (stage := oldStage)
        (targets := oldTargets) (row := row) (accuracy := accuracy) (prepared := prepared)
        (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
        (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
        (observed := observed) (points := points) (branches := branches) (higher := higher) (bank := bank)
        (rootFrames := rootFrames) (face := face) (models := shared.models) (firstInside := firstInside)
        (acquired := acquired) (domain := domain) (split := split) (cachedBounds := cachedBounds)
        (numerator := numerator)
        preparedFactory sourceFloor newTargets newComparisonRequest newRequested
        (fun next nextFactory floorTwo requestedFloor vertices fresh freshFactory firstPoint lastPoint
            firstOwner lastOwner viewAcquired acquiredFactory acquiredSame sameSheet view domainFactory
            domainSame stepsSame viewSplit splitSame countSame viewBounds boundsSame =>
          let movement := normSq (parent.edge.point upper - parent.edge.point lower)
          have ratioEq := (PreparedParent.initialRatio_eq_of_patch (parameter := parameter) (frame := frame)
            (basis := basis) (parent := parent) (patch := patch) (count := count) (covered := covered)
            (firstFloor := oldFloor) (lastFloor := Nat.max 2 sourceFloor) (firstStage := oldStage)
            (lastStage := source.stage) (firstPath := originalPath) (lastPath := originalPath)
            (firstTargets := oldTargets) (lastTargets := newTargets) prepared next).trans
              (PreparedParent.initialRatio_eq (parameter := parameter) (frame := frame) (basis := basis)
                (parent := parent) (patch := patch) (count := count) (floor := Nat.max 2 sourceFloor)
                (covered := covered) (targets := newTargets) next)
          have scaleEq := view_powerScale_eq (parameter := parameter) (frame := frame) (branches := branches)
            (higher := higher) (bank := bank) (rootFrames := rootFrames) (face := face) (shared := shared)
            sameSheet.symm domain view domainFactory cachedBounds viewBounds boundsSame
          have sizeEq := congrArg Budget.Aggregate.countCoordinate countSame.symm
          have sourceEq := (congrArg (fun size : Rational => size * movement *
              (96 + 32 * PreparedParent.initialRatio prepared *
                Rectangular.powerScale cachedBounds.val 1)) sizeEq).trans
            ((congrArg (fun ratio : Rational => Budget.Aggregate.countCoordinate viewSplit.count * movement *
              (96 + 32 * ratio * Rectangular.powerScale cachedBounds.val 1)) ratioEq).trans
              (congrArg (fun scale : Rational => Budget.Aggregate.countCoordinate viewSplit.count * movement *
                (96 + 32 * (next.preparation.cell.patch.base.model.bound /
                  (2 * next.preparation.cell.patch.inverseErrorScale)) * scale)) scaleEq.symm))
          have residualEq := (congrArg (fun size : Rational =>
            128 * size * Rectangular.powerScale cachedBounds.val 1 * movement / 256) sizeEq).trans
              (congrArg (fun scale : Rational =>
                128 * Budget.Aggregate.countCoordinate viewSplit.count * scale * movement / 256) scaleEq.symm)
          have targetEq := congrArg (fun size : Nat => Budget.Aggregate.perTerm (goal.tolerance / 4) size / 32)
            countSame.symm
          let parentEvaluation := value_parentEvaluation (parameter := parameter) (frame := frame) (basis := basis)
            (parent := parent) (patch := patch) (count := count) (covered := covered)
            (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath)
            (nextFloor := Nat.max 2 sourceFloor) (nextStage := source.stage) (nextTargets := newTargets) next coordinate
          let sourceCompiled := value_sourceCompiled (parameter := parameter) (frame := frame) (basis := basis)
            (parent := parent) (patch := patch) (count := count) (covered := covered)
            (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath)
            (nextFloor := Nat.max 2 sourceFloor) (nextStage := source.stage) (nextTargets := newTargets) next coordinate
          withNumerics (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
            (patch := patch) (count := count) (sourceFloor := sourceFloor) (covered := covered)
            (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (goal := goal)
            (source := source) (residual := residual) (residualFloor := gridFloor)
            (targets := newTargets) (row := row)
            (accuracy := Primitive.localRequest newRequested 3) (prepared := next)
            (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
            (operation := operation) (cropped := fresh.1) (comparisonRequest := newComparisonRequest)
            (requested := newRequested) (observed := fresh.2.1) (points := fresh.2.2)
            (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames) (face := face)
            (shared := shared) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
            (acquired := viewAcquired) (domain := view) (split := viewSplit)
            (numerator := numerator)
            (ambientBounds := ambientBounds) (cachedBounds := viewBounds)
            (channel := valueIndex coordinate) (gap := gap)
            (next.preparation.cell.request.models.value coordinate) parentEvaluation sourceCompiled
            glue original originalFactory stepsSame.symm sourceEq residualEq targetEq
            (fun request requestFactory requestSame indexSame globalSame =>
              consume source sourceFactory residual residualFactory gluingPositive glue glueFactory original
                originalFactory gridPaid newTargets targetsFactory next nextFactory floorTwo requestedFloor
                vertices fresh freshFactory firstPoint lastPoint firstOwner lastOwner viewAcquired acquiredFactory
                acquiredSame sameSheet view domainFactory domainSame stepsSame viewSplit splitSame countSame
                viewBounds boundsSame sourceEq residualEq targetEq parentEvaluation sourceCompiled request
                requestFactory requestSame indexSame globalSame)))

end UniformPieces.Chord.SharedMesh

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
