module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform
public import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Data.Except
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.Map
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Curves.Legendre.Periods.Jets.Models
import Purelib.Tactic.Ring

/-! # Ordered whole-crop comparisons on the same retained rectangle pieces

Every literal split occurrence keeps its actual old coefficient, primitive
and selected UniformPiece. The same source restrictions reassemble exactly;
finite Cauchy then compares the whole source integral to the ordered sum of
those independent primitives' endpoint differences. No constants are
identified across different pieces. An insufficient original source stage
retains the actual future Selection and all original unresolved pieces.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation UniformCellCertificate)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.InverseModels.BranchCellBank (FaceModels)
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Polynomial.Dense.Gaussian.Basic (constantOnePolynomial coordinatePolynomial)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit SegmentPiece GridCuts)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Polynomial.Ascending.Gaussian

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
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
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank} {oldModels : FaceModels rootFrames face}
    (prefixes : PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside)
    (ordered : lower ≤ upper) (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition oldModels firstInside points.samples.1.val.owner)
    (domain : PeriodDomain oldModels acquired.entry.sheet)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))

open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {channel : Fin 6} {exponent targetIndex : Nat}
    {oldBank : Bank (Paths.polynomial parameter) domain.geometry}
    {numerator : Polynomial} {gap : AccuracyRequest}
    (targetSources : Fin split.pieces.length → Polynomial)

/-- The original coefficient and dense primitive cached at every literal split occurrence.

The polynomial is a retained runtime value with its exact original readback.
Each primitive has that SAME coefficient and actual cell box as its indices;
independent additive constants and repeated cell visits remain separate.
-/
abbrev PieceTargets :=
  DependentVector (fun position : Fin split.pieces.length =>
    Σ coefficient : {value : Polynomial // value = targetSources position},
      DensePrimitive coefficient.val
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))

/-- One actual original preparation outcome and its unchanged selected success payload. -/
abbrev CheckedPiece (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources)
    (position : Fin split.pieces.length) :=
  Σ outcome : Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator (keptTargets.get position).1.val exponent targetIndex gap),
    {value : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator (keptTargets.get position).1.val exponent targetIndex gap // outcome = .ok value}

/-- The complete ordered successful preparation cache on the same retained target coefficients and primitives. -/
abbrev UniformPieces (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources) :=
  DependentVector (fun position : Fin split.pieces.length =>
    CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets position)

/-- The exact whole-crop success payload retains both the original targets and every same selected piece cache. -/
abbrev PieceCompletion :=
  Σ keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources,
    UniformPieces (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets

/-- A whole-crop preparation retains all original targets in both its success and insufficient-stage branches.

The error payload retains one genuine future source Selection and the SAME
complete list of unresolved split occurrences. No source model, source
query, Point, or primitive is rebuilt to promote an old stage.
-/
abbrev PiecePreparation :=
  Except
    (Σ _targets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources,
      SourceFloor (prepared := prepared) ×
        {unresolved : List (SegmentPiece domain.geometry (parent.edge.point lower) (parent.edge.point upper)) //
          unresolved = split.pieces})
    (PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)

namespace PiecePreparation

/-- Read the SAME entire retained target vector in either success or insufficient-stage execution outcome. -/
def targetBank :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources →
    PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources
  | .error failed => failed.1
  | .ok completed => completed.1

/-- The complete target-vector factory of one actual outcome, retaining coefficients and full primitive constants. -/
abbrev TargetFactory
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row)) : Prop :=
  targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
    (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
    (targetSources := targetSources) outcome =
      DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩)

/-- The actual accepted payload reads the target vector from that SAME whole original outcome. -/
theorem accepted_targets_eq
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (accepted : outcome = .ok completed) :
    completed.1 = targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources) outcome :=
  (congrArg (targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
    (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
    (targetSources := targetSources)) accepted).symm

/-- Extract the SAME complete original crop outcome when its retained construction floor was already at least two.

Every target and local selected outcome remains the supplied original
cache. The error is refuted by its own SourceFloor stopping reason;
no per-piece preparation or model/query factory executes here.
-/
def success
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (floorPaid : 2 ≤ floor) :
    {value : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources //
      outcome = .ok value} :=
  Except.requireSuccess outcome (fun failure => SourceFloor.impossible (prepared := prepared) failure.2.1 floorPaid)

/-- The retained complete crop cache is the exact success payload of that identical original outcome. -/
theorem success_eq
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (floorPaid : 2 ≤ floor) : outcome = .ok (success (points := points) (firstInside := firstInside) (acquired :=
      acquired)
      (domain := domain) (split := split) (targetSources := targetSources) (outcome := outcome) (floorPaid :=
        floorPaid)).val :=
  (success (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := targetSources) (outcome := outcome) (floorPaid :=
        floorPaid)).property

/-- Paid-stage success extraction preserves the whole original target vector and every original primitive constant. -/
theorem success_targets
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (floorPaid : 2 ≤ floor) :
    (success (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources) outcome floorPaid).val.1 =
      targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
        (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
        (targetSources := targetSources) outcome :=
  (congrArg (targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
    (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
    (targetSources := targetSources))
    (success_eq (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources) outcome floorPaid)).symm

end PiecePreparation

/-- Bind one genuine piece outcome once and extract its original success from the paid source stage. -/
private def prepareCheckedPiece
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources)
    (paid : 2 ≤ prepared.preparation.cell.request.selection.stage) (position : Fin split.pieces.length) :
    CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets position :=
  let coefficient := (keptTargets.get position).1
  let outcome := preparePiece (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource coefficient.val exponent gap
    parentEvaluation sourceCompiled
    (fun point => (congrArg (fun polynomial : Polynomial => polynomial.eval point) coefficient.property).trans
      (targetCompiled position point))
  let accepted := Except.requireSuccess outcome (fun failure => failure.property.2 paid)
  ⟨outcome, accepted⟩

/-- Share the original whole-crop target/check/error branch with a retained per-piece producer. -/
private def preparePiecesWith
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (makePiece : (keptTargets : PieceTargets (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) targetSources) →
      2 ≤ prepared.preparation.cell.request.selection.stage → (position : Fin split.pieces.length) →
      CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
        (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
        targetSources keptTargets position) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources :=
  let keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources :=
    DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩)
  if paid : 2 ≤ prepared.preparation.cell.request.selection.stage then
    let pieces := DependentVector.ofFn (fun position =>
      makePiece keptTargets paid position)
    .ok ⟨keptTargets, pieces⟩
  else
    let future := Selection.build prepared.preparation.cell.cache.scale
      prepared.preparation.cell.request.selection.scaleNonnegative
      (max 2 prepared.preparation.cell.request.selection.stage) prepared.preparation.cell.target
      prepared.preparation.cell.request.selection.targetPositive
    .error ⟨keptTargets, ⟨future, rfl, paid⟩, ⟨split.pieces, rfl⟩⟩

/-- Retain one actual successful piece constructed from its SAME pre-stage rectangular bounds cache. -/
private def prepareCheckedPieceWithBounds
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources)
    (paid : 2 ≤ prepared.preparation.cell.request.selection.stage) (position : Fin split.pieces.length)
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator}) :
    CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets position :=
  let coefficient := (keptTargets.get position).1
  let outcome := preparePieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource coefficient.val exponent gap
    parentEvaluation sourceCompiled
    (fun point => (congrArg (fun polynomial : Polynomial => polynomial.eval point) coefficient.property).trans
      (targetCompiled position point)) cachedBounds
  let accepted := Except.requireSuccess outcome (fun failure => failure.property.2 paid)
  ⟨outcome, accepted⟩

/-- The same checked cache reads the actual selected pre-stage rectangular bound. -/
private theorem checkedPieceWithBounds_bound
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources)
    (paid : 2 ≤ prepared.preparation.cell.request.selection.stage) (position : Fin split.pieces.length)
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator}) :
    (prepareCheckedPieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap)
      targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position
      cachedBounds).2.val.2.2.1 =
      Rectangular.entry cachedBounds.val (auxiliaryPiece split position).column
        (auxiliaryPiece split position).row := by
  let coefficient := (keptTargets.get position).1
  let outcome := preparePieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource coefficient.val exponent gap
    parentEvaluation sourceCompiled
    (fun point => (congrArg (fun polynomial : Polynomial => polynomial.eval point) coefficient.property).trans
      (targetCompiled position point)) cachedBounds
  let accepted := Except.requireSuccess outcome (fun failure => failure.property.2 paid)
  change accepted.val.2.2.1 =
    Rectangular.entry cachedBounds.val (auxiliaryPiece split position).column (auxiliaryPiece split position).row
  exact preparePieceWithBounds_bound (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource coefficient.val exponent gap
    parentEvaluation sourceCompiled
    (fun point => (congrArg (fun polynomial : Polynomial => polynomial.eval point) coefficient.property).trans
      (targetCompiled position point)) cachedBounds outcome rfl accepted.val accepted.property

/-- Prepare every original piece once, or retain its entire original unresolved occurrence bank.

Original target values are stored before any local preparation. A source
below stage two selects ONE genuine future floor and returns all unresolved
pieces. Otherwise each call of the original preparePiece is bound once,
and its actual outcome and selected cache remain retained together.
-/
def preparePieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row)) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources :=
  preparePiecesWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
    (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
    (targetSources := targetSources)
    primitives (fun keptTargets paid position =>
      prepareCheckedPiece (points := points) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
        (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
        (targetIndex := targetIndex) (gap := gap)
        targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position)

/-- Prepare all literal crop occurrences from the SAME pre-stage rectangular bounds cache.

Targets are retained before the original source-stage check. A source
below two returns the unchanged original future-floor request and all
unresolved pieces. Otherwise each actual piece outcome is computed once
through preparePieceWithBounds, retaining its original accepted payload.
The shared whole branch never rebuilds a bound, source model or Point.
-/
def preparePiecesWithBounds
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator}) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources :=
  preparePiecesWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
    (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
    (targetSources := targetSources)
    primitives (fun keptTargets paid position =>
      prepareCheckedPieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
        (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
        (targetIndex := targetIndex) (gap := gap)
        targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position
        cachedBounds)

namespace PiecePreparation

/-- The shared actual whole branch retains its complete original target vector in either outcome. -/
private theorem targetsWith_eq
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (makePiece : (keptTargets : PieceTargets (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) targetSources) →
      2 ≤ prepared.preparation.cell.request.selection.stage → (position : Fin split.pieces.length) →
      CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
        (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
        targetSources keptTargets position) :
    TargetFactory (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources)
      (preparePiecesWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
        (patch := patch) (count := count) (floor := floor) (covered := covered)
        (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
        (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
        (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
        (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
        (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
        (face := face) (oldModels := oldModels) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
        (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
        (targetSources := targetSources) primitives makePiece) primitives := by
  unfold TargetFactory preparePiecesWith
  by_cases paid : 2 ≤ prepared.preparation.cell.request.selection.stage
  · rewrite [dif_pos paid]
    rfl
  · rewrite [dif_neg paid]
    rfl

/-- Recover the exact complete original target factory from the SAME once-bound preparation outcome.

Both branches retain the original dependent vector built before any
piece preparation. The equation preserves full coefficients and complete
DensePrimitive records, including their actual additive constants. It
uses the supplied whole execution identity and does not execute any
preparation, query or numerical reader again.
-/
theorem targets_eq
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (factory : outcome = preparePieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap) targetSources oldBankEq originalSource parentEvaluation
      sourceCompiled targetCompiled primitives) :
    targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources) outcome =
        DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩) := by
  have same := congrArg
    (targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources)) factory
  exact same.trans (targetsWith_eq (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources)
    primitives (fun keptTargets paid position =>
      prepareCheckedPiece (points := points) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
        (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
        (targetIndex := targetIndex) (gap := gap)
        targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid
          position))

/-- Recover the SAME complete target-vector factory from an actual retained-bounds preparation outcome.

Only its own original producer equation is consumed. Coefficients, full
DensePrimitive records and their constants stay attached to that actual
outcome; no old-producer equality or numerical comparison is assumed.
-/
theorem targetsWithBounds_eq
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (factory : outcome = preparePiecesWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap) targetSources oldBankEq originalSource parentEvaluation
      sourceCompiled targetCompiled primitives cachedBounds) :
    targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources) outcome =
        DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩) := by
  have same := congrArg
    (targetBank (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources)) factory
  exact same.trans (targetsWith_eq (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      (targetSources := targetSources)
    primitives (fun keptTargets paid position =>
      prepareCheckedPieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
        (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
        (targetIndex := targetIndex) (gap := gap)
        targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position
        cachedBounds))

/-- A GIVEN whole retained-bounds outcome keeps the SAME selected rectangular bound at every literal occurrence.

The actual complete outcome, its producer equation and accepted payload
are retained inputs. The proof reads its original dependent vector and
per-piece successful caches; no preparation or bound factory executes.
-/
theorem bounds_eq
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ position (point : Canonical), (targetSources position).eval point =
      numerator.eval point *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
          point) ^ exponent)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (factory : outcome = preparePiecesWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap)
      targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled primitives cachedBounds)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources)
    (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length) :
    (completed.2.get position).2.val.2.2.1 =
        Rectangular.entry cachedBounds.val (auxiliaryPiece split position).column
        (auxiliaryPiece split position).row := by
  let keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources :=
    DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩)
  have actual := factory.symm.trans accepted
  unfold preparePiecesWithBounds preparePiecesWith at actual
  split at actual
  next paid =>
    have paired := Except.ok.inj actual
    have selected := congrArg (fun value : PieceCompletion (points := points) (firstInside := firstInside)
      (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap) targetSources =>
      (value.2.get position).2.val.2.2.1) paired.symm
    have read := DependentVector.ofFn_get (fun position =>
      prepareCheckedPieceWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap)
      targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position
      cachedBounds) position
    have selectedBound := checkedPieceWithBounds_bound (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (channel := channel) (oldBank := oldBank) (numerator := numerator) (exponent := exponent)
      (targetIndex := targetIndex) (gap := gap)
      targetSources oldBankEq originalSource parentEvaluation sourceCompiled targetCompiled keptTargets paid position
      cachedBounds
    exact selected.trans ((congrArg (fun value : CheckedPiece (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets position => value.2.val.2.2.1) read).trans selectedBound)
  next _unpaid => cases actual

end PiecePreparation

namespace UniformPieces

variable {targetSources}
    {keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources}
    (pieces : UniformPieces (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets)

/-- Read one actual selected original preparation outcome at its literal split occurrence. -/
abbrev checked (position : Fin split.pieces.length) :
    CheckedPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel) (oldBank := oldBank)
      (numerator := numerator) (exponent := exponent) (targetIndex := targetIndex) (gap := gap)
      targetSources keptTargets position := pieces.get position

/-- Read the SAME successful local cache without rerunning its preparation or queries. -/
abbrev entry (position : Fin split.pieces.length) :
    UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel oldBank numerator (keptTargets.get position).1.val exponent targetIndex gap :=
  (checked (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position).2.val

/-- The retained local success is the actual payload of that SAME original preparation outcome. -/
theorem outcome_eq (position : Fin split.pieces.length) :
    (checked (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position).1 = .ok (entry (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position) :=
  (checked (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position).2.property

/-- Read the independent actual primitive retained for this occurrence's original target coefficient. -/
abbrev primitive (position : Fin split.pieces.length) :
    DensePrimitive (keptTargets.get position).1.val
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row) :=
  (keptTargets.get position).2

/-- The original source restriction integral at each literal retained piece. -/
def sourceSamples (position : Fin split.pieces.length) : Canonical :=
  (UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := entry (points := points) (firstInside :=
      firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position)).integralSample

/-- Read the actual source restriction integral at the same retained original piece position. -/
theorem sourceSamples_eq (position : Fin split.pieces.length) :
    sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := targetSources)
      (keptTargets := keptTargets) (pieces := pieces) position =
    (UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      (data := entry (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := targetSources)
        (keptTargets := keptTargets) (pieces := pieces) position)).integralSample := by
  unfold sourceSamples
  rfl

/-- The actual independent primitive endpoint difference at each same retained ordered piece. -/
@[expose] def increments (position : Fin split.pieces.length) : Canonical :=
  (primitive (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets)
      position).value.eval (auxiliaryPiece split position).lastPoint -
    (primitive (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets)
      position).value.eval (auxiliaryPiece split position).firstPoint

/-- The actual local integral-comparison allowance and physical displacement, with no requested decay assumed. -/
@[expose] def localBounds (position : Fin split.pieces.length) : Rational :=
  16 * ((UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := entry (points := points) (firstInside :=
      firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position)).localAllowance +
    (UniformPiece.target (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := entry (points := points) (firstInside :=
      firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position)).model.localAllowance) *
    normSq (UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := entry (points := points) (firstInside :=
      firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position)).displacement

/-- Sum the independent retained primitive increments in literal original occurrence order. -/
def sample : Canonical := sumFin (increments (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets))

/-- The original finite Cauchy allowance retains the actual count and all actual local model payments. -/
def bound : Rational := (split.pieces.length : Rational) * sumFin (localBounds (points := points) (firstInside :=
  firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces))

/-- The same retained source restriction samples recover the original outer crop integral exactly.

The original partition walk is used only as exact finite incidence. Each
restriction supplies its own integral readback; no replacement coefficient,
restriction table or physical endpoint cache is constructed.
-/
theorem source_integral_eq :
    sumFin (sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces)) = (cropped.models.cell channel).integralSample := by
  let cell := cropped.models.cell channel
  let value : Rational → Canonical := fun input =>
    cell.displacement * Evaluation.eval (Antiderivative.antiderivative cell.polynomial)
      (Cast.Path.ofCoordinate input)
  let jump : Interval → Canonical := fun interval => value interval.upper - value interval.lower
  have scalars : sumFin (sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces)) = sumFin (fun position : Fin split.pieces.length =>
      value (auxiliaryPiece split position).interval.upper - value (auxiliaryPiece split position).interval.lower) :=
    sumFin_congr (fun position => by
      have actual := Cell.Restriction.integralSample_eq cell (UniformPiece.restricted (points := points) (firstInside
        := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := entry (points := points) (firstInside :=
      firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position))
      exact actual.trans (by unfold value Integral.definiteIntegral; ring1))
  have listed := Norm.Sum.Indexed.sumFin_map split.pieces (fun piece => jump piece.interval)
  have mapped := congrArg Norm.Sum.Basic.gaussianSum
    (Map.map_map jump SegmentPiece.interval split.pieces).symm
  have intervals := congrArg (fun intervals : List Interval => Norm.Sum.Basic.gaussianSum (intervals.map jump))
    split.intervals_eq
  have walking := congrArg (fun intervals : List Interval => Norm.Sum.Basic.gaussianSum (intervals.map jump))
    split.partition.walk_edges
  have whole := SegmentSplit.intervals_telescope value split.partition.walk
  have endpoint : value 1 - value 0 = cell.integralSample := by
    unfold value CellModel.integralSample Integral.definiteIntegral
    change cell.displacement *
        Evaluation.eval (Antiderivative.antiderivative cell.polynomial) (1 : Canonical) -
      cell.displacement * Evaluation.eval (Antiderivative.antiderivative cell.polynomial) (0 : Canonical) =
        cell.displacement *
          (Evaluation.eval (Antiderivative.antiderivative cell.polynomial) (1 : Canonical) -
            Evaluation.eval (Antiderivative.antiderivative cell.polynomial) (0 : Canonical))
    ring1
  exact scalars.trans (listed.trans (mapped.trans (intervals.trans (walking.symm.trans (whole.trans endpoint)))))

/-- The whole original source integral is quantitatively close to the SAME ordered primitive increment sum.

Every local root relation and model allowance is constructed internally by
its actual retained UniformPiece. Finite Cauchy preserves all occurrences,
including stationary or repeated geometry. Distinct primitive constants are
never identified; each difference uses its own one retained primitive.
-/
theorem integral_difference_le :
    normSq ((cropped.models.cell channel).integralSample - (sample (points := points) (firstInside := firstInside)
      (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets))) ≤
      (bound (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces)) := by
  have perPiece : ∀ position : Fin split.pieces.length,
      normSq ((sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position) - (increments (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) position)) ≤
        (localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position) :=
    fun position => by
      unfold sourceSamples increments localBounds
      exact UniformPiece.primitive_increment_le (points := points) (firstInside := firstInside)
        (acquired := acquired) (domain := domain) (split := split) (position := position)
        (data := entry (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces) position) (primitive := primitive (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) position)
  have finite := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    (sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces))
    (increments (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets))
    (localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces :=
      pieces)) perPiece
  have source := source_integral_eq (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) (pieces := pieces)
  unfold sample bound
  exact (congrArg (fun value : Canonical => normSq (value - sumFin (increments (points := points) (firstInside :=
    firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets))))
      source).symm.trans_le
    finite

end UniformPieces

/-- Prepare the actual dx/y source crop against the SAME retained old polynomial primitive bank.

The source channel and its original spatial/model readbacks are selected
internally. Each literal split occurrence retains its old bank coefficient
and primitive as separate actual data, including repeated visits.
-/
def prepareValueZeroPieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank constantOnePolynomial) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
    (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
    (fun position =>
      (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient)
    oldBankEq prepared.preparation.cell.request.models.valueZero
    (fun input => prepared.preparation.cell.models.valueZero.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueZero_readback prepared.preparation.cell.request.models point)
    (fun position point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        primitives.coefficient_eq (auxiliaryPiece split position).column (auxiliaryPiece split position).row point)
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)

/-- Prepare the actual x dx/y source crop using its coordinate numerator and the independent old primitive bank.

The original full-numerator coefficient is retained. This is the actual
second Legendre value channel, without relabelling it as a genus-one
holomorphic differential or identifying independent primitive constants.
-/
def prepareValueOnePieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank coordinatePolynomial) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
    (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
    (fun position =>
      (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient)
    oldBankEq prepared.preparation.cell.request.models.valueOne
    (fun input => prepared.preparation.cell.models.valueOne.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueOne_readback prepared.preparation.cell.request.models point)
    (fun position point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        primitives.coefficient_eq (auxiliaryPiece split position).column (auxiliaryPiece split position).row point)
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)

namespace UniformPieces

/-- Exact whole-target identity preserves each actual primitive's endpoint increment, including its own constant. -/
theorem increment_eq
    (keptTargets : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources)
    (primitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (targetSources position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (same : keptTargets =
      DependentVector.ofFn (fun position => ⟨⟨targetSources position, rfl⟩, primitives position⟩))
    (position : Fin split.pieces.length) :
    UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := targetSources) (keptTargets := keptTargets) position =
      (primitives position).value.eval (auxiliaryPiece split position).lastPoint -
        (primitives position).value.eval (auxiliaryPiece split position).firstPoint := by
  have retained := congrArg
    (fun actual : PieceTargets (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) targetSources =>
      (actual.get position).2.value.eval (auxiliaryPiece split position).lastPoint -
        (actual.get position).2.value.eval (auxiliaryPiece split position).firstPoint) same
  have selected := DependentVector.ofFn_get
    (fun position : Fin split.pieces.length =>
      (⟨⟨targetSources position, rfl⟩, primitives position⟩ :
        Σ coefficient : {value : Polynomial // value = targetSources position},
          DensePrimitive coefficient.val
            (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row)))
    position
  exact retained.trans (congrArg
    (fun actual : Σ coefficient : {value : Polynomial // value = targetSources position},
      DensePrimitive coefficient.val
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row) =>
      actual.2.value.eval (auxiliaryPiece split position).lastPoint -
        actual.2.value.eval (auxiliaryPiece split position).firstPoint) selected)

end UniformPieces

/-- The actual value-0 outcome retains the complete original primitive-vector factory. -/
theorem prepareValueZeroPieces_targets
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank constantOnePolynomial)
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (factory : outcome = prepareValueZeroPieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (oldBank := oldBank) (targetIndex := targetIndex) (gap := gap) oldBankEq primitives) :
    PiecePreparation.TargetFactory (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
      outcome
      (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row) :=
    PiecePreparation.targets_eq (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
    (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
    (fun position =>
      (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient)
    oldBankEq prepared.preparation.cell.request.models.valueZero
    (fun input => prepared.preparation.cell.models.valueZero.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueZero_readback prepared.preparation.cell.request.models point)
    (fun position point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        primitives.coefficient_eq (auxiliaryPiece split position).column (auxiliaryPiece split position).row point)
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
      outcome factory

/-- The actual value-0 success retains each original supplied primitive increment exactly.

The original dx/y preparation and accepted whole outcome remain actual
inputs. Full target-vector identity, rather than coefficient equality,
recovers each SAME supplied dense primitive with all constants intact.
-/
theorem prepareValueZeroPieces_increment
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank constantOnePolynomial)
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (factory : outcome = prepareValueZeroPieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (oldBank := oldBank) (targetIndex := targetIndex) (gap := gap) oldBankEq primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (accepted : outcome = .ok completed) (position : Fin split.pieces.length) :
    UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
      (keptTargets := completed.1) position =
      (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
          (auxiliaryPiece split position).lastPoint -
        (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
          (auxiliaryPiece split position).firstPoint := by
  have selected := PiecePreparation.accepted_targets_eq (points := points) (firstInside := firstInside)
    (acquired := acquired)
      (domain := domain) (split := split) (channel := 0) (oldBank := oldBank)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    outcome completed accepted
  have original := prepareValueZeroPieces_targets (points := points) (prefixes := prefixes)
    (ordered := ordered) (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
    (targetIndex := targetIndex) (gap := gap) oldBankEq primitives outcome factory
  exact UniformPieces.increment_eq (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    completed.1
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    (selected.trans original) position

/-- The actual value-1 outcome retains the complete original primitive-vector factory. -/
theorem prepareValueOnePieces_targets
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank coordinatePolynomial)
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (factory : outcome = prepareValueOnePieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (oldBank := oldBank) (targetIndex := targetIndex) (gap := gap) oldBankEq primitives) :
    PiecePreparation.TargetFactory (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
      outcome
      (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row) :=
    PiecePreparation.targets_eq (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
    (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
    (fun position =>
      (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient)
    oldBankEq prepared.preparation.cell.request.models.valueOne
    (fun input => prepared.preparation.cell.models.valueOne.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueOne_readback prepared.preparation.cell.request.models point)
    (fun position point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        primitives.coefficient_eq (auxiliaryPiece split position).column (auxiliaryPiece split position).row point)
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
      outcome factory

/-- The actual value-1 success retains each original supplied primitive increment exactly.

The original x dx/y preparation retains its arbitrary coordinate numerator.
Full target identity recovers the SAME supplied primitives and constants.
No genus-one holomorphic differential or primitive normalization is inferred.
-/
theorem prepareValueOnePieces_increment
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (primitives : Primitives oldBank coordinatePolynomial)
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (factory : outcome = prepareValueOnePieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (oldBank := oldBank) (targetIndex := targetIndex) (gap := gap) oldBankEq primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    (accepted : outcome = .ok completed) (position : Fin split.pieces.length) :
    UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
      (keptTargets := completed.1) position =
      (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
          (auxiliaryPiece split position).lastPoint -
        (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
          (auxiliaryPiece split position).firstPoint := by
  have selected := PiecePreparation.accepted_targets_eq (points := points) (firstInside := firstInside)
    (acquired := acquired)
      (domain := domain) (split := split) (channel := 1) (oldBank := oldBank)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := targetIndex) (gap := gap)
      (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    outcome completed accepted
  have original := prepareValueOnePieces_targets (points := points) (prefixes := prefixes)
    (ordered := ordered) (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
    (targetIndex := targetIndex) (gap := gap) oldBankEq primitives outcome factory
  exact UniformPieces.increment_eq (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := (fun position =>
        (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient))
    completed.1
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    (selected.trans original) position

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
