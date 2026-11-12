module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces
import Purelib.Curves.Legendre.Periods.Jets.Models
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Vector.Dependent

/-! # Actual whole-crop first and second differential preparations

A supplied finite per-cell Shared bank keeps its exact old inverse-model
owners and both original odd-power caches. Each literal split occurrence
constructs one original finite polynomial primitive for the selected actual
coefficient, then the existing whole-crop preparation retains it with the
same successful or insufficient-stage outcome. No Shared/power/model or
physical source observation is rebuilt.
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
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit SegmentPiece GridCuts)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Dense.Gaussian.Primitive

/-- The complete retained six-channel Shared cache at every original rectangular model-bank cell.

This is an exact nested dependent-vector view of supplied cache values.
It keeps each actual model as the index, without introducing another
model bank or constructing a Shared or OddPowers record.
-/
abbrev TargetModels {parameter : Canonical} {columns rows : Nat} {geometry : Geometry columns rows}
    (modelBank : Bank (Paths.polynomial parameter) geometry) :=
  DependentVector (fun column : Fin (columns + 1) =>
    DependentVector (fun row : Fin (rows + 1) =>
      Models.Shared (parameter := parameter) (modelBank.ready column row).model))

namespace TargetModels

/-- Read the SAME original per-cell Shared cache at its actual column and row indices. -/
abbrev cell {parameter : Canonical} {columns rows : Nat} {geometry : Geometry columns rows}
    {modelBank : Bank (Paths.polynomial parameter) geometry}
    (keptModels : TargetModels (parameter := parameter) modelBank)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    Models.Shared (parameter := parameter) (modelBank.ready column row).model :=
  (keptModels.get column).get row

end TargetModels

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

variable {targetIndex : Nat} {oldBank : Bank (Paths.polynomial parameter) domain.geometry}
    {gap : AccuracyRequest}

/-- Prepare all actual unweighted first derivative pieces against the SAME retained per-cell target models.

The original scaled numerator and source/target cube readbacks derive
both compilation laws. The original DensePrimitive.ofPolynomial computes
one finite primitive per literal occurrence during target materialization;
its full record and actual coefficient remain in the old outcome cache.
-/
def prepareFirstZeroPieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : TargetModels (parameter := parameter) oldBank) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 2) (oldBank := oldBank)
      (numerator := prepared.requests.firstNumeratorZero) (exponent := 3)
      (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstZero) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 2) (oldBank := oldBank)
    (numerator := prepared.requests.firstNumeratorZero) (exponent := 3) (targetIndex := targetIndex) (gap := gap)
    (targetSources := fun position =>
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstZero)
    (oldBankEq := oldBankEq) (originalSource := prepared.preparation.cell.request.models.firstZero)
    (parentEvaluation := fun input => prepared.preparation.cell.models.firstZero.eval_point input)
    (sourceCompiled := fun point =>
      (IntegrandRequests.firstZero_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorZero.eval point * value)
            (prepared.preparation.cell.request.models.powers.cube_eval point)))
    (targetCompiled := fun position point =>
      (IntegrandRequests.firstZero_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
          (auxiliaryPiece split position).column (auxiliaryPiece split position).row) point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorZero.eval point * value)
            ((TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
              (auxiliaryPiece split position).column (auxiliaryPiece split position).row).powers.cube_eval point)))
    (primitives := fun position => Certificate.DensePrimitive.ofPolynomial
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstZero
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))

/-- Prepare all actual coordinate-weighted first derivative pieces against the SAME retained per-cell target models.

The original scaled numerator and source/target cube readbacks derive
both compilation laws. The original DensePrimitive.ofPolynomial computes
one finite primitive per literal occurrence during target materialization;
its full record and actual coefficient remain in the old outcome cache.
-/
def prepareFirstOnePieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : TargetModels (parameter := parameter) oldBank) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 3) (oldBank := oldBank)
      (numerator := prepared.requests.firstNumeratorOne) (exponent := 3)
      (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstOne) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 3) (oldBank := oldBank)
    (numerator := prepared.requests.firstNumeratorOne) (exponent := 3) (targetIndex := targetIndex) (gap := gap)
    (targetSources := fun position =>
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstOne)
    (oldBankEq := oldBankEq) (originalSource := prepared.preparation.cell.request.models.firstOne)
    (parentEvaluation := fun input => prepared.preparation.cell.models.firstOne.eval_point input)
    (sourceCompiled := fun point =>
      (IntegrandRequests.firstOne_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorOne.eval point * value)
            (prepared.preparation.cell.request.models.powers.cube_eval point)))
    (targetCompiled := fun position point =>
      (IntegrandRequests.firstOne_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
          (auxiliaryPiece split position).column (auxiliaryPiece split position).row) point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorOne.eval point * value)
            ((TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
              (auxiliaryPiece split position).column (auxiliaryPiece split position).row).powers.cube_eval point)))
    (primitives := fun position => Certificate.DensePrimitive.ofPolynomial
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).firstOne
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))

/-- Prepare all actual unweighted second derivative pieces against the SAME retained per-cell target models.

The original scaled numerator and source/target fifth readbacks derive
both compilation laws. The original DensePrimitive.ofPolynomial computes
one finite primitive per literal occurrence during target materialization;
its full record and actual coefficient remain in the old outcome cache.
-/
def prepareSecondZeroPieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : TargetModels (parameter := parameter) oldBank) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 4) (oldBank := oldBank)
      (numerator := prepared.requests.secondNumeratorZero) (exponent := 5)
      (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondZero) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 4) (oldBank := oldBank)
    (numerator := prepared.requests.secondNumeratorZero) (exponent := 5) (targetIndex := targetIndex) (gap := gap)
    (targetSources := fun position =>
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondZero)
    (oldBankEq := oldBankEq) (originalSource := prepared.preparation.cell.request.models.secondZero)
    (parentEvaluation := fun input => prepared.preparation.cell.models.secondZero.eval_point input)
    (sourceCompiled := fun point =>
      (IntegrandRequests.secondZero_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorZero.eval point * value)
            (prepared.preparation.cell.request.models.powers.fifth_eval point)))
    (targetCompiled := fun position point =>
      (IntegrandRequests.secondZero_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
          (auxiliaryPiece split position).column (auxiliaryPiece split position).row) point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorZero.eval point * value)
            ((TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
              (auxiliaryPiece split position).column (auxiliaryPiece split position).row).powers.fifth_eval point)))
    (primitives := fun position => Certificate.DensePrimitive.ofPolynomial
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondZero
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))

/-- Prepare all actual coordinate-weighted second derivative pieces against the SAME retained per-cell target models.

The original scaled numerator and source/target fifth readbacks derive
both compilation laws. The original DensePrimitive.ofPolynomial computes
one finite primitive per literal occurrence during target materialization;
its full record and actual coefficient remain in the old outcome cache.
-/
def prepareSecondOnePieces
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : TargetModels (parameter := parameter) oldBank) :
    PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 5) (oldBank := oldBank)
      (numerator := prepared.requests.secondNumeratorOne) (exponent := 5)
      (targetIndex := targetIndex) (gap := gap)
      (fun position =>
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondOne) :=
  preparePieces (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (channel := 5) (oldBank := oldBank)
    (numerator := prepared.requests.secondNumeratorOne) (exponent := 5) (targetIndex := targetIndex) (gap := gap)
    (targetSources := fun position =>
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondOne)
    (oldBankEq := oldBankEq) (originalSource := prepared.preparation.cell.request.models.secondOne)
    (parentEvaluation := fun input => prepared.preparation.cell.models.secondOne.eval_point input)
    (sourceCompiled := fun point =>
      (IntegrandRequests.secondOne_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorOne.eval point * value)
            (prepared.preparation.cell.request.models.powers.fifth_eval point)))
    (targetCompiled := fun position point =>
      (IntegrandRequests.secondOne_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests
        (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
          (auxiliaryPiece split position).column (auxiliaryPiece split position).row) point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorOne.eval point * value)
            ((TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
              (auxiliaryPiece split position).column (auxiliaryPiece split position).row).powers.fifth_eval point)))
    (primitives := fun position => Certificate.DensePrimitive.ofPolynomial
      (TargetModels.cell (parameter := parameter) (modelBank := oldBank) targetModels
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row).secondOne
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
