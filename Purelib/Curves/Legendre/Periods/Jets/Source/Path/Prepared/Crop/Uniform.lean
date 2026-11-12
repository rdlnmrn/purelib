module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Entries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.Gauge
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Polynomial
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Data.Except
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Models
import Purelib.Polynomial.Dense.Power
import Purelib.Tactic.Ring

/-! # Actual source queries on one original auxiliary-rectangle piece

One literal SegmentSplit occurrence selects the fixed old target model.
Its independent source model, six-channel query and actual continued Point
retain their original preparation and stage. New restrictions and target
pullback tables are retained outside the query callback. The lower Point
Entry and same-View paths derive every interior sheet, rather than taking
same-sheet or final numerical evidence as an input.
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
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Polynomial.Ascending.Gaussian

universe u

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
    (position : Fin split.pieces.length)

/-- Read one literal retained split occurrence without identifying repeated geometric points. -/
abbrev auxiliaryPiece {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    {first last : Canonical} (split : SegmentSplit cuts first last) (position : Fin split.pieces.length) :=
  split.pieces[position.val]'position.isLt

/-- Retain the original parent sheet permutation on the exact cached endpoints of one auxiliary piece. -/
def auxiliaryLift {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differential genus} (parent : CenteredEdge curve differential)
    {columns rows : Nat} {geometry : Geometry columns rows} {first last : Canonical}
    (piece : SegmentPiece geometry first last) : LiftedCell
      (⟨piece.firstPoint, parent.edge.sheet⟩ : LiftedPoint 2)
      (⟨piece.lastPoint, parent.edge.sheet⟩ : LiftedPoint 2) where
  sheetTransport := (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment).sheetTransport
  finishSheet_eq := (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment).finishSheet_eq

/-- The actual outer restricted source model follows the original displayed affine crop. -/
theorem outer_point (channel : Fin 6) (input : Rational) :
    (cropped.models.cell channel).point input =
      PreparedSegmentCuts.point (parent.edge.point lower) (parent.edge.point upper) input := by
  calc
    _ = Purelib.Geometry.Rational.Affine.line (parent.edge.point lower)
        (parent.edge.point upper - parent.edge.point lower) input := by
      unfold CellModel.point CellModel.displacement Purelib.Geometry.Rational.Affine.line
      rewrite [cropped.models.cell_start channel, cropped.models.cell_finish channel]
      rfl
    _ = _ := (PreparedSegmentCuts.point_eq_line _ _ input).symm

include cropped in
/-- The actual retained lower piece point is the original prepared parent's mapped lower endpoint. -/
theorem piece_first_eq (position : Fin split.pieces.length) :
    (auxiliaryPiece split position).firstPoint =
      parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower) :=
  (auxiliaryPiece split position).first_eq.trans
    ((outer_point (cropped := cropped) 0 (auxiliaryPiece split position).interval.lower).symm.trans
      (cropped.models.cell_point 0 (auxiliaryPiece split position).interval.lower))

include cropped in
/-- The independent actual upper piece point keeps its original mapped upper endpoint and orientation. -/
theorem piece_last_eq (position : Fin split.pieces.length) :
    (auxiliaryPiece split position).lastPoint =
      parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper) :=
  (auxiliaryPiece split position).last_eq.trans
    ((outer_point (cropped := cropped) 0 (auxiliaryPiece split position).interval.upper).symm.trans
      (cropped.models.cell_point 0 (auxiliaryPiece split position).interval.upper))

/-- The exact original RootedQuery at one twice-mapped literal piece fraction.

This named type retains the original prepared parent, split occurrence,
unit-interval witness and both actual query owners. It performs no query
or coordinate construction.
-/
@[expose] def PieceQuery {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) : Type _ :=
  RootedQuery (frame := frame) prepared
      (Cell.Restriction.parameter lower upper
        (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input))
      (Cell.Restriction.parameter_inside lowerInside upperInside
        (Cell.Restriction.parameter_inside
          ⟨(auxiliaryPiece split position).within.1,
            (auxiliaryPiece split position).interval.ordered.le.trans (auxiliaryPiece split position).within.2⟩
          ⟨(auxiliaryPiece split position).within.1.trans (auxiliaryPiece split position).interval.ordered.le,
            (auxiliaryPiece split position).within.2⟩ inside))

/-- Read one original outer query restricted to the same cached auxiliary polynomial, without querying again. -/
def pieceObservation {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      split position input inside) :
    UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (auxiliaryLift parent (auxiliaryPiece split position))
      (Cell.Restriction.model (cropped.models.cell channel) restricted) input :=
  ((queried.observed.channel channel).restrict (lifted := liftedCell parent)
    (croppedCell (frame := frame) (parent := parent) lower upper) (cropped.models.channelCache channel) rfl).restrict
      (lifted := croppedCell (frame := frame) (parent := parent) lower upper)
      (auxiliaryLift parent (auxiliaryPiece split position)) restricted rfl

/-- The actual restricted source observation keeps the same original queried channel root name. -/
theorem pieceObservation_root_name {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside) split position input inside) :
    (pieceObservation (cropped := cropped) split position channel restricted input inside
      queried).algebraic.sheetValue.value.name =
      (queried.observed.channel channel).algebraic.sheetValue.value.name := by
  unfold pieceObservation
  rewrite [UniformObservation.restrict_root_name, UniformObservation.restrict_root_name]
  rfl

/-- Both actual polynomial restrictions preserve the original queried channel's physical point.

The returned observation is the same supplied channel restricted first
to the retained crop and then to its original piece. Neither restriction
replaces its algebraic point or constructs another root observation.
-/
theorem pieceObservation_point {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside) split position input inside) :
    (pieceObservation (cropped := cropped) split position channel restricted input inside queried).algebraic.point =
      (queried.observed.channel channel).algebraic.point := by
  unfold pieceObservation
  rewrite [UniformObservation.restrict_point, UniformObservation.restrict_point]
  rfl

/-- The cached auxiliary restriction begins at the exact original piece endpoint. -/
theorem piece_start {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper)) :
    (Cell.Restriction.model (cropped.models.cell channel) restricted).start =
      (auxiliaryPiece split position).firstPoint :=
  (outer_point channel (auxiliaryPiece split position).interval.lower).trans
    (auxiliaryPiece split position).first_eq.symm

/-- The cached auxiliary restriction finishes at the same retained original piece endpoint. -/
theorem piece_finish {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper)) :
    (Cell.Restriction.model (cropped.models.cell channel) restricted).finish =
      (auxiliaryPiece split position).lastPoint :=
  (outer_point channel (auxiliaryPiece split position).interval.upper).trans
    (auxiliaryPiece split position).last_eq.symm

/-- The actual target coordinate is the unchanged original source coordinate at the twice-mapped fraction. -/
theorem piece_point {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (coordinate : Cell.Spatial.Coordinate (auxiliaryPiece split position).firstPoint
      (auxiliaryPiece split position).lastPoint) (input : Rational) :
    coordinate.point input = prepared.preparation.cell.models.coordinate.point
      (Cell.Restriction.parameter lower upper
        (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input)) := by
  have geometry : coordinate.point input =
      (Cell.Restriction.model (cropped.models.cell channel) restricted).point input := by
    rewrite [coordinate.point_eq]
    unfold CellModel.point CellModel.displacement
    rewrite [piece_start (cropped := cropped) split position channel restricted,
      piece_finish (cropped := cropped) split position channel restricted]
    rfl
  exact geometry.trans ((Cell.Restriction.point_eq (cropped.models.cell channel) restricted input).trans
    ((Cell.Restriction.point_eq (prepared.preparation.cell.models.cell channel)
      (cropped.models.channelCache channel) _).trans
        (prepared.preparation.cell.models.cell_point channel _)))

/-- Transport the SAME Point Entry across its exact coordinate index, preserving its whole Owner. -/
def castPointEntry {siteCount : Nat} {site : ContinuedNeighborhood (Paths.polynomial parameter) siteCount}
    {first last : Canonical} (same : first = last) (sample : ContinuedNeighborhood.Point site last)
    (entry : Entry oldModels last sample.owner) :
    Entry oldModels first (ContinuedNeighborhood.Point.castPoint same sample).owner := by
  cases same
  exact entry

/-- Exact Point-index transport retains the original actual Entry sheet. -/
theorem castPointEntry_sheet
    {siteCount : Nat} {site : ContinuedNeighborhood (Paths.polynomial parameter) siteCount}
    {first last : Canonical} (same : first = last) (sample : ContinuedNeighborhood.Point site last)
    (entry : Entry oldModels last sample.owner) :
    (castPointEntry same sample entry).sheet = entry.sheet := by
  cases same
  rfl

/-- The exact one-query continuation retaining the actual path, both observations and their original readbacks.

The target is the supplied actual model. The source factory, finite reading
identity and signed root-name identity retain both original observations;
this type adds no geometric or numerical comparison premise.
-/
@[expose] def PieceQueryConsumer {columns rows : Nat}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}
    (split : SegmentSplit cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (targetModel : CellModel) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      split position input inside) (Result : Type u) : Type _ :=
  (path : {value : OwnerPath (Paths.polynomial parameter) (parent.edge.point lower)
      cropped.endpoints.1.direct.owner
      (parent.edge.point (Cell.Restriction.parameter lower upper
        (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input))) queried.direct.owner //
    value.vertices = [parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input))]}) →
      (original : UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (auxiliaryLift parent (auxiliaryPiece split position))
        (Cell.Restriction.model (cropped.models.cell channel) restricted) input) →
      original = pieceObservation (cropped := cropped) split position channel restricted input inside queried →
      (target : UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (auxiliaryLift parent (auxiliaryPiece split position)) targetModel input) →
      target.observation.integrandReading = original.observation.integrandReading →
      target.algebraic.sheetValue.value.name = original.algebraic.sheetValue.value.name → Result

/-- The exact charged pullback type on the original source, target model and retained physical piece.

This carrier names the original complete allowance expression; no scalar,
polynomial, bound or pullback cache is recomputed or replaced.
-/
@[expose] def PiecePullback (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (coordinate : Cell.Spatial.Coordinate (auxiliaryPiece split position).firstPoint
      (auxiliaryPiece split position).lastPoint)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (numerator targetSource : Polynomial) (exponent : Nat)
    (bounds : PrimitiveOverlapBounds
      (face.clearance.restrict
        (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
      numerator) : Type _ :=
  Cell.Spatial.Pullback coordinate targetSource
      (UniformObservation.polynomialCharge
        (Cell.Restriction.model (cropped.models.cell channel) restricted).localAllowance
        (bounds.powerScale exponent *
          ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.bound +
            prepared.preparation.cell.request.model.bound)))

/-- The complete original applied one-piece query operation type, with every cache and premise unchanged.

Named type families keep the charged pullback and dependent continuation
at their exact original owners. The function retains all original binder
names and modes; its consuming worker introduces these same arguments.
-/
@[expose] def PieceQueryOperation : Type _ :=
  ∀ (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (coordinate : Cell.Spatial.Coordinate (auxiliaryPiece split position).firstPoint
      (auxiliaryPiece split position).lastPoint)
    (targetIndex sourceDepth : Nat)
    (_sourceDepthEq : prepared.preparation.cell.request.selection.stage = 2 + sourceDepth)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (_oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat)
    (_parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (_sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (_targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent)
    (bounds : PrimitiveOverlapBounds
      (face.clearance.restrict
        (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
      numerator)
    (targetPullback : PiecePullback (cropped := cropped) (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) (position := position)
      channel restricted coordinate oldBank numerator targetSource exponent bounds)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      split position input inside)
    {Result : Type u}
    (_consume : PieceQueryConsumer (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
      (patch := patch) (count := count) (floor := floor) (covered := covered)
      (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
      (targets := targets) (row := row) (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside) (operation := operation) (cropped := cropped)
      (columns := domain.steps) (rows := domain.steps) (geometry := domain.geometry) (cuts := domain.cuts)
      (split := split) (position := position) (channel := channel) (restricted := restricted)
      (targetModel := targetPullback.model) (input := input) (inside := inside) (queried := queried)
      (Result := Result)), Result

/-- Cache the SAME actual old-bank and source-model evaluations with their independently derived unflipped sign.

The actual continued Point and Entry certify the original geometric sheet.
The orientedOverlap construction occurs ONLY inside the erased nearest-sign
proof. Runtime data evaluates the supplied actual bank/model directly;
no oriented bank refinement or canonical overlap value is transported into
this result.
-/
private def pieceOverlap {columns rows : Nat} {geometry : Geometry columns rows}
    {siteCount : Nat} {site : ContinuedNeighborhood (Paths.polynomial parameter) siteCount}
    {point : Canonical} (targetIndex sourceDepth : Nat)
    (source : Model (Paths.polynomial parameter) site.base.box)
    (actual : ContinuedNeighborhood.Point site point) (insideFace : face.cell.box.Contains point)
    (entered : Entry oldModels point actual.owner)
    (rectangles : RectangularPatch oldModels.bounds (oldModels.frame.owners entered.sheet) geometry)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (oldBank : Bank (Paths.polynomial parameter) geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (rectangles.sheets.refine targetIndex).transitions (rectangles.sheets.refine targetIndex).gauge)
    (insideCell : (geometry.box column row).Contains point) (insideActual : site.box.Contains point)
    (sourceEq : source.value.eval point = (site.base.refine (2 + sourceDepth)).value.eval point) :
    {sample : OverlapSample (oldBank.ready column row).model source point // sample.alignment.flip = false} :=
  let left := (oldBank.ready column row).model
  let sample : OverlapSample left source point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq (left.value.eval point - source.value.eval point) ≤
        Canonical.normSq (left.value.eval point + source.value.eval point)
      let derived := Face.PrimitiveComparison.FaceModels.orientedOverlap
        (genus := 1) (curve := Fibre.frameCurve frame) (branches := branches) (higher := higher)
        (bank := bank) (frames := rootFrames) (face := face) (models := oldModels)
        (columns := columns) (rows := rows) (geometry := geometry) (point := point)
        actual insideFace entered rectangles
        column row basis insideCell insideActual targetIndex sourceDepth source sourceEq
      have near := derived.val.alignment.nearest
      rewrite [derived.val.alignment.value_eq, derived.property] at near
      change Canonical.normSq (derived.val.leftValue - derived.val.rightValue) ≤
        Canonical.normSq (derived.val.leftValue + derived.val.rightValue) at near
      rewrite [derived.val.leftValue_eq, derived.val.rightValue_eq] at near
      have retained := congrArg (fun bank : Bank (Paths.polynomial parameter) geometry =>
        (bank.ready column row).model.value.eval point) oldBankEq
      exact Eq.mpr (congrArg (fun value : Canonical =>
        Canonical.normSq (value - source.value.eval point) ≤
          Canonical.normSq (value + source.value.eval point)) retained) near⟩⟩
  ⟨sample, rfl⟩

/-- Change one actual restricted source query on its literal auxiliary piece.

The given old bank and coefficient retain their complete factory readbacks.
The source stage remains the actual original selected index; sourceDepthEq
spells that same index after its genuine two-step payment. The original
lower Entry and SAME actual prefix derive the interior sheet. All newly
returned observations use that one supplied RootedQuery, with no second
query execution or root acquisition.
-/
def withPieceQuery :
    PieceQueryOperation.{u} (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
      (patch := patch) (count := count) (floor := floor) (covered := covered)
      (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
      (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
      (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
      (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest)
      (requested := requested) (observed := observed) (points := points) (branches := branches) (higher := higher)
      (bank := bank) (rootFrames := rootFrames) (face := face) (oldModels := oldModels)
      (firstInside := firstInside) (acquired := acquired) (domain := domain)
      (split := split) (position := position) := by
  intro channel restricted coordinate targetIndex sourceDepth sourceDepthEq oldBank oldBankEq
    numerator originalSource targetSource exponent parentEvaluation sourceCompiled targetCompiled bounds targetPullback
    input inside queried Result consume
  let piece := auxiliaryPiece split position
  let child := Cell.Restriction.parameter piece.interval.lower piece.interval.upper input
  have childInside := Cell.Restriction.parameter_inside
    (⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩ : 0 ≤ piece.interval.lower ∧
      piece.interval.lower ≤ 1)
    (⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩ : 0 ≤ piece.interval.upper ∧
      piece.interval.upper ≤ 1) inside
  let fraction := Cell.Restriction.parameter lower upper child
  have fractionInside := Cell.Restriction.parameter_inside lowerInside upperInside childInside
  have later : lower ≤ fraction := Cell.Restriction.parameter_ge_left ordered childInside.1
  have sourcePoint := piece_point (cropped := cropped) split position channel restricted coordinate input
  have physicalPoint : coordinate.point input = parent.edge.point fraction :=
    sourcePoint.trans (prepared.queryPoint_eq fraction)
  have cellInside := coordinate.point_inside piece.first_inside piece.last_inside inside.1 inside.2
  have faceInside := (domain.patch.cell_refines piece.column piece.row).contains cellInside
  have queryInside : face.cell.box.Contains (parent.edge.point fraction) :=
    Eq.mp (congrArg face.cell.box.Contains physicalPoint) faceInside
  exact points.withQueryEntry prefixes firstInside acquired queried later queryInside
    (fun path pathFactory entered enteredSheet => by
      have pathVertices : path.vertices = [parent.edge.point fraction] :=
        (congrArg (fun value => value.vertices) pathFactory).trans
          (prefixes.property fraction fractionInside later cropped.endpoints.1.direct queried.direct)
      let actual := ContinuedNeighborhood.Point.castPoint physicalPoint queried.sample
      let entry := castPointEntry physicalPoint queried.sample entered
      have entrySheet : entry.sheet = acquired.entry.sheet :=
        (castPointEntry_sheet physicalPoint queried.sample entered).trans enteredSheet
      let spelled := entry.withSheet acquired.entry.sheet entrySheet
      have actualInside : prepared.preparation.cell.patch.box.Contains (coordinate.point input) :=
        Eq.mpr (congrArg prepared.preparation.cell.patch.box.Contains physicalPoint)
          (RootedQuery.sample_inside (prepared := prepared) (fraction := fraction) (inside := fractionInside))
      have sourceReadback : prepared.preparation.cell.request.model.value.eval (coordinate.point input) =
          (prepared.preparation.cell.patch.base.refine (2 + sourceDepth)).value.eval (coordinate.point input) :=
        (congrArg (fun model : Model (Paths.polynomial parameter) prepared.preparation.cell.patch.base.box =>
          model.value.eval (coordinate.point input)) prepared.preparation.cell.request.model_eq).trans
          (congrArg (fun depth => (prepared.preparation.cell.patch.base.refine depth).value.eval
            (coordinate.point input)) sourceDepthEq)
      let left := (oldBank.ready piece.column piece.row).model
      let right := prepared.preparation.cell.request.model
      let sample := pieceOverlap (parameter := parameter) (frame := frame) (basis := basis)
        (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
        (face := face) (oldModels := oldModels) (columns := domain.steps) (rows := domain.steps)
        (geometry := domain.geometry) (site := prepared.preparation.cell.patch)
        (point := coordinate.point input) targetIndex sourceDepth right actual faceInside spelled domain.patch
        piece.column piece.row oldBank oldBankEq cellInside actualInside sourceReadback
      let original := pieceObservation (cropped := cropped) split position channel restricted input inside queried
      have originalEvaluation :
          Evaluation.eval (Cell.Restriction.model (cropped.models.cell channel) restricted).polynomial ⟨input, 0⟩ =
            originalSource.eval (coordinate.point input) :=
        (Cell.Restriction.eval_eq (cropped.models.cell channel) restricted input).trans
          ((Cell.Restriction.eval_eq (prepared.preparation.cell.models.cell channel)
            (cropped.models.channelCache channel) child).trans
            ((parentEvaluation fraction).trans (congrArg originalSource.eval sourcePoint.symm)))
      let value : {value : Canonical // value = targetSource.eval (coordinate.point input)} :=
        ⟨targetSource.eval (coordinate.point input), rfl⟩
      let target := UniformObservation.changeFromOverlap (genus := 1) (curve := Fibre.frameCurve frame)
        (differential := Specification.Table.forms parameter channel)
        (start := (⟨piece.firstPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (finish := (⟨piece.lastPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (lifted := auxiliaryLift parent piece)
        (source := Cell.Restriction.model (cropped.models.cell channel) restricted) (parameter := input)
        (coordinate := coordinate) (leftBox := domain.geometry.box piece.column piece.row)
        (rightBox := prepared.preparation.cell.patch.base.box) (numerator := numerator)
        (targetSource := targetSource) (originalSource := originalSource)
        (clearance := face.clearance.restrict (domain.patch.cell_refines piece.column piece.row))
        (left := left) (right := right)
        bounds exponent original
        (piece_start (cropped := cropped) split position channel restricted)
        (piece_finish (cropped := cropped) split position channel restricted) originalEvaluation
        targetPullback sample.val cellInside
        (prepared.preparation.cell.patch.box_refines.contains actualInside) sample.property
        (targetCompiled (coordinate.point input)) (sourceCompiled (coordinate.point input)) value
      exact consume ⟨path, pathVertices⟩ original rfl target
        (UniformObservation.changeFromOverlap_reading (genus := 1) (curve := Fibre.frameCurve frame)
        (differential := Specification.Table.forms parameter channel)
        (start := (⟨piece.firstPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (finish := (⟨piece.lastPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (lifted := auxiliaryLift parent piece)
        (source := Cell.Restriction.model (cropped.models.cell channel) restricted) (parameter := input)
        (coordinate := coordinate) (leftBox := domain.geometry.box piece.column piece.row)
        (rightBox := prepared.preparation.cell.patch.base.box) (numerator := numerator)
        (targetSource := targetSource) (originalSource := originalSource)
        (clearance := face.clearance.restrict (domain.patch.cell_refines piece.column piece.row))
        (left := left) (right := right)
          bounds exponent original
          (piece_start (cropped := cropped) split position channel restricted)
          (piece_finish (cropped := cropped) split position channel restricted)
          originalEvaluation targetPullback sample.val cellInside
          (prepared.preparation.cell.patch.box_refines.contains actualInside) sample.property
          (targetCompiled (coordinate.point input)) (sourceCompiled (coordinate.point input)) value)
        (UniformObservation.changeFromOverlap_root_name (genus := 1) (curve := Fibre.frameCurve frame)
        (differential := Specification.Table.forms parameter channel)
        (start := (⟨piece.firstPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (finish := (⟨piece.lastPoint, parent.edge.sheet⟩ : LiftedPoint 2))
        (lifted := auxiliaryLift parent piece)
        (source := Cell.Restriction.model (cropped.models.cell channel) restricted) (parameter := input)
        (coordinate := coordinate) (leftBox := domain.geometry.box piece.column piece.row)
        (rightBox := prepared.preparation.cell.patch.base.box) (numerator := numerator)
        (targetSource := targetSource) (originalSource := originalSource)
        (clearance := face.clearance.restrict (domain.patch.cell_refines piece.column piece.row))
        (left := left) (right := right)
          bounds exponent original
          (piece_start (cropped := cropped) split position channel restricted)
          (piece_finish (cropped := cropped) split position channel restricted)
          originalEvaluation targetPullback sample.val cellInside
          (prepared.preparation.cell.patch.box_refines.contains actualInside) sample.property
          (targetCompiled (coordinate.point input)) (sourceCompiled (coordinate.point input)) value))

/-- One original query and certified one-endpoint prefix together with its SAME two polynomial observations.

The source observation has its original double-restriction factory. The
target retains that source reading and signed root generator. These are
construction readbacks; no requested final closeness is supplied as data.
-/
abbrev PieceReadings (channel : Fin 6)
    (restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper))
    (target : CellModel) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :=
  Σ queried : PieceQuery (prepared := prepared) (lower := lower) (upper := upper)
      (lowerInside := lowerInside) (upperInside := upperInside)
      split position input inside,
  Σ _path : {value : OwnerPath (Paths.polynomial parameter) (parent.edge.point lower)
      cropped.endpoints.1.direct.owner
      (parent.edge.point (Cell.Restriction.parameter lower upper
        (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input))) queried.direct.owner //
    value.vertices = [parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input))]},
  Σ original : {value : UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (auxiliaryLift parent (auxiliaryPiece split position))
      (Cell.Restriction.model (cropped.models.cell channel) restricted) input //
    value = pieceObservation (cropped := cropped) split position channel restricted input inside queried},
  {value : UniformObservation (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (auxiliaryLift parent (auxiliaryPiece split position)) target input //
    value.observation.integrandReading = original.val.observation.integrandReading ∧
      value.algebraic.sheetValue.value.name = original.val.algebraic.sheetValue.value.name}

/-- The actual future source Selection and the proved finite stopping reason for a source below stage two. -/
abbrev SourceFloor :=
  {future : Selection prepared.preparation.cell.cache.scale
      (max 2 prepared.preparation.cell.request.selection.stage) prepared.preparation.cell.target //
    future = Selection.build prepared.preparation.cell.cache.scale
      prepared.preparation.cell.request.selection.scaleNonnegative
      (max 2 prepared.preparation.cell.request.selection.stage) prepared.preparation.cell.target
      prepared.preparation.cell.request.selection.targetPositive ∧
    ¬ 2 ≤ prepared.preparation.cell.request.selection.stage}

namespace SourceFloor

/-- An actually retained preparation floor at least two contradicts this original insufficient-stage outcome. -/
theorem impossible (failure : SourceFloor (prepared := prepared)) (floorPaid : 2 ≤ floor) : False :=
  failure.property.2 (floorPaid.trans prepared.floor_le_sourceStage)

/-- Extract the SAME bound original outcome using its already-paid construction floor.

The supplied value is an existing outcome, such as one bound preparePiece
execution. Only generic Except extraction runs; no source preparation,
model, piece factory or query is repeated or retagged.
-/
def success {Value : Type u} (outcome : Except (SourceFloor (prepared := prepared)) Value)
    (floorPaid : 2 ≤ floor) : {value : Value // outcome = .ok value} :=
  Except.requireSuccess outcome (fun failure => failure.impossible floorPaid)

/-- The extracted value belongs to that identical original success outcome. -/
theorem success_eq {Value : Type u} (outcome : Except (SourceFloor (prepared := prepared)) Value)
    (floorPaid : 2 ≤ floor) : outcome = .ok (success outcome floorPaid).val :=
  (success outcome floorPaid).property

end SourceFloor

/-- The actual once-built restriction, coordinate, bounds, future requests, pullback and paired query callback.

Every component is original owned data. The pair-producing callback is
productive, not a memoized infinite family: one call keeps its one actual
RootedQuery, prefix path and both observations. Independent future calls
remain independent executions.
-/
abbrev UniformPiece (channel : Fin 6) (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (numerator targetSource : Polynomial) (exponent targetIndex : Nat) (gap : AccuracyRequest) :=
  Σ restricted : Restriction.Cached (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper),
  Σ coordinate : Cell.Spatial.Coordinate (auxiliaryPiece split position).firstPoint
      (auxiliaryPiece split position).lastPoint,
  Σ bounds : PrimitiveOverlapBounds
      (face.clearance.restrict
        (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
      numerator,
  (PrimitiveOverlapBounds.PowerRequest bounds
    (domain.patch.models.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model
    prepared.preparation.cell.patch.base.model exponent targetIndex
    (max 2 prepared.preparation.cell.request.selection.stage) gap.tolerance gap.positive) ×
  Σ target : Cell.Spatial.Pullback coordinate targetSource
      (UniformObservation.polynomialCharge
        (Cell.Restriction.model (cropped.models.cell channel) restricted).localAllowance
        (bounds.powerScale exponent *
          ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.bound +
            prepared.preparation.cell.request.model.bound))),
    (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
      PieceReadings (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position) channel restricted target.model input inside

/-- Execute the original piece branch with its one bounds operation delayed until after restriction and coordinate. -/
private def preparePieceWith (channel : Fin 6) (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat) (gap : AccuracyRequest)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent)
    (makeBounds : Unit → PrimitiveOverlapBounds
      (face.clearance.restrict
        (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
      numerator) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap) :=
  if enough : 2 ≤ prepared.preparation.cell.request.selection.stage then
    let restricted := Restriction.Cached.canonical (cropped.models.cell channel).polynomial
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
      (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper)
    let coordinate := Cell.Spatial.Coordinate.build
      (auxiliaryPiece split position).firstPoint (auxiliaryPiece split position).lastPoint
    let bounds := makeBounds ()
    let requests := bounds.requestPowerGap
      (domain.patch.models.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model
      prepared.preparation.cell.patch.base.model exponent targetIndex
      (max 2 prepared.preparation.cell.request.selection.stage) gap.tolerance gap.positive
    let left := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model
    let right := prepared.preparation.cell.request.model
    have sumNonnegative : 0 ≤ left.bound + right.bound :=
      (Data.Rat.Fraction.Field.zero_add (0 : Rational)).symm.trans_le
        (Arithmetic.add_le_add_direct left.bound_nonnegative right.bound_nonnegative)
    have gapNonnegative := Arithmetic.mul_nonneg_direct (bounds.powerScale_nonnegative exponent) sumNonnegative
    let target := Cell.Spatial.Pullback.build coordinate targetSource
      (UniformObservation.polynomialCharge
        (Cell.Restriction.model (cropped.models.cell channel) restricted).localAllowance
        (bounds.powerScale exponent * (left.bound + right.bound)))
      (UniformObservation.polynomialCharge_nonnegative
        (Cell.Restriction.model (cropped.models.cell channel) restricted).localAllowance_nonneg gapNonnegative)
    let queries : (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
        PieceReadings (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (position := position) channel restricted target.model input inside :=
      fun input inside =>
        let child := Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input
        have childInside := Cell.Restriction.parameter_inside
          ⟨(auxiliaryPiece split position).within.1,
            (auxiliaryPiece split position).interval.ordered.le.trans (auxiliaryPiece split position).within.2⟩
          ⟨(auxiliaryPiece split position).within.1.trans (auxiliaryPiece split position).interval.ordered.le,
            (auxiliaryPiece split position).within.2⟩ inside
        let queried := cropped.queryAt child childInside
        withPieceQuery (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
          (acquired := acquired) (domain := domain) (split := split) (position := position)
          channel restricted coordinate
          targetIndex (prepared.preparation.cell.request.selection.stage - 2) (Nat.add_sub_of_le enough).symm
          oldBank oldBankEq numerator originalSource targetSource exponent parentEvaluation sourceCompiled
          targetCompiled
          bounds target input inside queried
          (fun path original factory changed reading roots =>
            ⟨queried, path, ⟨original, factory⟩, ⟨changed, reading, roots⟩⟩)
    .ok ⟨restricted, coordinate, bounds, requests, target, queries⟩
  else
    let future := Selection.build prepared.preparation.cell.cache.scale
      prepared.preparation.cell.request.selection.scaleNonnegative
      (max 2 prepared.preparation.cell.request.selection.stage) prepared.preparation.cell.target
      prepared.preparation.cell.request.selection.targetPositive
    .error ⟨future, rfl, enough⟩

/-- The successful original branch retains the exact value returned by its delayed bounds operation. -/
private theorem preparePieceWith_bound (channel : Fin 6) (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat) (gap : AccuracyRequest)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent)
    (makeBounds : Unit → PrimitiveOverlapBounds
      (face.clearance.restrict
        (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
      numerator)
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap)
    (accepted : preparePieceWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource targetSource exponent gap
    parentEvaluation sourceCompiled targetCompiled makeBounds = .ok data) :
    data.2.2.1 = makeBounds () := by
  unfold preparePieceWith at accepted
  split at accepted
  · exact (congrArg (fun value : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap => value.2.2.1) (Except.ok.inj accepted)).symm
  · cases accepted

/-- Materialize one genuine fixed-target piece, or retain the original source's typed future-floor request.

The literal old split chooses the fixed target cell. The old bank and
coefficient are supplied original caches with their factory readbacks.
Only after the actual source stage passes two are the new restriction,
coordinate, local bounds, independent future selections and target pullback
constructed once. No source model, source query or old table is restaged.
-/
def preparePiece (channel : Fin 6) (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat) (gap : AccuracyRequest)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap) :=
  preparePieceWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource targetSource exponent gap
    parentEvaluation sourceCompiled targetCompiled (fun _ =>
      PrimitiveOverlapBounds.build
        (face.clearance.restrict
          (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
        numerator)

/-- Materialize one original piece using its SAME previously cached rectangular bound.

The whole rectangular cache and its exact original factory equation are
retained inputs, available before source/grid stage selection. The worker
reads the selected entry exactly where the original bounds construction
occurred. Original source-floor failure and every other factory/query
remain the same; no cache is recomputed and then identified by equality.
-/
def preparePieceWithBounds (channel : Fin 6) (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat) (gap : AccuracyRequest)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent)
    (cached : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator}) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap) :=
  preparePieceWith (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource targetSource exponent gap
    parentEvaluation sourceCompiled targetCompiled (fun _ =>
      Rectangular.entry cached.val (auxiliaryPiece split position).column (auxiliaryPiece split position).row)

/-- A given successful retained-bounds outcome contains that SAME selected all-cell cache entry.

The whole actual outcome and its factory identity are inputs. This readback
never executes a source query, rectangular bound or preparation again.
-/
theorem preparePieceWithBounds_bound (channel : Fin 6) (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (numerator originalSource targetSource : Polynomial) (exponent : Nat) (gap : AccuracyRequest)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ exponent)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = numerator.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ exponent)
    (cached : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    (outcome : Except (SourceFloor (prepared := prepared))
        (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (position := position)
          channel oldBank numerator targetSource exponent targetIndex gap))
    (factory : outcome = preparePieceWithBounds (parameter := parameter) (frame := frame) (basis := basis)
      (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource targetSource exponent gap
    parentEvaluation sourceCompiled targetCompiled cached)
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        channel oldBank numerator targetSource exponent targetIndex gap) (accepted : outcome = .ok data) :
    data.2.2.1 =
      Rectangular.entry cached.val (auxiliaryPiece split position).column (auxiliaryPiece split position).row :=
  preparePieceWith_bound (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (patch := patch) (count := count) (floor := floor) (covered := covered)
    (baseStart := baseStart) (baseFinish := baseFinish) (originalPath := originalPath) (stage := stage)
    (targets := targets) (row := row) (accuracy := accuracy) (prepared := prepared)
    (lower := lower) (upper := upper) (lowerInside := lowerInside) (upperInside := upperInside)
    (operation := operation) (cropped := cropped) (comparisonRequest := comparisonRequest) (requested := requested)
    (points := points) (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames)
    (face := face) (oldModels := oldModels) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (position := position)
    channel targetIndex oldBank oldBankEq numerator originalSource targetSource exponent gap
    parentEvaluation sourceCompiled targetCompiled
    (fun _ => Rectangular.entry cached.val (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    data (factory.symm.trans accepted)

namespace UniformPiece

variable {channel : Fin 6} {targetIndex exponent : Nat}
    {oldBank : Bank (Paths.polynomial parameter) domain.geometry} {numerator targetSource : Polynomial}
    {gap : AccuracyRequest}
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel oldBank numerator targetSource exponent targetIndex gap)

/-- Read the SAME once-built restriction of the actual outer source cell. -/
abbrev restricted : Restriction.Cached (cropped.models.cell channel).polynomial
    (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.lower)
    (Cast.Path.ofCoordinate (auxiliaryPiece split position).interval.upper) := data.1

/-- Read the SAME retained coordinate on both literal old-piece endpoints. -/
abbrev coordinate : Cell.Spatial.Coordinate (auxiliaryPiece split position).firstPoint
    (auxiliaryPiece split position).lastPoint := data.2.1

/-- Read the fixed numerator/clearance cache at this actual original target cell. -/
abbrev bounds : PrimitiveOverlapBounds
    (face.clearance.restrict
      (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    numerator := data.2.2.1

/-- Read both independent original future model Selections, without constructing or retagging a model. -/
abbrev requests : PrimitiveOverlapBounds.PowerRequest data.bounds
    (domain.patch.models.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model
    prepared.preparation.cell.patch.base.model exponent targetIndex
    (max 2 prepared.preparation.cell.request.selection.stage) gap.tolerance gap.positive := data.2.2.2.1

/-- Read the SAME actual target pullback on its derived local allowance. -/
abbrev target : Cell.Spatial.Pullback data.coordinate targetSource
    (UniformObservation.polynomialCharge
      (Cell.Restriction.model (cropped.models.cell channel) data.restricted).localAllowance
      (data.bounds.powerScale exponent *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.bound +
          prepared.preparation.cell.request.model.bound))) := data.2.2.2.2.1

/-- Query the original source once and retain that answer, its actual prefix and the two observations. -/
abbrev query : (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
    PieceReadings (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel data.restricted data.target.model input inside := data.2.2.2.2.2

/-- The actual nested source model uses its retained polynomial restriction. -/
abbrev source : CellModel := Cell.Restriction.model (cropped.models.cell channel) data.restricted

/-- The actual nested source displacement is the difference of the SAME literal cached piece endpoints. -/
theorem source_displacement :
    data.source.displacement =
      (auxiliaryPiece split position).lastPoint - (auxiliaryPiece split position).firstPoint :=
  congrArg₂ (fun last first : Canonical => last - first)
    (piece_finish (cropped := cropped) split position channel data.restricted)
    (piece_start (cropped := cropped) split position channel data.restricted)

/-- Both productive certificates read the SAME paired query operation and its retained original source data.

Each certificate query invokes that operation once. Independent calls of
the two certificate functions remain independent; the pair cache returned
by data.query is available to consumers that need one shared execution.
No source preparation, model or polynomial table is reconstructed here.
-/
def certificates :
    UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (auxiliaryLift parent (auxiliaryPiece split position)) data.source ×
      UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (auxiliaryLift parent (auxiliaryPiece split position)) data.target.model :=
  ⟨⟨fun input lower upper => (query (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position) (data := data) input ⟨lower, upper⟩).2.2.1.val⟩,
    ⟨fun input lower upper => (query (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position) (data := data) input ⟨lower, upper⟩).2.2.2.val⟩⟩

/-- The actual retained cell integrals obey the original finite uniform-comparison estimate.

The per-query construction internally supplies the exact same signed root
name. Both source and target model owners, their independent local charges
and the original piece displacement remain in the displayed bound.
-/
theorem integral_difference_le :
    normSq (data.source.integralSample - data.target.model.integralSample) ≤
      16 * (data.source.localAllowance + data.target.model.localAllowance) * normSq data.source.displacement := by
  have sourceAllowance : data.source.localAllowance = prepared.preparation.cell.allowance :=
    (Cell.Restriction.model_allowance (cropped.models.cell channel) data.restricted).trans
      ((Cell.Restriction.model_allowance (prepared.preparation.cell.models.cell channel)
        (cropped.models.channelCache channel)).trans (prepared.preparation.cell.models.cell_allowance channel))
  have sourcePositive : 0 < data.source.localAllowance :=
    Eq.mpr (congrArg (fun value : Rational => 0 < value) sourceAllowance) prepared.preparation.query.positive
  let actual := certificates (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := data)
  exact UniformCellCertificate.integral_difference_le actual.1 actual.2
    ((piece_start (cropped := cropped) split position channel data.restricted).trans data.target.start_eq.symm)
    ((piece_finish (cropped := cropped) split position channel data.restricted).trans data.target.finish_eq.symm)
    (fun input lower upper => by
      let answer := query (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position) (data := data) input ⟨lower, upper⟩
      change NamedEquivalent answer.2.2.1.val.algebraic.sheetValue.value.name
        answer.2.2.2.val.algebraic.sheetValue.value.name
      exact NamedEquivalent.transport rfl answer.2.2.2.property.2.symm
        (NamedEquivalent.refl answer.2.2.1.val.algebraic.sheetValue.value.name))
    (Arithmetic.add_pos_of_pos_of_nonneg_direct sourcePositive data.target.model.localAllowance_nonneg)

/-- The retained source integral is quantitatively close to the SAME old primitive's oriented increment.

Only the exact derivative law of the supplied original primitive is used.
Its additive constant is retained: the two displayed endpoint values come
from that one polynomial, and no normalization or period equality is assumed.
-/
theorem primitive_increment_le
    (primitive : DensePrimitive targetSource
      (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row)) :
    normSq (data.source.integralSample -
      (primitive.value.eval (auxiliaryPiece split position).lastPoint -
        primitive.value.eval (auxiliaryPiece split position).firstPoint)) ≤
      16 * (data.source.localAllowance + data.target.model.localAllowance) * normSq data.source.displacement := by
  have integral := data.target.integralSample_primitive primitive.value primitive.derivative_eq
  exact (congrArg (fun value : Canonical => normSq (data.source.integralSample - value)) integral).symm.trans_le
    (integral_difference_le (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position) (data := data))

end UniformPiece

/-- Prepare the actual dx/y source channel on one retained old rectangle piece.

The original value-zero spatial pullback and source-model readback are
selected internally. The target coefficient remains its independent old
cache with the supplied original coefficient factory law; no final
comparison, sheet equality or accuracy bound is an input.
-/
def prepareValueZeroPiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetSource : Polynomial) (gap : AccuracyRequest)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = constantOnePolynomial.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ 1) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        0 oldBank constantOnePolynomial targetSource 1 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position) 0 targetIndex oldBank oldBankEq
    constantOnePolynomial prepared.preparation.cell.request.models.valueZero targetSource 1 gap
    (fun input => prepared.preparation.cell.models.valueZero.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueZero_readback prepared.preparation.cell.request.models point) targetCompiled

/-- Prepare the actual x dx/y source channel on the SAME kind of original retained piece.

The original value-one pullback, coordinate numerator and selected source
model remain their actual owners. This is the second value coordinate,
without pretending it belongs to the genus-one holomorphic Fin1 list.
-/
def prepareValueOnePiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetSource : Polynomial) (gap : AccuracyRequest)
    (targetCompiled : ∀ point : Canonical, targetSource.eval point = coordinatePolynomial.eval point *
      ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval
        point) ^ 1) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        1 oldBank coordinatePolynomial targetSource 1 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position) 1 targetIndex oldBank oldBankEq
    coordinatePolynomial prepared.preparation.cell.request.models.valueOne targetSource 1 gap
    (fun input => prepared.preparation.cell.models.valueOne.eval_point input)
    (fun point => by
      simpa only [pow_one, -eq_self, -iff_self] using
        IntegrandRequests.valueOne_readback prepared.preparation.cell.request.models point) targetCompiled

/-- Prepare the actual first unweighted derivative on one retained original piece.

The original cached one-half numerator and both independently retained
cube caches derive the source and target compilation readbacks internally.
The supplied target Shared cache keeps its actual old-bank model owner;
no numerator, power, model or source query is rebuilt or reinterpreted.
-/
def prepareFirstZeroPiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : Models.Shared (parameter := parameter)
      (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
    (gap : AccuracyRequest) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        2 oldBank prepared.requests.firstNumeratorZero targetModels.firstZero 3 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position)
    2 targetIndex oldBank oldBankEq prepared.requests.firstNumeratorZero
    prepared.preparation.cell.request.models.firstZero targetModels.firstZero 3 gap
    (fun input => prepared.preparation.cell.models.firstZero.eval_point input)
    (fun point =>
      (IntegrandRequests.firstZero_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorZero.eval point * value)
            (prepared.preparation.cell.request.models.powers.cube_eval point)))
    (fun point =>
      (IntegrandRequests.firstZero_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests targetModels point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorZero.eval point * value)
            (targetModels.powers.cube_eval point)))

/-- Prepare the actual first coordinate-weighted derivative on one retained original piece.

The original cached one-half numerator and both independently retained
cube caches derive the source and target compilation readbacks internally.
The supplied target Shared cache keeps its actual old-bank model owner;
no numerator, power, model or source query is rebuilt or reinterpreted.
-/
def prepareFirstOnePiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : Models.Shared (parameter := parameter)
      (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
    (gap : AccuracyRequest) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        3 oldBank prepared.requests.firstNumeratorOne targetModels.firstOne 3 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position)
    3 targetIndex oldBank oldBankEq prepared.requests.firstNumeratorOne
    prepared.preparation.cell.request.models.firstOne targetModels.firstOne 3 gap
    (fun input => prepared.preparation.cell.models.firstOne.eval_point input)
    (fun point =>
      (IntegrandRequests.firstOne_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorOne.eval point * value)
            (prepared.preparation.cell.request.models.powers.cube_eval point)))
    (fun point =>
      (IntegrandRequests.firstOne_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests targetModels point).trans
          (congrArg (fun value : Canonical => prepared.requests.firstNumeratorOne.eval point * value)
            (targetModels.powers.cube_eval point)))

/-- Prepare the actual second unweighted derivative on one retained original piece.

The original cached three-quarter numerator and both independently retained
fifth caches derive the source and target compilation readbacks internally.
The supplied target Shared cache keeps its actual old-bank model owner;
no numerator, power, model or source query is rebuilt or reinterpreted.
-/
def prepareSecondZeroPiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : Models.Shared (parameter := parameter)
      (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
    (gap : AccuracyRequest) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        4 oldBank prepared.requests.secondNumeratorZero targetModels.secondZero 5 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position)
    4 targetIndex oldBank oldBankEq prepared.requests.secondNumeratorZero
    prepared.preparation.cell.request.models.secondZero targetModels.secondZero 5 gap
    (fun input => prepared.preparation.cell.models.secondZero.eval_point input)
    (fun point =>
      (IntegrandRequests.secondZero_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorZero.eval point * value)
            (prepared.preparation.cell.request.models.powers.fifth_eval point)))
    (fun point =>
      (IntegrandRequests.secondZero_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests targetModels point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorZero.eval point * value)
            (targetModels.powers.fifth_eval point)))

/-- Prepare the actual second coordinate-weighted derivative on one retained original piece.

The original cached three-quarter numerator and both independently retained
fifth caches derive the source and target compilation readbacks internally.
The supplied target Shared cache keeps its actual old-bank model owner;
no numerator, power, model or source query is rebuilt or reinterpreted.
-/
def prepareSecondOnePiece (targetIndex : Nat)
    (oldBank : Bank (Paths.polynomial parameter) domain.geometry)
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge)
    (targetModels : Models.Shared (parameter := parameter)
      (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
    (gap : AccuracyRequest) :
    Except (SourceFloor (prepared := prepared))
      (UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (position := position)
        5 oldBank prepared.requests.secondNumeratorOne targetModels.secondOne 5 targetIndex gap) :=
  preparePiece (points := points) (prefixes := prefixes) (ordered := ordered) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position)
    5 targetIndex oldBank oldBankEq prepared.requests.secondNumeratorOne
    prepared.preparation.cell.request.models.secondOne targetModels.secondOne 5 gap
    (fun input => prepared.preparation.cell.models.secondOne.eval_point input)
    (fun point =>
      (IntegrandRequests.secondOne_readback (parameter := parameter)
        (model := prepared.preparation.cell.request.model)
        prepared.requests prepared.preparation.cell.request.models point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorOne.eval point * value)
            (prepared.preparation.cell.request.models.powers.fifth_eval point)))
    (fun point =>
      (IntegrandRequests.secondOne_readback (parameter := parameter)
        (model := (oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model)
        prepared.requests targetModels point).trans
          (congrArg (fun value : Canonical => prepared.requests.secondNumeratorOne.eval point * value)
            (targetModels.powers.fifth_eval point)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
