module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Children
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces
public import Purelib.Riemann.Readings.RectangularPointReadings.Chord
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Total source-piece comparisons on the original numerical chord bank

The original split piece supplies both literal points and their actual
containing cell. Its retained source/target models recover the same old
primitive increment. The numerical comparison keeps original geometry,
primitives, anchors and offsets throughout. Physical child queries, Entries
and the transported-domain Lifted are constructed independently; their
exact coordinate incidence links the same literal triangle slots.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Face.Entries.FaceModels.Entry (PointData)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Polynomial.Dense.Gaussian.Basic (constantOnePolynomial coordinatePolynomial)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

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
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    (shared : Face.DomainBanks.FaceDomains rootFrames face)
    (prefixes : PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside)
    (ordered : lower ≤ upper) (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition shared.models firstInside points.samples.1.val.owner)
    (domain : PeriodDomain shared.models acquired.entry.sheet)

universe u

variable {points shared prefixes ordered firstInside acquired domain}

namespace UniformPieces.Chord

variable {numerator : Polynomial} {bounds : PrimitiveOverlapBounds face.clearance numerator}
    {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge) numerator)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    {gap : AccuracyRequest} {channel : Fin 6}

/-- Read only the original coefficient at the same literal source-piece occurrence. -/
@[expose] def pieceCoefficients (position : Fin split.pieces.length) : Polynomial :=
  (primitives.cells (auxiliaryPiece split position).column (auxiliaryPiece split position).row).coefficient

include cropped in
/-- The literal numerical triangle is the actual child's mapped endpoint triangle, with both roles retained. -/
theorem coordinate_eq (position : Fin split.pieces.length) :
    ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint =
      ClearBoxPaths.Chord.coordinate
        (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower))
        (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper)) :=
  congrArg₂ ClearBoxPaths.Chord.coordinate
    (piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) position)
    (piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) position)

/-- The actual same-cell numerical cache and both payments for one literal original source piece.

No numerical owner is indexed by the transported child domain. Both the
original target triangle bank and the newly constructed same-cell reader
keep their original primitive/anchor/offset owners and literal point slots.
-/
@[expose] def Comparison
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint)) :=
  {fixed : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint) //
    fixed = PointReadings.inCell anchors offsets
      (auxiliaryPiece split position).column (auxiliaryPiece split position).row
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint)
      (ClearBoxPaths.Chord.coordinate_inside
        (auxiliaryPiece split position).first_inside (auxiliaryPiece split position).last_inside) ∧
    normSq (UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
          (keptTargets := completed.1) position -
          SewingRetraction.wordValue
            (fun edge : OrientedEdge 3 => triangleReadings.values edge.finish - triangleReadings.values edge.start)
            ClearBoxPaths.Chord.incidence.path) ≤ 16 * request.globalBound ∧
    normSq ((UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (position := position)
          (data := UniformPieces.entry (points := points) (firstInside := firstInside) (acquired := acquired)
            (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
            (keptTargets := completed.1) (pieces := completed.2) position)).integralSample - SewingRetraction.wordValue
            (fun edge : OrientedEdge 3 => triangleReadings.values edge.finish - triangleReadings.values edge.start)
            ClearBoxPaths.Chord.incidence.path) ≤
      2 * ((UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
            (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
            (keptTargets := completed.1) (pieces := completed.2) position) + 16 * request.globalBound)}

/-- Compare the original literal source piece after its exact retained target increment has been recovered. -/
private def comparePiece
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint))
    (raw : UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
          (keptTargets := completed.1) position =
      (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
        (auxiliaryPiece split position).lastPoint -
      (primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row).value.eval
        (auxiliaryPiece split position).firstPoint) :
    Comparison request primitives anchors offsets split completed position triangleReadings := by
  let piece := auxiliaryPiece split position
  let compared := RectangularPointReadings.Chord.compareCell
    (bank := domain.patch.models)
    (transitions := (domain.patch.sheets.refine request.index).transitions)
    (gauge := (domain.patch.sheets.refine request.index).gauge)
    request primitives anchors offsets triangleReadings domain.patch.cell_refines
    piece.column piece.row piece.first_inside piece.last_inside
  have geometric := (congrArg (fun value : Canonical => normSq (value -
      SewingRetraction.wordValue
            (fun edge : OrientedEdge 3 => triangleReadings.values edge.finish - triangleReadings.values edge.start)
            ClearBoxPaths.Chord.incidence.path)) raw).trans_le compared.property.2
  let retained := UniformPieces.entry (points := points) (firstInside := firstInside) (acquired := acquired)
            (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
            (keptTargets := completed.1) (pieces := completed.2) position
  let primitive := UniformPieces.primitive (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
    (keptTargets := completed.1) position
  have localPayment := UniformPiece.primitive_increment_le (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position) (data := retained) primitive
  have through := Norm.Bounds.normSq_sub_le_via
    (UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position) (data := retained)).integralSample
    (UniformPieces.increments (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
          (keptTargets := completed.1) position) (SewingRetraction.wordValue
            (fun edge : OrientedEdge 3 => triangleReadings.values edge.finish - triangleReadings.values edge.start)
            ClearBoxPaths.Chord.incidence.path)
  have paid := through.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct localPayment geometric) (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  exact ⟨compared.val, compared.property.1, geometric, paid⟩

/-- Compare the same actual source piece using its full retained primitive-vector factory.

The given outcome and its accepted payload remain distinct retained data.
Their exact target-vector factory recovers the SAME original dense
primitive and additive constant. The original same-cell comparison branch
then constructs its finite bound; no numerical inequality is an input.
-/
def compareTargets
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : PiecePreparation.TargetFactory (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (targetSources := pieceCoefficients request primitives split) outcome
      (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint)) :
    Comparison (channel := channel) request primitives anchors offsets split completed position triangleReadings :=
  comparePiece (channel := channel) request primitives anchors offsets split completed position triangleReadings
    (UniformPieces.increment_eq (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
      completed.1
      (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
      ((PiecePreparation.accepted_targets_eq (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (channel := channel)
        (oldBank := RectangularSheetGauge.Transitions.oriented
          (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
        (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
        (targetSources := pieceCoefficients request primitives split) outcome completed accepted).trans factory)
      position)

/-- Pay the actual value-0 source restriction against its literal signed chord on the UNCHANGED original bank.

The actual whole preparation factory and accepted success recover the
same retained primitive internally. Every original split occurrence is
accepted directly; no outer-chord endpoint assumption, domain transport,
new model/selector or primitive normalization is required.
-/
def compareValueZeroPiece {bounds : PrimitiveOverlapBounds face.clearance constantOnePolynomial}
    {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge) constantOnePolynomial)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : outcome = prepareValueZeroPieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint)) :
    Comparison (channel := 0) request primitives anchors offsets split completed position triangleReadings :=
  compareTargets (channel := 0) request primitives anchors offsets split outcome
    (prepareValueZeroPieces_targets (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives outcome factory)
    completed accepted position triangleReadings

/-- Construct the genuine value-0 child lift beside its same-bank numerical comparison, with internal incidence.

The original child consumer retains both exact Query/Point Owners, all
actual paths/joins/Entry caches, and transported old-domain evidence.
The numerical comparison remains on the original bank; coordinate_eq
links only the literal triangle coordinates and never retags either bank
or identifies a root from coordinates. Global mesh/period attachment and
old model/global target payment remain separate.
-/
def withValueZeroChild {Result : Type u}
    (families : PreparedTraceBudget.Trace.CropFamily.All parent)
    {bounds : PrimitiveOverlapBounds face.clearance constantOnePolynomial}
    {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge) constantOnePolynomial)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : outcome = prepareValueZeroPieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 0)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := constantOnePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint))
    (consume : Comparison (channel := 0) request primitives anchors offsets split
        completed position triangleReadings →
      ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
          (auxiliaryPiece split position).lastPoint =
        ClearBoxPaths.Chord.coordinate
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower))
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper)) →
      ChildConsumer (points := points) shared prefixes ordered firstInside acquired domain
        families split position Result) : Result :=
  let compared := compareValueZeroPiece request primitives anchors offsets split
    outcome factory completed accepted position triangleReadings
  PreparedParent.Crop.Observation.Points.withChildLift
    (frame := frame) (basis := basis) (points := points)
    shared prefixes ordered firstInside acquired domain families split position
    (consume compared (coordinate_eq (cropped := cropped) (points := points)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) position))

/-- Pay the actual value-1 source restriction against its literal signed chord on the UNCHANGED original bank.

The actual whole preparation factory and accepted success recover the
same retained primitive internally. Every original split occurrence is
accepted directly; no outer-chord endpoint assumption, domain transport,
new model/selector or primitive normalization is required.
-/
def compareValueOnePiece {bounds : PrimitiveOverlapBounds face.clearance coordinatePolynomial}
    {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge) coordinatePolynomial)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : outcome = prepareValueOnePieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint)) :
    Comparison (channel := 1) request primitives anchors offsets split completed position triangleReadings :=
  compareTargets (channel := 1) request primitives anchors offsets split outcome
    (prepareValueOnePieces_targets (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives outcome factory)
    completed accepted position triangleReadings

/-- Construct the genuine value-1 child lift beside its same-bank numerical comparison, with internal incidence.

The original child consumer retains both exact Query/Point Owners, all
actual paths/joins/Entry caches, and transported old-domain evidence.
The numerical comparison remains on the original bank; coordinate_eq
links only the literal triangle coordinates and never retags either bank
or identifies a root from coordinates. Global mesh/period attachment and
old model/global target payment remain separate.
-/
def withValueOneChild {Result : Type u}
    (families : PreparedTraceBudget.Trace.CropFamily.All parent)
    {bounds : PrimitiveOverlapBounds face.clearance coordinatePolynomial}
    {target : Rational} (request : GridPrimitiveAccuracy bounds domain.steps target)
    (primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge) coordinatePolynomial)
    (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : outcome = prepareValueOnePieces (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := 1)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := coordinatePolynomial) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (position : Fin split.pieces.length)
    (triangleReadings : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
        (auxiliaryPiece split position).lastPoint))
    (consume : Comparison (channel := 1) request primitives anchors offsets split
        completed position triangleReadings →
      ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
          (auxiliaryPiece split position).lastPoint =
        ClearBoxPaths.Chord.coordinate
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower))
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper)) →
      ChildConsumer (points := points) shared prefixes ordered firstInside acquired domain
        families split position Result) : Result :=
  let compared := compareValueOnePiece request primitives anchors offsets split
    outcome factory completed accepted position triangleReadings
  PreparedParent.Crop.Observation.Points.withChildLift
    (frame := frame) (basis := basis) (points := points)
    shared prefixes ordered firstInside acquired domain families split position
    (consume compared (coordinate_eq (cropped := cropped) (points := points)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) position))

end UniformPieces.Chord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
