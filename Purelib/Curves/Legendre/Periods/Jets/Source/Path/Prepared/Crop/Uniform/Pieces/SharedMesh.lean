module

public import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces.Chord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.SharedMesh
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Children
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Chord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.ContinuedPoints
import Purelib.Riemann.Paths.ClearBoxPaths.Chord
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Dependent

/-! # Genuine child comparisons against one retained shared numerical mesh

One original common mesh, primitive value vector, lookup bank and triangle
view bank are retained inputs. The actual value-channel producer outcome
and physical child consumer stay unchanged. Their local finite comparison
is transported to the two literal indexed axis-leg occurrences in that
same shared numerical cache, without selecting another source or model.

The same child callbacks construct supported source-edge words and actual
contained transport rows between all three retained mesh Points. New join
payments, signed common-refinement incidence, global root return and
canonical cycle attachment remain separate certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Face.PrimitiveComparison
open Face.Entries.FaceModels.Entry (PointData TracedPoint)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
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
open Purelib.Riemann.Readings.RectangularPointReadings.Chord (MeshReadings)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
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
open Purelib.Algebra.FiniteSum.Fin (sumFin)

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
    (prefixes : Trace.CropFamily.Checked parent lower lowerInside)
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

namespace SharedMesh

/-- The exact local source-integral payment against the retained shared-bank indexed word. -/
@[expose] def IntegralBound
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets)
    : Prop :=
    normSq ((UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
          (domain := domain) (split := split) (position := position)
          (data := UniformPieces.entry (points := points) (firstInside := firstInside) (acquired := acquired)
            (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
            (keptTargets := completed.1) (pieces := completed.2) position)).integralSample -
        SewingRetraction.wordValue
          (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
            (MeshReadings.shared split cached).values edge.finish -
              (MeshReadings.shared split cached).values edge.start)
          (MeshReadings.word split cached position)) ≤
      2 * (UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position + 16 * request.globalBound)

/-- The existing comparison pays the same source integral against the actual indexed shared-bank word.

Only the exact cached target-word readback is transported. The original
comparison, source restriction, target primitives and local charge remain
unchanged; no primitive constant or global incidence is a premise.
-/
theorem integral_le
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets)
    (compared : Comparison request primitives anchors offsets split completed position
      ((MeshReadings.triangles split cached).get position)) :
    IntegralBound request primitives anchors offsets split completed position cached :=
  Eq.mp (congrArg (fun value : Canonical =>
    normSq ((UniformPiece.source (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      (data := UniformPieces.entry (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position)).integralSample - value) ≤
      2 * (UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position + 16 * request.globalBound))
      (MeshReadings.wordValue_eq split cached position)) compared.property.2.2

section Whole

variable
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (cached : MeshReadings split anchors offsets)

/-- The same-cell comparison cache at every original split occurrence on the one retained shared mesh.

Each entry retains its actual source restriction, target primitive reading
and local payment. The original completion and shared numerical bank remain
the owners; repeated and stationary pieces retain their own positions.
-/
@[expose] def Comparisons :=
  Data.Vector.DependentVector (fun position : Fin split.pieces.length =>
    Comparison (channel := channel) request primitives anchors offsets split completed position
      ((MeshReadings.triangles split cached).get position))

omit completed in
/-- Sum the two retained indexed leg readings at every original piece in its literal occurrence order. -/
def sample : Canonical :=
  sumFin (fun position : Fin split.pieces.length =>
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
        (MeshReadings.shared split cached).values edge.finish -
          (MeshReadings.shared split cached).values edge.start)
      (MeshReadings.word split cached position))

/-- The finite whole-crop payment keeps the original piece count and every actual local allowance.

The common mesh gluing charge is included once per original piece before
finite Cauchy sums the errors. This quantity makes no decay or requested
global accuracy claim for the unchanged old models.
-/
@[expose] def bound : Rational :=
  (split.pieces.length : Rational) * sumFin (fun position : Fin split.pieces.length =>
    2 * (UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
      (keptTargets := completed.1) (pieces := completed.2) position + 16 * request.globalBound))

namespace Comparisons

variable {completed cached}

/-- The complete original crop integral obeys the summed payment against the same shared-mesh readings.

The existing source restriction readback identifies the exact original
crop integral. Each actual cached comparison supplies its own local bound;
finite Cauchy sums those bounds without replacing any primitive constant,
source model, numerical bank or signed occurrence.
-/
theorem integral_difference_le
    (compared : Comparisons (channel := channel) request primitives anchors offsets split completed cached) :
    normSq ((cropped.models.cell channel).integralSample - sample request primitives anchors offsets split cached) ≤
      bound (channel := channel) request primitives split completed := by
  let sources := UniformPieces.sourceSamples (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
    (keptTargets := completed.1) (pieces := completed.2)
  let values := fun position : Fin split.pieces.length =>
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
        (MeshReadings.shared split cached).values edge.finish -
          (MeshReadings.shared split cached).values edge.start)
      (MeshReadings.word split cached position)
  let payments := fun position : Fin split.pieces.length =>
    2 * (UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
      (keptTargets := completed.1) (pieces := completed.2) position + 16 * request.globalBound)
  have perPiece (position : Fin split.pieces.length) :
      normSq (sources position - values position) ≤ payments position :=
    (congrArg (fun source : Canonical => normSq (source - values position))
      (UniformPieces.sourceSamples_eq (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position)).trans_le
      (integral_le (channel := channel) request primitives anchors offsets split completed position cached
        (compared.get position))
  have finite := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin sources values payments perPiece
  have original := UniformPieces.source_integral_eq (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split)
    (targetSources := pieceCoefficients request primitives split) (keptTargets := completed.1) (pieces := completed.2)
  exact (congrArg (fun source : Canonical => normSq (source - sumFin values)) original).symm.trans_le finite

/-- Retain the actual shared-mesh comparison bank from one SAME complete target-vector factory.

Only the original PointReadings comparison executes at each literal
occurrence. Both producer paths supply this exact full-vector readback;
no source/primitive factory, normalization or final bound is an input.
-/
def ofTargets
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
    (cached : MeshReadings split anchors offsets) :
    Comparisons (channel := channel) request primitives anchors offsets split completed cached :=
  Data.Vector.DependentVector.ofFn (fun position =>
    compareTargets (channel := channel) request primitives anchors offsets split
      outcome factory completed accepted position ((MeshReadings.triangles split cached).get position))

/-- Compare an actual retained-bounds outcome against the SAME shared numerical mesh.

Its own producer equation yields the full original target factory. The
accepted payload, certified rectangular bounds and whole primitives stay
attached to that actual outcome. This construction executes no preparation,
new grid request or source/Point/model factory.
-/
def withBounds
    (originalSource : Polynomial)
    (parentEvaluation : ∀ value : Rational,
      Evaluation.eval (prepared.preparation.cell.models.cell channel).polynomial ⟨value, 0⟩ =
        originalSource.eval (prepared.preparation.cell.models.coordinate.point value))
    (sourceCompiled : ∀ point : Canonical, originalSource.eval point =
      numerator.eval point * (prepared.preparation.cell.request.model.value.eval point) ^ 1)
    (targetCompiled : ∀ position (point : Canonical), (pieceCoefficients request primitives split position).eval point =
      numerator.eval point *
        ((RectangularSheetGauge.Transitions.oriented
          (domain.patch.sheets.refine request.index).transitions
          (domain.patch.sheets.refine request.index).gauge).ready
            (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.value.eval point ^ 1)
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    (outcome : PiecePreparation (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))
    (factory : outcome = preparePiecesWithBounds (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split) rfl originalSource parentEvaluation sourceCompiled targetCompiled
      (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
      cachedBounds)
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split)) (accepted : outcome = .ok completed)
    (cached : MeshReadings split anchors offsets) :
    Comparisons (channel := channel) request primitives anchors offsets split completed cached :=
  let targetFactory := PiecePreparation.targetsWithBounds_eq (points := points) (prefixes := prefixes)
    (ordered := ordered) (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
    (channel := channel)
    (oldBank := RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
    (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
    (targetSources := pieceCoefficients request primitives split)
    rfl originalSource parentEvaluation sourceCompiled targetCompiled
    (fun position => primitives.dense (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
    cachedBounds outcome factory
  ofTargets (channel := channel) request primitives anchors offsets split
    outcome targetFactory completed accepted cached

/-- Construct and retain every value-0 comparison on the same original shared mesh.

Each actual primitive comparison is built once in original piece order,
using the retained producer outcome, accepted completion and cached
triangle readings. No physical child query or numerical bank is rebuilt.
-/
def valueZero {bounds : PrimitiveOverlapBounds face.clearance constantOnePolynomial}
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
    (cached : MeshReadings split anchors offsets) :
    Comparisons (channel := 0) request primitives anchors offsets split completed cached :=
  ofTargets (channel := 0) request primitives anchors offsets split outcome
    (prepareValueZeroPieces_targets (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives outcome factory)
    completed accepted cached

/-- Construct and retain every value-1 comparison on the same original shared mesh.

Each actual primitive comparison is built once in original piece order,
using the retained producer outcome, accepted completion and cached
triangle readings. No physical child query or numerical bank is rebuilt.
-/
def valueOne {bounds : PrimitiveOverlapBounds face.clearance coordinatePolynomial}
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
    (cached : MeshReadings split anchors offsets) :
    Comparisons (channel := 1) request primitives anchors offsets split completed cached :=
  ofTargets (channel := 1) request primitives anchors offsets split outcome
    (prepareValueOnePieces_targets (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split)
      (targetIndex := request.index) (gap := gap) rfl primitives outcome factory)
    completed accepted cached

end Comparisons

end Whole

/-- The actual child consumer extended by its original three mesh Points and both rooted source words.

Every original child Query, crop, join, Entry and whole domain remains in
its original telescope. All three numerical views retain the SAME supplied surface and original
slot lookups. The actual PointData attachment consumer is reused in path
order1start,0corner,2finish, with each physical root owner kept separate.
The dependent tail constructs both supported leg words on those SAME
Points, retaining the actual rows, target comparisons and unpaid joins.
-/
@[expose] def MeshConsumer
    {numericalModels : Bank (Fibre.frameCurve frame).polynomial domain.geometry}
    {numericalPrimitives : Primitives numericalModels numerator}
    (anchors : PrimitiveAnchors numericalPrimitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (families : Trace.CropFamily.All parent)
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets) (Result : Type u) :=
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  let firstFraction := Cell.Restriction.parameter lower upper piece.interval.lower
  let lastFraction := Cell.Restriction.parameter lower upper piece.interval.upper
  let firstBound := Cell.Restriction.parameter_inside lowerInside upperInside firstUnit
  let lastBound := Cell.Restriction.parameter_inside lowerInside upperInside lastUnit
  let firstEq := piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let lastEq := piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let firstFace := Eq.mp (congrArg face.cell.box.Contains firstEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
  let lastFace := Eq.mp (congrArg face.cell.box.Contains lastEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
  (first : RootedQuery (frame := frame) prepared firstFraction firstBound) →
  first = cropped.queryAt piece.interval.lower firstUnit →
  (last : RootedQuery (frame := frame) prepared lastFraction lastBound) →
  last = cropped.queryAt piece.interval.upper lastUnit →
  (prefixPath : OwnerPath (Paths.polynomial parameter) (parent.edge.point lower) cropped.endpoints.1.direct.owner
    (parent.edge.point firstFraction) first.direct.owner) →
  prefixPath = prefixes.val firstFraction firstBound
    (Cell.Restriction.parameter_ge_left ordered firstUnit.1) cropped.endpoints.1.direct first.direct →
  (carried : Entry shared.models (parent.edge.point firstFraction) first.sample.owner) →
  carried.sheet = acquired.entry.sheet →
  (moving : OwnerPath (Paths.polynomial parameter) (parent.edge.point firstFraction) first.direct.owner
    (parent.edge.point lastFraction) last.direct.owner) →
  moving = (families firstFraction firstBound).val lastFraction lastBound
    (Cell.Restriction.parameter_le ordered piece.interval.ordered.le) first.direct last.direct →
  (vertices : moving.vertices = [parent.edge.point lastFraction]) →
  (sourceJoin : OwnerJoin first.sample.owner first.direct.owner) →
  sourceJoin = OwnerJoin.acquire first.sample.owner first.direct.owner first.sampleRoots.symm →
  (targetJoin : OwnerJoin last.direct.owner last.sample.owner) →
  targetJoin = OwnerJoin.acquire last.direct.owner last.sample.owner last.sampleRoots →
  (childAcquired : Entry.Acquisition shared.models firstFace first.sample.owner) →
  childAcquired = Entry.Acquisition.build shared.models firstFace first.sample.owner →
  (sameSheet : childAcquired.entry.sheet = acquired.entry.sheet) →
  (childDomain : PeriodDomain shared.models childAcquired.entry.sheet) →
  childDomain = PeriodDomain.castSheet sameSheet.symm domain →
  HEq childDomain domain →
  (geometry : ClearBoxPaths.Chord.Prepared face.clearance face.cell.box_proper
    (parent.edge.point firstFraction) (parent.edge.point lastFraction) firstFace lastFace) →
  geometry = ClearBoxPaths.Chord.prepare face.clearance face.cell.box_proper
    (parent.edge.point firstFraction) (parent.edge.point lastFraction) firstFace lastFace →
  (lifted : Face.PrimitiveData.Chord.Lifted (curve := Fibre.frameCurve frame)
    (basis := basis) (parent := parent.edge)
    (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
    (firstInside := firstFace) (lastInside := lastFace)
    shared geometry (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := firstFraction) (inside := firstBound)))
      (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := lastFraction) (inside := lastBound)))
      moving vertices sourceJoin targetJoin
      childAcquired childDomain count) →
  lifted = Face.PrimitiveData.Chord.ofAcquired (curve := Fibre.frameCurve frame)
    (basis := basis) (parent := parent.edge)
    (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
    (firstInside := firstFace) (lastInside := lastFace)
    shared geometry (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := firstFraction) (inside := firstBound)))
      (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := lastFraction) (inside := lastBound)))
      moving vertices sourceJoin targetJoin
      childAcquired childDomain count →
  piece.firstPoint = parent.edge.point firstFraction →
  piece.lastPoint = parent.edge.point lastFraction →
  let cornerPoint := ClearBoxPaths.Chord.corner (parent.edge.point firstFraction) (parent.edge.point lastFraction)
  let cornerInside := ClearBoxPaths.Chord.corner_inside firstFace lastFace
  (cornerData : PointData (curve := Fibre.frameCurve frame) cornerPoint) →
  cornerData = PointData.ofPoint (curve := Fibre.frameCurve frame) lifted.sample
    lifted.neighborhood.center_inside →
  (cornerAcquired : Entry.Acquisition shared.models cornerInside cornerData.sample.owner) →
  cornerAcquired = Entry.Acquisition.build shared.models cornerInside cornerData.sample.owner →
  (cornerSheet : cornerAcquired.entry.sheet = childAcquired.entry.sheet) →
  (cornerDomain : PeriodDomain shared.models cornerAcquired.entry.sheet) →
  cornerDomain = PeriodDomain.castSheet (cornerSheet.trans sameSheet).symm domain →
  HEq cornerDomain domain →
  (finishAcquired : Entry.Acquisition shared.models lastFace last.sample.owner) →
  finishAcquired = Entry.Acquisition.build shared.models lastFace last.sample.owner →
  (finishSheet : finishAcquired.entry.sheet = childAcquired.entry.sheet) →
  (finishDomain : PeriodDomain shared.models finishAcquired.entry.sheet) →
  finishDomain = PeriodDomain.castSheet (finishSheet.trans sameSheet).symm domain →
  HEq finishDomain domain →
  HEq lifted.domain.geometry domain.geometry →
  (firstViewTriangles : List (ModelTriangle lifted.domain.geometry)) →
  HEq firstViewTriangles (MeshReadings.mesh split cached).triangles →
  (firstView : OwnedTriangulation firstViewTriangles) →
  HEq firstView (MeshReadings.mesh split cached).surface →
  firstView.mesh.vertices = (MeshReadings.mesh split cached).surface.mesh.vertices →
  (firstLookup : VertexLookup firstView.mesh.vertices (parent.edge.point firstFraction)) →
  HEq firstLookup (((MeshReadings.lookups split cached).get position).get (1 : Fin 3)) →
  firstLookup.index.val =
    (((MeshReadings.lookups split cached).get position).get (1 : Fin 3)).index.val →
  HEq (firstView.owners firstLookup.index)
    ((MeshReadings.mesh split cached).surface.owners
      (((MeshReadings.lookups split cached).get position).get (1 : Fin 3)).index) →
  HEq cornerDomain.geometry domain.geometry →
  (cornerViewTriangles : List (ModelTriangle cornerDomain.geometry)) →
  HEq cornerViewTriangles (MeshReadings.mesh split cached).triangles →
  (cornerView : OwnedTriangulation cornerViewTriangles) →
  HEq cornerView (MeshReadings.mesh split cached).surface →
  cornerView.mesh.vertices = (MeshReadings.mesh split cached).surface.mesh.vertices →
  (cornerLookup : VertexLookup cornerView.mesh.vertices cornerPoint) →
  HEq cornerLookup (((MeshReadings.lookups split cached).get position).get (0 : Fin 3)) →
  cornerLookup.index.val =
    (((MeshReadings.lookups split cached).get position).get (0 : Fin 3)).index.val →
  HEq (cornerView.owners cornerLookup.index)
    ((MeshReadings.mesh split cached).surface.owners
      (((MeshReadings.lookups split cached).get position).get (0 : Fin 3)).index) →
  HEq finishDomain.geometry domain.geometry →
  (finishViewTriangles : List (ModelTriangle finishDomain.geometry)) →
  HEq finishViewTriangles (MeshReadings.mesh split cached).triangles →
  (finishView : OwnedTriangulation finishViewTriangles) →
  HEq finishView (MeshReadings.mesh split cached).surface →
  finishView.mesh.vertices = (MeshReadings.mesh split cached).surface.mesh.vertices →
  (finishLookup : VertexLookup finishView.mesh.vertices (parent.edge.point lastFraction)) →
  HEq finishLookup (((MeshReadings.lookups split cached).get position).get (2 : Fin 3)) →
  finishLookup.index.val =
    (((MeshReadings.lookups split cached).get position).get (2 : Fin 3)).index.val →
  HEq (finishView.owners finishLookup.index)
    ((MeshReadings.mesh split cached).surface.owners
      (((MeshReadings.lookups split cached).get position).get (2 : Fin 3)).index) →
  Face.PrimitiveData.Chord.Lifted.FirstVertexConsumer
    (curve := Fibre.frameCurve frame) (basis := basis) (parent := parent.edge)
    (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
    (firstInside := firstFace) (lastInside := lastFace) (shared := shared) (geometry := geometry)
    (first := (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
      (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
        (fraction := firstFraction) (inside := firstBound))))
    (last := (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
      (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
        (fraction := lastFraction) (inside := lastBound))))
    (moving := moving) (vertices := vertices) (sourceJoin := sourceJoin) (targetJoin := targetJoin)
    (acquired := childAcquired) (retainedDomain := childDomain) (count := count)
    lifted firstView firstLookup count Result
    (afterPoint := fun firstMeshPoint =>
      PointData.MeshVertexConsumer (curve := Fibre.frameCurve frame) (models := shared.models)
        (geometry := cornerDomain.geometry) cornerData cornerInside cornerAcquired cornerDomain.patch
        cornerView cornerLookup basis count Result
        (afterPoint := fun cornerMeshPoint =>
          PointData.MeshVertexConsumer (curve := Fibre.frameCurve frame) (models := shared.models)
            (geometry := finishDomain.geometry) (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
              (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
                (fraction := lastFraction) (inside := lastBound))) lastFace finishAcquired finishDomain.patch
            finishView finishLookup basis count Result
            (afterPoint := fun finishMeshPoint =>
              FaceModels.PieceConsumer (curve := Fibre.frameCurve frame) (branches := branches)
                (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
                (domainSheet := acquired.entry.sheet) (domain := domain) (numerator := numerator)
                (numericalModels := numericalModels) (primitives := numericalPrimitives)
                (anchors := anchors) (offsets := offsets) (cuts := domain.cuts)
                (sourceStart := parent.edge.point lower) (sourceFinish := parent.edge.point upper)
                (split := split) (cached := cached) (position := position)
                (firstSheet := childAcquired.entry.sheet) (middleSheet := cornerAcquired.entry.sheet)
                (lastSheet := finishAcquired.entry.sheet)
                (start := parent.edge.point firstFraction) (corner := cornerPoint)
                (finish := parent.edge.point lastFraction)
                (firstInside := firstFace) (middleInside := cornerInside) (lastInside := lastFace)
                (firstCount := count) (middleCount := count) (lastCount := count)
                (firstFrame := childAcquired.pointFrame) (middleFrame := cornerAcquired.pointFrame)
                (lastFrame := finishAcquired.pointFrame)
                (first := firstMeshPoint) (middle := cornerMeshPoint) (last := finishMeshPoint) Result)))

/-- Invoke the original word consumer on three abstract retained Points with all original indices explicit.

The sheet relations are the actual corner and finish acquisition readbacks.
They determine Entry lineage only through each Point's original entry_sheet
law. Only scalar endpoint incidence is transported, and no Point, selector,
physical child or numerical cache is acquired here.
-/
private def atMeshPoints
    {numericalModels : Bank (Fibre.frameCurve frame).polynomial domain.geometry}
    {numericalPrimitives : Primitives numericalModels numerator}
    (anchors : PrimitiveAnchors numericalPrimitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets)
    {firstSheet middleSheet lastSheet : Fin 2} {start finish : Canonical}
    {startInside : face.cell.box.Contains start}
    {cornerInside : face.cell.box.Contains (ClearBoxPaths.Chord.corner start finish)}
    {finishInside : face.cell.box.Contains finish} {firstCount middleCount lastCount : Nat}
    {firstFrame : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval start)}
    {middleFrame : OwnerFrame
      ((Fibre.frameCurve frame).polynomial.eval (ClearBoxPaths.Chord.corner start finish))}
    {lastFrame : OwnerFrame ((Fibre.frameCurve frame).polynomial.eval finish)}
    (firstMeshPoint : TracedPoint shared.models firstSheet start startInside firstCount firstFrame)
    (cornerMeshPoint : TracedPoint shared.models middleSheet (ClearBoxPaths.Chord.corner start finish)
      cornerInside middleCount middleFrame)
    (finishMeshPoint : TracedPoint shared.models lastSheet finish finishInside lastCount lastFrame)
    (cornerSheet : middleSheet = firstSheet) (finishSheet : lastSheet = firstSheet)
    (firstEq : (auxiliaryPiece split position).firstPoint = start)
    (lastEq : (auxiliaryPiece split position).lastPoint = finish) {Result : Type u}
    (consume : FaceModels.PieceConsumer (curve := Fibre.frameCurve frame) (branches := branches)
      (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
      (domainSheet := acquired.entry.sheet) (domain := domain) (numerator := numerator)
      (numericalModels := numericalModels) (primitives := numericalPrimitives)
      (anchors := anchors) (offsets := offsets) (cuts := domain.cuts)
      (sourceStart := parent.edge.point lower) (sourceFinish := parent.edge.point upper)
      (split := split) (cached := cached) (position := position)
      (firstSheet := firstSheet) (middleSheet := middleSheet) (lastSheet := lastSheet)
      (start := start) (corner := ClearBoxPaths.Chord.corner start finish) (finish := finish)
      (firstInside := startInside) (middleInside := cornerInside) (lastInside := finishInside)
      (firstCount := firstCount) (middleCount := middleCount) (lastCount := lastCount)
      (firstFrame := firstFrame) (middleFrame := middleFrame) (lastFrame := lastFrame)
      (first := firstMeshPoint) (middle := cornerMeshPoint) (last := finishMeshPoint) Result) : Result :=
  have firstSheetEq := TracedPoint.entry_sheet (curve := Fibre.frameCurve frame) (branches := branches)
    (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
    (sheet := firstSheet) (point := start)
    (inside := startInside) (count := firstCount) (targetFrame := firstFrame) firstMeshPoint
  have middleSheetEq := TracedPoint.entry_sheet (curve := Fibre.frameCurve frame) (branches := branches)
    (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
    (sheet := middleSheet)
    (point := ClearBoxPaths.Chord.corner start finish) (inside := cornerInside) (count := middleCount)
    (targetFrame := middleFrame) cornerMeshPoint
  have lastSheetEq := TracedPoint.entry_sheet (curve := Fibre.frameCurve frame) (branches := branches)
    (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
    (sheet := lastSheet) (point := finish)
    (inside := finishInside) (count := lastCount) (targetFrame := lastFrame) finishMeshPoint
  have firstLineage := firstSheetEq.trans (cornerSheet.symm.trans middleSheetEq.symm)
  have lastLineage := middleSheetEq.trans ((cornerSheet.trans finishSheet.symm).trans lastSheetEq.symm)
  have middlePointEq := congrArg₂ ClearBoxPaths.Chord.corner firstEq lastEq
  FaceModels.withPieceWords (curve := Fibre.frameCurve frame) (branches := branches)
    (higher := higher) (bank := bank) (frames := rootFrames) (face := face) (models := shared.models)
    (domainSheet := acquired.entry.sheet) (domain := domain) (numerator := numerator)
    (numericalModels := numericalModels) (primitives := numericalPrimitives)
    (anchors := anchors) (offsets := offsets) (cuts := domain.cuts)
    (sourceStart := parent.edge.point lower) (sourceFinish := parent.edge.point upper)
    (split := split) (cached := cached) (position := position)
    (firstSheet := firstSheet) (middleSheet := middleSheet) (lastSheet := lastSheet)
    (start := start) (corner := ClearBoxPaths.Chord.corner start finish) (finish := finish)
    (firstInside := startInside) (middleInside := cornerInside) (lastInside := finishInside)
    (firstCount := firstCount) (middleCount := middleCount) (lastCount := lastCount)
    (firstFrame := firstFrame) (middleFrame := middleFrame) (lastFrame := lastFrame)
    (first := firstMeshPoint) (middle := cornerMeshPoint) (last := finishMeshPoint)
    (firstLineage := firstLineage) (lastLineage := lastLineage)
    (firstPointEq := firstEq) (middlePointEq := middlePointEq) (lastPointEq := lastEq) consume

/-- The exact original consume-to-child function type, with its actual input owners and callback tail retained. -/
private def SlotFunction
    {numericalModels : Bank (Fibre.frameCurve frame).polynomial domain.geometry}
    {numericalPrimitives : Primitives numericalModels numerator}
    (anchors : PrimitiveAnchors numericalPrimitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (families : Trace.CropFamily.All parent)
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets) (Result : Type u) :=
  MeshConsumer (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
    (firstInside := firstInside) (acquired := acquired) (domain := domain)
    anchors offsets split families position cached Result →
  ChildConsumer (points := points) shared prefixes ordered firstInside acquired domain
    families split position Result

/-- Construct the three original slot attachments and both supported rooted words on the same retained child.

The same actual mesh Points feed both leg rows after their three original
attachment callbacks. Entry lineage is derived from their retained sheets
and the genuine corner/finish acquisitions; geometric incidences use only
the original child endpoint laws. The new joins remain unpaid here.
-/
private def attachSlots
    {numericalModels : Bank (Fibre.frameCurve frame).polynomial domain.geometry}
    {numericalPrimitives : Primitives numericalModels numerator}
    (anchors : PrimitiveAnchors numericalPrimitives) (offsets : Offsets anchors.edges)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (families : Trace.CropFamily.All parent)
    (position : Fin split.pieces.length) (cached : MeshReadings split anchors offsets) {Result : Type u} :
    SlotFunction (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain)
      anchors offsets split families position cached Result :=
  fun consume =>
    let piece := auxiliaryPiece split position
    let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
      ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
    let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
      ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
    let firstFraction := Cell.Restriction.parameter lower upper piece.interval.lower
    let lastFraction := Cell.Restriction.parameter lower upper piece.interval.upper
    let firstBound := Cell.Restriction.parameter_inside lowerInside upperInside firstUnit
    let lastBound := Cell.Restriction.parameter_inside lowerInside upperInside lastUnit
    let oldFirstEq := piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) position
    let oldLastEq := piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
      (acquired := acquired) (domain := domain) (split := split) position
    let firstFace := Eq.mp (congrArg face.cell.box.Contains oldFirstEq)
      ((domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
    let lastFace := Eq.mp (congrArg face.cell.box.Contains oldLastEq)
      ((domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
    fun first firstFactory last lastFactory prefixPath prefixEq carried carriedSheet moving movingEq vertices
        sourceJoin sourceJoinEq targetJoin targetJoinEq childAcquired childAcquiredEq sameSheet childDomain
        childDomainEq
        domainHEq geometry geometryEq lifted liftedEq firstEq lastEq =>
      let mesh := MeshReadings.mesh split cached
      let firstStored := ((MeshReadings.lookups split cached).get position).get (1 : Fin 3)
      let cornerStored := ((MeshReadings.lookups split cached).get position).get (0 : Fin 3)
      let finishStored := ((MeshReadings.lookups split cached).get position).get (2 : Fin 3)
      let cornerInside := ClearBoxPaths.Chord.corner_inside firstFace lastFace
      let cornerData := PointData.ofPoint (curve := Fibre.frameCurve frame) lifted.sample
        lifted.neighborhood.center_inside
      let cornerAcquired := Entry.Acquisition.build shared.models cornerInside cornerData.sample.owner
      have cornerSheet : cornerAcquired.entry.sheet = childAcquired.entry.sheet :=
        (cornerAcquired.entry.sheet_unique lifted.cornerEntry cornerInside).trans lifted.corner_sheet
      let cornerDomain := PeriodDomain.castSheet (cornerSheet.trans sameSheet).symm domain
      let finishAcquired := Entry.Acquisition.build shared.models lastFace last.sample.owner
      have finishSheet : finishAcquired.entry.sheet = childAcquired.entry.sheet :=
        (finishAcquired.entry.sheet_unique lifted.lastEntry lastFace).trans lifted.last_sheet
      let finishDomain := PeriodDomain.castSheet (finishSheet.trans sameSheet).symm domain
      have targetEq : lifted.domain = PeriodDomain.castSheet sameSheet.symm domain :=
        lifted.domain_eq.trans childDomainEq
      have firstPointEq : ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint (1 : Fin 3) =
          parent.edge.point firstFraction :=
        (ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint).2.1.trans firstEq
      have cornerPointEq : ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint (0 : Fin 3) =
          ClearBoxPaths.Chord.corner (parent.edge.point firstFraction) (parent.edge.point lastFraction) :=
        (ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint).1.trans
          (congrArg₂ ClearBoxPaths.Chord.corner firstEq lastEq)
      have finishPointEq : ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint (2 : Fin 3) =
          parent.edge.point lastFraction :=
        (ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint).2.2.trans lastEq
      PeriodDomain.withSurfaceView (curve := Fibre.frameCurve frame) (models := shared.models)
        sameSheet.symm domain lifted.domain targetEq mesh.surface firstStored firstPointEq
        (fun firstGeometryHEq firstViewTriangles firstTrianglesHEq firstView firstSurfaceHEq firstVerticesEq
            firstLookup firstLookupHEq firstIndexEq firstOwnerHEq =>
          PeriodDomain.withSurfaceView (curve := Fibre.frameCurve frame) (models := shared.models)
            (cornerSheet.trans sameSheet).symm domain cornerDomain rfl mesh.surface cornerStored cornerPointEq
            (fun cornerGeometryHEq cornerViewTriangles cornerTrianglesHEq cornerView cornerSurfaceHEq cornerVerticesEq
                cornerLookup cornerLookupHEq cornerIndexEq cornerOwnerHEq =>
              PeriodDomain.withSurfaceView (curve := Fibre.frameCurve frame) (models := shared.models)
                (finishSheet.trans sameSheet).symm domain finishDomain rfl mesh.surface finishStored finishPointEq
                (fun finishGeometryHEq finishViewTriangles finishTrianglesHEq finishView finishSurfaceHEq
                    finishVerticesEq
                    finishLookup finishLookupHEq finishIndexEq finishOwnerHEq =>
                  Face.PrimitiveData.Chord.Lifted.withFirstMeshVertex
                    (curve := Fibre.frameCurve frame) (basis := basis) (parent := parent.edge)
                    (lower := firstFraction) (upper := lastFraction)
                    (lowerInside := firstBound) (upperInside := lastBound)
                    (firstInside := firstFace) (lastInside := lastFace) (shared := shared) (geometry := geometry)
                    (first := (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
                      (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
                        (fraction := firstFraction) (inside := firstBound))))
                    (last := (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
                      (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
                        (fraction := lastFraction) (inside := lastBound))))
                    (moving := moving) (vertices := vertices) (sourceJoin := sourceJoin) (targetJoin := targetJoin)
                    (acquired := childAcquired) (retainedDomain := childDomain) (count := count)
                    lifted firstView firstLookup count
                    (fun kept keptEq firstOwned firstOwnedEq firstCellInside firstCell firstCellEq firstMeshPoint
                      firstMeshPointEq firstFrameEq firstSelection firstSelectionFactoryEq firstSelectionHEq
                      firstSelectionEq firstSelected firstSelectedFactoryEq firstSelectedEq firstSelectedFrameEq
                      firstSelectedSheetEq firstSelectedIndexEq firstCompared firstComparedEq firstRoute firstCovered
                      firstParents firstRoots firstMeshRoots firstMeshRootsEq firstNear =>
                      PointData.withMeshVertex (curve := Fibre.frameCurve frame) (models := shared.models)
                        (geometry := cornerDomain.geometry) cornerData cornerInside cornerAcquired cornerDomain.patch
                        cornerView cornerLookup basis count
                        (fun cornerOwned cornerOwnedEq cornerCellInside cornerCell cornerCellEq cornerMeshPoint
                          cornerMeshPointEq cornerFrameEq cornerSelection cornerSelectionFactoryEq cornerSelectionHEq
                          cornerSelectionEq cornerSelected cornerSelectedFactoryEq cornerSelectedEq
                          cornerSelectedFrameEq cornerSelectedSheetEq cornerSelectedIndexEq cornerCompared
                          cornerComparedEq cornerRoute cornerCovered cornerParents cornerRoots cornerMeshRoots
                          cornerMeshRootsEq cornerNear =>
                          PointData.withMeshVertex (curve := Fibre.frameCurve frame) (models := shared.models)
                            (geometry := finishDomain.geometry)
                            (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
                              (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
                                (fraction := lastFraction) (inside := lastBound)))
                            lastFace finishAcquired finishDomain.patch
                            finishView finishLookup basis count
                            (fun finishOwned finishOwnedEq finishCellInside finishCell finishCellEq finishMeshPoint
                              finishMeshPointEq finishFrameEq finishSelection finishSelectionFactoryEq
                              finishSelectionHEq
                              finishSelectionEq finishSelected finishSelectedFactoryEq finishSelectedEq
                              finishSelectedFrameEq finishSelectedSheetEq finishSelectedIndexEq finishCompared
                              finishComparedEq finishRoute finishCovered finishParents finishRoots finishMeshRoots
                              finishMeshRootsEq finishNear =>
                              atMeshPoints (points := points) (shared := shared)
                                (firstInside := firstInside) (acquired := acquired) (domain := domain)
                                (numericalModels := numericalModels) (numericalPrimitives := numericalPrimitives)
                                anchors offsets split position cached
                                (firstSheet := childAcquired.entry.sheet) (middleSheet := cornerAcquired.entry.sheet)
                                (lastSheet := finishAcquired.entry.sheet)
                                (start := parent.edge.point firstFraction) (finish := parent.edge.point lastFraction)
                                (startInside := firstFace) (cornerInside := cornerInside) (finishInside := lastFace)
                                (firstCount := count) (middleCount := count) (lastCount := count)
                                (firstFrame := childAcquired.pointFrame) (middleFrame := cornerAcquired.pointFrame)
                                (lastFrame := finishAcquired.pointFrame)
                                firstMeshPoint cornerMeshPoint finishMeshPoint cornerSheet finishSheet firstEq lastEq
                                (consume first firstFactory last lastFactory prefixPath prefixEq carried carriedSheet
                                  moving movingEq vertices sourceJoin sourceJoinEq targetJoin targetJoinEq childAcquired
                                  childAcquiredEq sameSheet childDomain childDomainEq domainHEq geometry geometryEq
                                  lifted
                                  liftedEq firstEq lastEq cornerData rfl cornerAcquired rfl cornerSheet cornerDomain rfl
                                  (PeriodDomain.castSheet_heq (cornerSheet.trans sameSheet).symm domain)
                                  finishAcquired rfl
                                  finishSheet finishDomain rfl
                                  (PeriodDomain.castSheet_heq (finishSheet.trans sameSheet).symm domain)
                                  firstGeometryHEq
                                  firstViewTriangles firstTrianglesHEq firstView firstSurfaceHEq firstVerticesEq
                                  firstLookup firstLookupHEq firstIndexEq firstOwnerHEq cornerGeometryHEq
                                  cornerViewTriangles cornerTrianglesHEq cornerView cornerSurfaceHEq cornerVerticesEq
                                  cornerLookup cornerLookupHEq cornerIndexEq cornerOwnerHEq finishGeometryHEq
                                  finishViewTriangles finishTrianglesHEq finishView finishSurfaceHEq finishVerticesEq
                                  finishLookup finishLookupHEq finishIndexEq finishOwnerHEq kept keptEq firstOwned
                                  firstOwnedEq firstCellInside firstCell firstCellEq firstMeshPoint firstMeshPointEq
                                  firstFrameEq firstSelection firstSelectionFactoryEq firstSelectionHEq firstSelectionEq
                                  firstSelected firstSelectedFactoryEq firstSelectedEq firstSelectedFrameEq
                                  firstSelectedSheetEq firstSelectedIndexEq firstCompared firstComparedEq firstRoute
                                  firstCovered firstParents firstRoots firstMeshRoots firstMeshRootsEq firstNear
                                  cornerOwned cornerOwnedEq cornerCellInside cornerCell cornerCellEq cornerMeshPoint
                                  cornerMeshPointEq cornerFrameEq cornerSelection cornerSelectionFactoryEq
                                  cornerSelectionHEq cornerSelectionEq cornerSelected cornerSelectedFactoryEq
                                  cornerSelectedEq cornerSelectedFrameEq cornerSelectedSheetEq cornerSelectedIndexEq
                                  cornerCompared cornerComparedEq cornerRoute cornerCovered cornerParents cornerRoots
                                  cornerMeshRoots cornerMeshRootsEq cornerNear
                                  finishOwned finishOwnedEq finishCellInside finishCell finishCellEq finishMeshPoint
                                  finishMeshPointEq finishFrameEq finishSelection finishSelectionFactoryEq
                                  finishSelectionHEq finishSelectionEq finishSelected finishSelectedFactoryEq
                                  finishSelectedEq finishSelectedFrameEq finishSelectedSheetEq finishSelectedIndexEq
                                  finishCompared finishComparedEq finishRoute finishCovered finishParents finishRoots
                                  finishMeshRoots finishMeshRootsEq finishNear)))))))

/-- Construct the actual value-0 child with triangle readings indexed from the same retained common mesh.

The original constructor performs its one numerical comparison and child
lift. Its callback keeps the same comparison, both endpoint Query/Point
owners, paths, joins, Entries and transported-domain evidence. The SAME
numerical surface and three original lookups are reindexed through actual
domain transports. Existing corner and finish Points receive their missing
acquisitions once, with sheets derived from the actual original Entries.
The one PointData algorithm retains all three root/cell-route caches.
The shared continuation then constructs both actual supported leg rows on
those same Points. The theorem integral_le preserves the original
numerical payment; it does not pay the new transport joins.
-/
def withValueZeroChild {Result : Type u}
    (families : Trace.CropFamily.All parent)
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
    (cached : MeshReadings split anchors offsets)
    (consume : Comparison (channel := 0) request primitives anchors offsets split
        completed position ((MeshReadings.triangles split cached).get position) →
      IntegralBound (channel := 0) request primitives anchors offsets split completed position cached →
      ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
          (auxiliaryPiece split position).lastPoint =
        ClearBoxPaths.Chord.coordinate
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower))
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper)) →
      MeshConsumer (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain)
        anchors offsets split families position cached Result) : Result :=
  UniformPieces.Chord.withValueZeroChild families request primitives anchors offsets split
    outcome factory completed accepted position ((MeshReadings.triangles split cached).get position)
    (fun compared incidence =>
      attachSlots (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain)
        anchors offsets split families position cached
        (consume compared
          (integral_le (channel := 0) request primitives anchors offsets split completed position cached compared)
          incidence))

/-- Construct the actual value-1 child with triangle readings indexed from the same retained common mesh.

The original constructor performs its one numerical comparison and child
lift. Its callback keeps the same comparison, both endpoint Query/Point
owners, paths, joins, Entries and transported-domain evidence. The SAME
numerical surface and three original lookups are reindexed through actual
domain transports. Existing corner and finish Points receive their missing
acquisitions once, with sheets derived from the actual original Entries.
The one PointData algorithm retains all three root/cell-route caches.
The shared continuation then constructs both actual supported leg rows on
those same Points. The theorem integral_le preserves the original
numerical payment; it does not pay the new transport joins.
-/
def withValueOneChild {Result : Type u}
    (families : Trace.CropFamily.All parent)
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
    (cached : MeshReadings split anchors offsets)
    (consume : Comparison (channel := 1) request primitives anchors offsets split
        completed position ((MeshReadings.triangles split cached).get position) →
      IntegralBound (channel := 1) request primitives anchors offsets split completed position cached →
      ClearBoxPaths.Chord.coordinate (auxiliaryPiece split position).firstPoint
          (auxiliaryPiece split position).lastPoint =
        ClearBoxPaths.Chord.coordinate
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.lower))
          (parent.edge.point (Cell.Restriction.parameter lower upper (auxiliaryPiece split position).interval.upper)) →
      MeshConsumer (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain)
        anchors offsets split families position cached Result) : Result :=
  UniformPieces.Chord.withValueOneChild families request primitives anchors offsets split
    outcome factory completed accepted position ((MeshReadings.triangles split cached).get position)
    (fun compared incidence =>
      attachSlots (points := points) (shared := shared) (prefixes := prefixes) (ordered := ordered)
        (firstInside := firstInside) (acquired := acquired) (domain := domain)
        anchors offsets split families position cached
        (consume compared
          (integral_le (channel := 1) request primitives anchors offsets split completed position cached compared)
          incidence))

end SharedMesh

end UniformPieces.Chord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
