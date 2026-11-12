module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Pieces.SharedMesh
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform.Bounds
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
public import Purelib.Riemann.Paths.RectangularSegmentSplitting.Widths
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Chain
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # Fixed-cache payment on the actual shared-mesh crop comparison

The literal occurrence bank supplies both displacement and power weights.
Its existing target grid index and source Query pay the two independent
model residuals. The finite estimate preserves every cache and primitive
constant; its measured weights are not a source-stage selection schedule.
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
open Purelib.Data.Rat.Fraction
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
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic (constantOnePolynomial coordinatePolynomial)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_add sumFin_mul_left)

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

namespace SharedMesh

variable
    (completed : PieceCompletion (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions
        (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (pieceCoefficients request primitives split))

/-- Read the same selected local cache at one literal original split occurrence. -/
abbrev piece (position : Fin split.pieces.length) :
    UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position) channel
      (RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      numerator (completed.1.get position).1.val 1 request.index gap :=
  UniformPieces.entry (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
    (keptTargets := completed.1) (pieces := completed.2) position

/-- The squared physical displacement of that same retained original source restriction. -/
def displacementCost (position : Fin split.pieces.length) : Rational :=
  normSq (piece request primitives split completed position).source.displacement

/-- The same local power-scale cache weighted by its actual physical squared displacement. -/
def powerCost (position : Fin split.pieces.length) : Rational :=
  (piece request primitives split completed position).bounds.powerScale 1 *
    displacementCost request primitives split completed position

/-- Sum actual displacement costs over the unchanged literal split occurrences. -/
def totalDisplacementCost : Rational := sumFin (displacementCost request primitives split completed)

/-- Sum actual retained power-weighted costs over the unchanged literal split occurrences. -/
def totalPowerCost : Rational := sumFin (powerCost request primitives split completed)

/-- The same cached child displacement uses the actual squared split width and original crop displacement. -/
theorem displacementCost_eq (position : Fin split.pieces.length) :
    displacementCost request primitives split completed position =
      (split.width position) ^ 2 * normSq (cropped.models.cell channel).displacement :=
  (Cell.Restriction.displacement_normSq (cropped.models.cell channel)
    (piece request primitives split completed position).restricted).trans
      (congrArg (fun width : Rational => width ^ 2 * normSq (cropped.models.cell channel).displacement)
        (split.width_eq position).symm)

/-- Every same-cache child squared displacement is nonnegative. -/
theorem displacementCost_nonnegative (position : Fin split.pieces.length) :
    0 ≤ displacementCost request primitives split completed position :=
  Norm.Basic.normSq_nonneg (piece request primitives split completed position).source.displacement

/-- The actual original crop displacement is exactly the retained physical endpoint difference. -/
theorem cropDisplacement_eq :
    (cropped.models.cell channel).displacement = parent.edge.point upper - parent.edge.point lower :=
  congrArg₂ (fun last first : Canonical => last - first)
    (cropped.models.cell_finish channel) (cropped.models.cell_start channel)

/-- Actual child displacement costs sum to at most the original physical crop displacement cost.

The same literal widths are nonnegative and sum to one. Their squared
sum is therefore at most one, with no child-count factor, new partition or
assumption on a numerical model bound.
-/
theorem totalDisplacementCost_le :
    totalDisplacementCost request primitives split completed ≤
      normSq (parent.edge.point upper - parent.edge.point lower) := by
  have exactCosts := Algebra.FiniteSum.Fin.sumFin_congr
    (fun position => displacementCost_eq request primitives split completed position)
  have factored := Algebra.FiniteSum.Fin.sumFin_mul_right
    (fun position : Fin split.pieces.length => (split.width position) ^ 2)
    (normSq (cropped.models.cell channel).displacement)
  have bounded := Arithmetic.mul_le_mul_of_nonneg_right_direct split.sum_squared_widths_le_one
    (Norm.Basic.normSq_nonneg (cropped.models.cell channel).displacement)
  exact (exactCosts.trans factored).trans_le
    ((bounded.trans_eq (Data.Rat.Fraction.Field.one_mul _)).trans_eq
      (congrArg normSq (cropDisplacement_eq (cropped := cropped) (channel := channel))))

/-- The original shared-mesh bound is paid by its actual source allowance and actual grid radius.

The two finite sums are read from the supplied completion, not supplied as
external bounds. The source ratio uses its original initial patch; the
original grid request keeps its actual index and global gluing charge.
No future request is asserted to improve any unchanged old model.
-/
theorem bound_le :
    let ratio := prepared.preparation.cell.patch.base.model.bound /
      (2 * prepared.preparation.cell.patch.inverseErrorScale)
    bound (channel := channel) request primitives split completed ≤
      targets.localBound * (split.pieces.length : Rational) *
        (96 * totalDisplacementCost request primitives split completed +
          32 * ratio * totalPowerCost request primitives split completed) +
        128 * (split.pieces.length : Rational) * totalPowerCost request primitives split completed *
          Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) request.index +
        32 * (split.pieces.length : Rational) ^ 2 * request.globalBound := by
  let ratio := prepared.preparation.cell.patch.base.model.bound /
    (2 * prepared.preparation.cell.patch.inverseErrorScale)
  let radius := Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) request.index
  let weight := 32 * targets.localBound * ratio + 128 * radius
  have perPiece (position : Fin split.pieces.length) :
      2 * (UniformPieces.localBounds (points := points) (firstInside := firstInside) (acquired := acquired)
        (domain := domain) (split := split) (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position + 16 * request.globalBound) ≤
      (96 * targets.localBound * displacementCost request primitives split completed position +
        weight * powerCost request primitives split completed position) + 32 * request.globalBound := by
    have charge : UniformPieces.localBounds (points := points) (firstInside := firstInside)
        (acquired := acquired) (domain := domain) (split := split)
        (targetSources := pieceCoefficients request primitives split)
        (keptTargets := completed.1) (pieces := completed.2) position ≤
        targets.localBound *
          (48 + 16 * ratio * (piece request primitives split completed position).bounds.powerScale 1) *
            displacementCost request primitives split completed position +
          64 * powerCost request primitives split completed position * radius :=
      UniformPiece.comparison_charge_le (points := points) (firstInside := firstInside)
        (acquired := acquired) (domain := domain) (split := split) (position := position)
        (data := piece request primitives split completed position) rfl
    have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct charge (Order.Basic.le_refl (16 * request.globalBound)))
      (show (0 : Rational) ≤ 2 by decide +kernel)
    exact bounded.trans_eq (by dsimp only [weight, powerCost]; ring1)
  have finite := Algebra.FiniteSum.Rational.Order.IndexedBudget.sumFin_le perPiece
  have folded : sumFin (fun position : Fin split.pieces.length =>
      (96 * targets.localBound * displacementCost request primitives split completed position +
        weight * powerCost request primitives split completed position) + 32 * request.globalBound) =
      96 * targets.localBound * totalDisplacementCost request primitives split completed +
        weight * totalPowerCost request primitives split completed +
        (split.pieces.length : Rational) * (32 * request.globalBound) := by
    rewrite [sumFin_add, sumFin_add, sumFin_mul_left, sumFin_mul_left,
      Algebra.FiniteSum.Fin.Rational.sum_constant]
    rfl
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct (finite.trans_eq folded)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le split.pieces.length))
  exact scaled.trans_eq (by dsimp only [weight, radius]; ring1)

/-- The SAME actual retained-bounds crop costs are paid by its pre-stage all-cell scale and physical displacement.

The whole outcome and its original producer equation retain every piece
cache. The selected-bound readback supplies each actual cache identity;
the rectangular sum bounds its scale. No D estimate or final accuracy is
a premise, and no source/model/bound producer executes in this proof.
-/
theorem totalPowerCost_le
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
    (piecePrimitives : ∀ position : Fin split.pieces.length,
      DensePrimitive (pieceCoefficients request primitives split position)
        (domain.geometry.box (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
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
      piecePrimitives cachedBounds)
    (accepted : outcome = .ok completed) :
    totalPowerCost request primitives split completed ≤
      Rectangular.powerScale cachedBounds.val 1 * normSq (parent.edge.point upper - parent.edge.point lower) := by
  have perPiece (position : Fin split.pieces.length) :
      powerCost request primitives split completed position ≤
        Rectangular.powerScale cachedBounds.val 1 * displacementCost request primitives split completed position := by
    have same := PiecePreparation.bounds_eq (points := points) (prefixes := prefixes) (ordered := ordered)
      (firstInside := firstInside) (acquired := acquired) (domain := domain) (split := split) (channel := channel)
      (oldBank := RectangularSheetGauge.Transitions.oriented
        (domain.patch.sheets.refine request.index).transitions (domain.patch.sheets.refine request.index).gauge)
      (numerator := numerator) (exponent := 1) (targetIndex := request.index) (gap := gap)
      (targetSources := pieceCoefficients request primitives split)
      rfl originalSource parentEvaluation sourceCompiled targetCompiled piecePrimitives cachedBounds
      outcome factory completed accepted position
    have original := congrArg
      (fun bounds : PrimitiveOverlapBounds
        (face.clearance.restrict
          (domain.patch.cell_refines (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
        numerator => bounds.powerScale 1) same
    have ceiling := (original.trans_le
      (Rectangular.entry_powerScale_le cachedBounds.val 1
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row))
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct ceiling
      (displacementCost_nonnegative request primitives split completed position)
  have finite := Algebra.FiniteSum.Rational.Order.IndexedBudget.sumFin_le perPiece
  have factored := Algebra.FiniteSum.Fin.sumFin_mul_left (Rectangular.powerScale cachedBounds.val 1)
    (displacementCost request primitives split completed)
  exact (finite.trans_eq factored).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (totalDisplacementCost_le request primitives split completed)
      (Rectangular.powerScale_nonnegative cachedBounds.val 1))

namespace Comparisons

variable {completed}

/-- The same retained comparison bank pays the whole source integral by the derived actual-stage bound. -/
theorem integral_difference_le_paid
    (cached : MeshReadings split anchors offsets)
    (compared : Comparisons (channel := channel) request primitives anchors offsets split completed cached) :
    let ratio := prepared.preparation.cell.patch.base.model.bound /
      (2 * prepared.preparation.cell.patch.inverseErrorScale)
    normSq ((cropped.models.cell channel).integralSample - sample request primitives anchors offsets split cached) ≤
      targets.localBound * (split.pieces.length : Rational) *
        (96 * totalDisplacementCost request primitives split completed +
          32 * ratio * totalPowerCost request primitives split completed) +
        128 * (split.pieces.length : Rational) * totalPowerCost request primitives split completed *
          Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) request.index +
        32 * (split.pieces.length : Rational) ^ 2 * request.globalBound :=
  (integral_difference_le request primitives anchors offsets split compared).trans
    (bound_le request primitives split completed)

end Comparisons

end SharedMesh

end UniformPieces.Chord

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
