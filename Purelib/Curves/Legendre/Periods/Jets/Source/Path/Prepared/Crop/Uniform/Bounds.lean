module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Bounds
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Polynomial
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Actual charged source-piece bounds on retained source and grid stages

The source restriction and target pullback retain their original allowances.
The SAME paid source Query bounds its selected inverse residual, and the
SAME refined rectangular model supplies its independent geometric radius.
No new observation, stage cast, primitive or power table is constructed.
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
open Purelib.Data.Rat.Fraction
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

namespace UniformPiece

/-- The two residual payments expand into separate allowance and grid charges. -/
private theorem charge_payment_identity (allowance scale ratio radius cost : Rational) :
    (48 * allowance + 64 * (scale * (radius + ratio * (allowance / 4)))) * cost =
      allowance * (48 + 16 * ratio * scale) * cost + 64 * (scale * cost) * radius := by
  rewrite [Field.div_eq_mul_inv_direct allowance 4]
  have coefficient : (4 : Rational)⁻¹ * 64 = 16 := by decide +kernel
  calc
    _ = (48 * allowance + 64 * scale * radius +
        scale * ratio * allowance * ((4 : Rational)⁻¹ * 64)) * cost := by ring1
    _ = _ := by
      rewrite [coefficient]
      ring1

/-- Nonnegative scalar weights preserve the separate source and grid residual payments. -/
private theorem charge_payment_le (allowance scale ratio radius cost grid source : Rational)
    (scaleNonnegative : 0 ≤ scale) (costNonnegative : 0 ≤ cost)
    (gridPaid : grid ≤ radius) (sourcePaid : source ≤ ratio * (allowance / 4)) :
    (48 * allowance + 64 * scale * (grid + source)) * cost ≤
      allowance * (48 + 16 * ratio * scale) * cost + 64 * (scale * cost) * radius := by
  have gap := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct gridPaid sourcePaid) scaleNonnegative
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct gap
    (show (0 : Rational) ≤ 64 by decide +kernel)
  have charged := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.add_le_add_direct (Order.Basic.le_refl (48 * allowance)) scaled) costNonnegative
  have same : (48 * allowance + 64 * scale * (grid + source)) * cost =
      (48 * allowance + 64 * (scale * (grid + source))) * cost := by ring1
  exact same.trans_le (charged.trans_eq (charge_payment_identity allowance scale ratio radius cost))

variable {channel : Fin 6} {targetIndex exponent : Nat}
    {oldBank : Bank (Paths.polynomial parameter) domain.geometry} {numerator targetSource : Polynomial}
    {gap : AccuracyRequest}
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel oldBank numerator targetSource exponent targetIndex gap)

/-- The same two retained source restrictions preserve the original path Targets allowance. -/
theorem source_allowance_eq : data.source.localAllowance = targets.localBound :=
  (Cell.Restriction.model_allowance (cropped.models.cell channel) data.restricted).trans
    ((Cell.Restriction.model_allowance (prepared.preparation.cell.models.cell channel)
      (cropped.models.channelCache channel)).trans
      ((prepared.preparation.cell.models.cell_allowance channel).trans prepared.allowance_eq))

/-- The actual charged comparison expands using both retained model bounds and the same physical displacement. -/
theorem comparison_charge_eq :
    16 * (data.source.localAllowance + data.target.model.localAllowance) * normSq data.source.displacement =
      (48 * targets.localBound + 64 * data.bounds.powerScale exponent *
        ((oldBank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.bound +
          prepared.preparation.cell.request.model.bound)) * normSq data.source.displacement := by
  have targetAllowance := data.target.allowance_eq
  rewrite [targetAllowance, source_allowance_eq (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) (position := position) (data := data),
    UniformObservation.polynomialCharge_eq]
  ring1

/-- The actual grid residual and source Query pay the same retained piece's charged comparison.

The grid equation identifies its original target bank, without changing
its cached index. The source model is bounded through its own original
value-zero request. The ratio uses the same initial source patch and is
independent of its selected numerical stage.
-/
theorem comparison_charge_le
    (oldBankEq : oldBank = RectangularSheetGauge.Transitions.oriented
      (domain.patch.sheets.refine targetIndex).transitions (domain.patch.sheets.refine targetIndex).gauge) :
    let ratio := prepared.preparation.cell.patch.base.model.bound /
      (2 * prepared.preparation.cell.patch.inverseErrorScale)
    16 * (data.source.localAllowance + data.target.model.localAllowance) * normSq data.source.displacement ≤
      targets.localBound * (48 + 16 * ratio * data.bounds.powerScale exponent) * normSq data.source.displacement +
        64 * (data.bounds.powerScale exponent * normSq data.source.displacement) *
          Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) targetIndex := by
  let ratio := prepared.preparation.cell.patch.base.model.bound /
    (2 * prepared.preparation.cell.patch.inverseErrorScale)
  have old := congrArg (fun bank : Bank (Paths.polynomial parameter) domain.geometry =>
    (bank.ready (auxiliaryPiece split position).column (auxiliaryPiece split position).row).model.bound) oldBankEq
  have oriented := RectangularSheetGauge.Bank.orient_bound (domain.patch.models.refine targetIndex)
    (domain.patch.sheets.refine targetIndex).gauge.values
    (auxiliaryPiece split position).column (auxiliaryPiece split position).row
  have grid : (oldBank.ready (auxiliaryPiece split position).column
      (auxiliaryPiece split position).row).model.bound ≤
      Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) targetIndex :=
    (old.trans oriented).trans_le
      (domain.patch.models.refine_uniform_bound targetIndex
        (auxiliaryPiece split position).column (auxiliaryPiece split position).row)
  have source : prepared.preparation.cell.request.model.bound ≤ ratio * (targets.localBound / 4) :=
    prepared.preparation.query.model_bound_le_allowance.trans_eq
      (congrArg (fun allowance : Rational => ratio * (allowance / 4)) prepared.allowance_eq)
  exact (comparison_charge_eq (points := points) (firstInside := firstInside) (acquired := acquired)
    (domain := domain) (split := split) (position := position) (data := data)).trans_le
      (charge_payment_le targets.localBound (data.bounds.powerScale exponent) ratio
        (Approximation.Rational.Geometric.Basic.quarterRadius (1 / 256) targetIndex)
        (normSq data.source.displacement) _ _ (data.bounds.powerScale_nonnegative exponent)
        (Norm.Basic.normSq_nonneg data.source.displacement) grid source)

end UniformPiece

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
