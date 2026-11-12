module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.Polynomial
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial.Primitives
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
public import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # A genuine polynomial common sum on an original entered-path cover

The source PolynomialWork and Models are the actual ordinary-P caches on
the given parent cover. Both source residual and target grid floors are
paid before their models are read. The complete original geometry and
root lineage are retained; no holomorphic common sum stands in for P.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint atPoint_coordinate)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
    {start finish : Canonical} {owner : Owner (curve.polynomial.eval start)} {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {prepared : CoveredTracedPath path owner} {basis : Differential genus} {parentSheet : Fin 2}
    (entered : EnteredPath models prepared basis parentSheet)
    {differential : OddPowerDifferential curve.polynomial}
    {globalBounds : PrimitiveOverlapBounds face.clearance (differential.numerator.scale differential.scale)}
    {target : Rational}
    (budget : FragmentAccuracy globalBounds entered.domain.steps entered.mesh.splits.pieceCount target)
    {count floor stage : Nat} (covered : CoveredParents count entered.cache.parents)
    (work : PolynomialWork covered floor differential) (sourceModels : work.Models stage)
    (sourceFloor : budget.minimumIndex ≤ floor)
    {primitives : Primitives (Transitions.oriented (entered.domain.patch.sheets.refine budget.grid.index).transitions
      (entered.domain.patch.sheets.refine budget.grid.index).gauge) (differential.numerator.scale differential.scale)}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (readings : SharedPrimitiveValues anchors offsets entered.mesh.mesh.surface)

/-- Select a genuine full-polynomial face allowance before source or face models are constructed. -/
def polynomialBudget (bounds : PrimitiveOverlapBounds face.clearance
    (differential.numerator.scale differential.scale)) (amount : Rational) (positive : 0 < amount) :
    FragmentAccuracy bounds entered.domain.steps entered.mesh.splits.pieceCount (amount / 4) :=
  FragmentAccuracy.build bounds entered.domain.steps entered.mesh.splits.pieceCount (amount / 4)
    (Order.Field.div_pos_direct positive (by decide +kernel))

include sourceFloor in
/-- One supplied common polynomial model pays each actual entered split piece at the internally selected allowance. -/
private theorem polynomial_piece_lt
    (bounds : FragmentBounds entered.domain.patch basis
      (numeratorPolynomial := differential.numerator.scale differential.scale))
    (position : Fin entered.cache.parents.length)
    (piece : Riemann.Paths.RectangularSegmentSplitting.SegmentPiece entered.domain.geometry
      ((entered.cache.parents[position.val]'position.isLt).edge.point 0)
      ((entered.cache.parents[position.val]'position.isLt).edge.point 1))
    (member : piece ∈ (entered.mesh.splits.get position).pieces) :
    normSq (((atPoint readings) piece.lastPoint - (atPoint readings) piece.firstPoint) -
      ((PolynomialWork.Models.primitivePolynomial covered work sourceModels position).eval piece.lastPoint -
        (PolynomialWork.Models.primitivePolynomial covered work sourceModels position).eval piece.firstPoint)) <
      budget.perFragment := by
  let source : PolynomialWork.Models.Entry work stage position := PolynomialWork.Models.entry sourceModels position
  let patch := (covered.entry position).val
  let primitive := PolynomialModel.primitive (curve := curve) source.2.val
  have later : budget.minimumIndex ≤ source.1.val.selection.stage := sourceFloor.trans source.1.val.selection.lower
  have pieceBound := bounds.shared_polynomial_increment_le patch (covered.entry position).property primitive
    budget.grid readings (entered.mesh.splits.get_member position) piece member
    (entered.reached _ (List.getElem_mem position.isLt))
  have sourceResidual := FragmentAccuracy.uniform_residual (patch.neighborhood count).base.model later
  have analytic := bounds.residualCharge_accurate budget piece sourceResidual
  have paid := (Order.Arithmetic.add_lt_add_direct budget.ownership_accurate analytic).trans_eq
    (Field.two_halves budget.perFragment)
  exact pieceBound.trans_lt paid

include sourceFloor in
/-- Both actual floors pay the full entered-path discrepancy against the SAME supplied polynomial model bank.

Finite Cauchy uses the total original split count. The source value is the
actual original model-cell integral, with its independent constants and
stage. Root signs are derived from the entered path's original ParentReached
witnesses for the supplied covering patches.
-/
theorem polynomial_integral_lt :
    normSq ((readings.values entered.last - readings.values entered.first) -
      (PathModel.mk (PolynomialWork.Models.cells covered work sourceModels)).integralSample) < target := by
  let bounds := FragmentBounds.buildNumerator entered.domain.patch basis
    (differential.numerator.scale differential.scale)
  have actual := entered.mesh.splits.primitive_difference_lt (atPoint readings)
    (fun position point => (PolynomialWork.Models.primitivePolynomial covered work sourceModels position).eval point)
    budget.target_positive (fun position piece member => by
      have pieceBound := entered.polynomial_piece_lt budget covered work sourceModels sourceFloor readings
        bounds position piece member
      exact pieceBound.le.trans_eq budget.perFragment_eq)
  obtain ⟨chain⟩ := entered.cache.chain
  have targetSum := entered.mesh.splits.primitiveIncrements_shared (atPoint readings) chain
  have firstEq : atPoint readings start = readings.values entered.first :=
    (congrArg (atPoint readings) entered.first_eq).symm.trans (atPoint_coordinate readings entered.first)
  have lastEq : atPoint readings finish = readings.values entered.last :=
    (congrArg (atPoint readings) entered.last_eq).symm.trans (atPoint_coordinate readings entered.last)
  have targetValue := targetSum.trans (congrArg₂ (fun last first : Canonical => last - first) lastEq firstEq)
  have sourceValue := PolynomialWork.Models.parentSplits_integral covered work sourceModels entered.mesh.splits
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < target)
    (congrArg₂ (fun last first : Canonical => last - first) targetValue sourceValue)) actual

include sourceFloor readings in
/-- Actual supplied endpoint readings are close to the SAME genuine polynomial model integral.

The two original endpoint slots may be partial, repeated or stationary.
Their given point readings retain the actual primitive owners and offsets;
the independent source and grid floors pay their comparison with the
retained entered-mesh readings. No containing grid edge is substituted.
-/
theorem polynomial_points_lt {pointCount : Nat} {point : Fin pointCount → Canonical}
    (points : PointReadings anchors offsets point)
    (first last : Fin pointCount) (firstEq : point first = start) (lastEq : point last = finish)
    (amount : Rational) (allocation : target = amount / 4) :
    normSq ((points.values last - points.values first) -
      (PathModel.mk (PolynomialWork.Models.cells covered work sourceModels)).integralSample) < amount := by
  have ownerBound := RectangularPointReadings.GridPrimitiveAccuracy.point_increment_bound
    budget.grid points readings entered.domain.patch.cell_refines
    first last entered.first entered.last (entered.first_eq.trans firstEq.symm) (entered.last_eq.trans lastEq.symm)
  have analytic := (entered.polynomial_integral_lt budget covered work sourceModels sourceFloor readings).trans_eq
    allocation
  have perLe : budget.perFragment ≤ amount / 4 := by
    rewrite [budget.perFragment_eq]
    exact (Approximation.Rational.Budget.Aggregate.perTerm_le budget.target_positive.le _).trans_eq allocation
  have ownership : 32 * budget.grid.globalBound < amount / 4 :=
    budget.ownership_accurate.trans_le
      ((Order.Field.divide_le_self budget.perFragment_positive.le (by decide +kernel)).trans perLe)
  let meshValue := readings.values entered.last - readings.values entered.first
  let common := (PathModel.mk (PolynomialWork.Models.cells covered work sourceModels)).integralSample
  have identity : (points.values last - points.values first) - common =
      ((points.values last - points.values first) - meshValue) + (meshValue - common) := by ring1
  rewrite [identity]
  have triangle := Norm.Bounds.normSq_add_le_two
    ((points.values last - points.values first) - meshValue) (meshValue - common)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle analytic
  rewrite [Norm.Basic.normSq_eq_canonical]
  have estimate := triangle.trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct ownerBound analytic.le) (by decide : (0 : Rational) ≤ 2))
  have total : 2 * (16 * budget.grid.globalBound + amount / 4) < amount := by
    have paid := Order.Arithmetic.add_lt_add_right_direct ownership (amount / 4)
    have quarter : amount / 4 + amount / 4 + amount / 4 + amount / 4 = amount := by
      rewrite [show amount / 4 + amount / 4 + amount / 4 + amount / 4 = (amount / 4) * 4 by ring1]
      exact Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
    have paid' := Order.Arithmetic.add_lt_add_right_direct paid (amount / 4)
    have remaining := Order.Arithmetic.add_lt_add_left_direct (allocation ▸ budget.target_positive)
      (amount / 4 + amount / 4 + amount / 4)
    have neutral : (amount / 4 + amount / 4 + amount / 4) + 0 = amount / 4 + amount / 4 + amount / 4 :=
      (Field.add_comm _ _).trans (Field.zero_add _)
    have translated := Eq.mp (congrArg (fun value : Rational =>
      value < amount / 4 + amount / 4 + amount / 4 + amount / 4) neutral) remaining
    have final := paid'.trans translated
    exact (show 2 * (16 * budget.grid.globalBound + amount / 4) =
      32 * budget.grid.globalBound + amount / 4 + amount / 4 by ring1).trans_lt (final.trans_eq quarter)
  exact estimate.trans_lt total

include sourceFloor readings in
/-- The SAME full-polynomial corner cache is close to the genuine supplied common model integral.

The quarter-target allocation and original point/grid comparison pay both
endpoint-owner changes. This statement retains the actual model stages,
primitive constants and corner owners; its discrepancy is derived internally.
-/
theorem polynomial_corner_lt (corners : PointReadings anchors offsets (Corners.FaceCorners.point face.cell.box))
    (first last : Fin 4) (firstEq : Corners.FaceCorners.point face.cell.box first = start)
    (lastEq : Corners.FaceCorners.point face.cell.box last = finish)
    (amount : Rational) (allocation : target = amount / 4) :
    normSq ((corners.values last - corners.values first) -
      (PathModel.mk (PolynomialWork.Models.cells covered work sourceModels)).integralSample) < amount :=
  entered.polynomial_points_lt budget covered work sourceModels sourceFloor readings
    corners first last firstEq lastEq amount allocation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath
