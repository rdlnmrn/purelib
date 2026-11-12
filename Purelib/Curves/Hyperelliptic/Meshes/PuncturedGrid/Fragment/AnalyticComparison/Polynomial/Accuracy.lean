module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial.Readings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Requested accuracy of retained polynomial fragment comparisons

The original finite fragment allocation chooses the source and face floors
from the actual geometric piece count. Those floors pay the same cached
polynomial charges, with the supplied models, constants and endpoint views
unchanged. No comparison or observation is repeated to establish payment.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Algebra.FiniteSum.Fin.Rational (sum_constant)
open Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget (sumFin_le)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Readings.RectangularExteriorBoundary.Geometry (allCells)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.LinearAlgebra.Grid (Offsets)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target : Rational} {request : LocalRequest parent count target}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable {assigned : SheetEntry fragment domains request}

section Pieces

variable {numerator : CoefficientPolynomial} {sourceIndex faceIndex : Nat}
variable {sourceInverse : Model curve.polynomial request.neighborhood.base.box}
variable {sourceFactory : sourceInverse = request.neighborhood.base.refine sourceIndex}
variable {primitive : PrimitiveModel request.neighborhood sourceIndex numerator}
variable {primitives : Primitives (Transitions.oriented (assigned.domain.patch.sheets.refine faceIndex).transitions
  (assigned.domain.patch.sheets.refine faceIndex).gauge) numerator}

namespace NumeratorPieceComparison

variable {piece : SegmentPiece assigned.domain.geometry fragment.located.first fragment.located.last}
variable {member : piece ∈ assigned.split.pieces}
variable (kept : NumeratorPieceComparison assigned sourceInverse sourceFactory primitive primitives piece member)

/-- The retained analytic charge is the original scalar residual charge on the same actual cell and subfragment.

The whole supplied source and target refinements retain their own indices.
The numerator and inverse ceilings read the same original face restriction;
no new inverse, transition or polynomial comparison is constructed.
-/
theorem charge_eq_residualCharge
    (bounds : FragmentBounds assigned.domain.patch source (numeratorPolynomial := numerator)) :
    kept.charge = bounds.residualCharge piece
      (quarterRadius request.neighborhood.base.model.bound sourceIndex) faceIndex := by
  have leftBound := (congrArg Model.bound kept.left_eq).trans (Model.refine_bound _ _)
  have sourceBound := (congrArg Model.bound sourceFactory).trans (Model.refine_bound _ _)
  have numeratorBound : kept.bounds.numeratorUpper = bounds.numerator piece.column piece.row :=
    kept.bounds.numeratorUpper_eq.trans (bounds.numerator_eq piece.column piece.row).symm
  have inverseBound : kept.bounds.inverseUpper = bounds.inverse :=
    kept.bounds.inverseUpper_eq.trans bounds.inverse_eq.symm
  refine kept.charge_eq.trans ?_
  unfold numeratorPieceCharge FragmentBounds.residualCharge
  rewrite [leftBound, sourceBound, numeratorBound, inverseBound, Norm.Basic.normSq_eq_canonical]
  rfl

/-- The independently selected source and face floors pay the actual cached polynomial analytic charge.

The original allocation is raised to its supplied later face index. The
source residual comes from the given model's retained refinement equation
and its separate source floor; the comparison is not executed again.
-/
theorem charge_accurate
    {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance numerator}
    {requested : Rational}
    (budget : FragmentAccuracy globalBounds assigned.domain.steps assigned.split.count requested)
    (sourceLater : budget.minimumIndex ≤ sourceIndex) (faceLater : budget.grid.index ≤ faceIndex) :
    2 * kept.charge < budget.perFragment / 2 := by
  let bounds := FragmentBounds.buildNumerator assigned.domain.patch source numerator
  let raised := budget.atGridIndex faceIndex faceLater
  have paid := bounds.residualCharge_accurate raised piece
    (Face.FragmentAccuracy.uniform_residual request.neighborhood.base.model sourceLater)
  change 2 * bounds.residualCharge piece
    (quarterRadius request.neighborhood.base.model.bound sourceIndex) faceIndex < budget.perFragment / 2 at paid
  exact Eq.mpr (congrArg (fun value : Rational => 2 * value < budget.perFragment / 2)
    (kept.charge_eq_residualCharge bounds)) paid

end NumeratorPieceComparison

namespace NumeratorFragmentComparison.Cache

variable {globalBounds : PrimitiveOverlapBounds fragment.face.located.face.clearance numerator}
variable {tolerance : Rational} {accuracy : GridPrimitiveAccuracy globalBounds assigned.domain.steps tolerance}
variable {targetPrimitives : Primitives
  (Transitions.oriented (assigned.domain.patch.sheets.refine accuracy.index).transitions
    (assigned.domain.patch.sheets.refine accuracy.index).gauge) numerator}
variable {anchors : PrimitiveAnchors targetPrimitives} {offsets : Offsets anchors.edges} {points : List Canonical}
variable {mesh : CommonMesh assigned.domain.geometry (allCells assigned.domain.geometry) points}
variable {included : ∀ point ∈ assigned.split.points, point ∈ points}
variable {readings : SharedPrimitiveValues anchors offsets mesh.surface}
variable (kept : Cache assigned sourceInverse sourceFactory primitive accuracy targetPrimitives mesh included readings)

/-- The actual polynomial comparison bound meets its requested target once both original floors are paid.

The original fragment allocation is constructed from geometry and numerator
bounds before observations. Its literal piece count pays both finite-sum
factors, including an empty split. All charges are read from the supplied
comparison cache, without repeating their producers.
-/
theorem bound_lt {requested : Rational}
    (budget : FragmentAccuracy globalBounds assigned.domain.steps assigned.split.count requested)
    (sourceLater : budget.minimumIndex ≤ sourceIndex) (faceLater : budget.grid.index ≤ accuracy.index) :
    kept.bound < requested := by
  let raised := budget.atGridIndex accuracy.index faceLater
  have globalEq : raised.grid.globalBound = accuracy.globalBound :=
    raised.grid.globalBound_eq_of_index_eq accuracy rfl
  have ownership : 32 * accuracy.globalBound < budget.perFragment / 2 :=
    Eq.mp (congrArg (fun value : Rational => 32 * value < budget.perFragment / 2) globalEq)
      raised.ownership_accurate
  have each : ∀ position : Fin assigned.split.pieces.length,
      32 * accuracy.globalBound + 2 *
        (pieceAt assigned sourceInverse sourceFactory primitive accuracy targetPrimitives kept.pieces position).charge ≤
          budget.perFragment := by
    intro position
    have analytic := (pieceAt assigned sourceInverse sourceFactory primitive
      accuracy targetPrimitives kept.pieces position).charge_accurate budget sourceLater faceLater
    exact ((Order.Arithmetic.add_lt_add_direct ownership analytic).trans_eq
      (Field.two_halves budget.perFragment)).le
  have summed := sumFin_le each
  have constant := (sum_constant assigned.split.pieces.length budget.perFragment).trans
    (congrArg (fun value : Nat => (value : Rational) * budget.perFragment) assigned.split.count_eq.symm)
  have bounded := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct summed
    (Cast.Order.natCast_le_direct (Nat.zero_le assigned.split.count))
  have paid : (assigned.split.count : Rational) * ((assigned.split.count : Rational) * budget.perFragment) <
      requested := by
    rewrite [budget.perFragment_eq]
    exact Approximation.Rational.Budget.Aggregate.count_mul_perTerm_lt budget.target_positive assigned.split.count
  exact kept.bound_eq.trans_lt ((bounded.trans_eq
    (congrArg (fun value : Rational => (assigned.split.count : Rational) * value) constant)).trans_lt paid)

end NumeratorFragmentComparison.Cache

end Pieces

namespace PolynomialModelComparison

variable {modelFloor : Nat} {differential : OddPowerDifferential curve.polynomial}
variable {sourceBounds : UniformBounds (request.patch.neighborhood count)}
variable {allowance : Rational} {positive : 0 < allowance}
variable {uniform : UniformRequest sourceBounds 0 (differential.numerator.scale differential.scale)
  modelFloor (allowance / 4)}
variable {first last : Canonical} {coordinate : Spatial.Coordinate first last}
variable {model : PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive}
variable {points : List Canonical} {index : Nat} {tolerance : Rational}
variable {budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains}
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable {shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics}
variable {included : ∀ point ∈ assigned.split.points, point ∈ points}
variable {view : EndpointReadings.Cache assigned shared included}
variable (compared : EndpointCache assigned model view)

/-- The original source selection and retained numerical index pay the same endpoint comparison's computed bound.

The original selection's lower-bound certificate pays the source minimum.
The face floor concerns the actual numerical index of the given endpoint
view, and its genuine polynomial accuracy stays on that same budget owner.
-/
theorem endpoint_bound_lt {requested : Rational}
    (budget : FragmentAccuracy (EndpointReadings.budget view).globalBounds
      assigned.domain.steps assigned.split.count requested)
    (sourceFloor : budget.minimumIndex ≤ modelFloor) (faceLater : budget.grid.index ≤ index) :
    compared.comparison.bound < requested :=
  NumeratorFragmentComparison.Cache.bound_lt compared.comparison budget
    (sourceFloor.trans uniform.selection.lower)
    (faceLater.trans_eq (endpointAccuracy_index assigned view).symm)

include compared in
/-- Paid original floors give the requested strict increment error on the same retained literal endpoint slots. -/
theorem endpoint_increment_lt {requested : Rational}
    (budget : FragmentAccuracy (EndpointReadings.budget view).globalBounds
      assigned.domain.steps assigned.split.count requested)
    (sourceFloor : budget.minimumIndex ≤ modelFloor) (faceLater : budget.grid.index ≤ index) :
    normSq (((EndpointReadings.reading view).values 1 - (EndpointReadings.reading view).values 0) -
      (model.primitive.primitive.value.eval fragment.located.last -
        model.primitive.primitive.value.eval fragment.located.first)) < requested :=
  (endpoint_increment_le compared).trans_lt (endpoint_bound_lt compared budget sourceFloor faceLater)

end PolynomialModelComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
