module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Requested scalar accuracy for original grid fragments

Each original fragment consumes its retained face and sheet budget. Both
polynomial indices pay the same preselected residual allowance.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings (meshBudget)

open Purelib.Riemann.Normalization.InverseRootPolynomial

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Differentials.Basic.Differential genus}
  {axes : PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {partition : Rectangle.AxisPartition 0 1 (axes.parameters parent)} {interval :
    Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularFaces.RegularPrimitiveFragment axes parent partition
    interval}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {count : Nat} {target : Coordinate} {request :
    Readings.UniformPreparedRequests.LocalRequest parent count target}
  {fragments : Nat} {tolerance : Coordinate}

/-- Read the original fragment's scalar budget through its retained face, sheet and domain equalities. -/
@[expose] def scalarBudget (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : FaceScalarBudgets source fragments
      tolerance domains) : DomainScalarBudget
      assigned.domain source fragments tolerance :=
  (((FaceScalarBudgets.get budgets
    fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain assigned.domain_eq.symm

/-- The original fragment mesh budget is exactly the mesh constructed from its retained scalar budget. -/
theorem meshBudget_scalar (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : FaceScalarBudgets source fragments
      tolerance domains) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    BankReadings.meshBudget assigned
      (FaceScalarBudgets.meshes points budgets) =
      (ScalarAccuracy.scalarBudget assigned budgets).meshBudget points := by
  unfold BankReadings.meshBudget
    ScalarAccuracy.scalarBudget
  rw [FaceScalarBudgets.meshes_get, ←
    FaceScalarBudget.castFace_meshes,
    FaceScalarBudget.meshes_atSheet,
      DomainScalarBudget.castDomain_meshBudget]
  rfl

/-- The original fragment's minimum comparison stage is below the retained common face-budget stage. -/
theorem scalarBudget_minimum_le (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : FaceScalarBudgets source fragments
      tolerance domains) :
    (ScalarAccuracy.scalarBudget assigned budgets).certificate.minimumIndex
      ≤ FaceScalarBudgets.index budgets := by
  unfold ScalarAccuracy.scalarBudget
  rw [DomainScalarBudget.castDomain_minimumIndex]
  exact ((FaceScalarBudget.atSheet _
    _).certificate.grid_ge.trans
    (FaceScalarBudget.atSheet_le _ _)).trans
    ((FaceScalarBudget.castFace_index _ _).trans_le
      (FaceScalarBudgets.get_le budgets _))

/-- Every original inverse model's residual at a later index is below the common one-sixteenth geometric residual. -/
private theorem uniform_residual {polynomial : Normalization.InverseRootPolynomial.Polynomial} {box :
  Normalization.InverseRootPolynomial.Box} (model : Model polynomial box)
    {minimum index : Nat} (later : minimum ≤ index) :
    Rational.Geometric.Basic.quarterRadius model.bound index ≤
      Rational.Geometric.Basic.quarterRadius (1 / 16) minimum :=
  (quarterRadius_antitone model.bound_nonnegative later).trans (by
    simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
      (Arithmetic.pow_nonneg_direct (by decide) minimum))

/-- Both sufficiently late original polynomial readings make twice the analytic piece charge smaller than half its
retained fragment allowance. -/
theorem pieceCharge_accurate (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (bounds : Face.FragmentReadings.FragmentBounds assigned.domain.patch source)
    {globalBounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds fragment.face.located.face.clearance
      (Readings.PreparedPrimitiveSamples.differentialNumerator source)}
    (budget : Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy globalBounds assigned.domain.steps fragments
      tolerance)
    (piece : Paths.RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last) (index : Nat)
    (leftLater : budget.minimumIndex ≤ index) (rightLater : budget.minimumIndex ≤ request.request.index) :
    2 * AnalyticComparison.pieceCharge assigned bounds piece index <
      budget.perFragment / 2 := open Data in by
  let residual := Rational.Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex
  have residualNonnegative : 0 ≤ residual := Rational.Geometric.Basic.quarterRadius_nonneg (by decide +kernel) _
  have left := ScalarAccuracy.uniform_residual
    (assigned.domain.patch.transported.cell piece.column piece.row).model
    (leftLater.trans (Nat.le_add_right _ 2))
  have right := ScalarAccuracy.uniform_residual
    request.neighborhood.base.model rightLater
  have productNonnegative : 0 ≤ bounds.numerator piece.column piece.row * bounds.inverse :=
    Arithmetic.mul_nonneg_direct (bounds.atCell piece.column piece.row).numeratorUpper_nonnegative
      (bounds.atCell piece.column piece.row).inverseUpper_positive.le
  have globalNonnegative := Arithmetic.mul_nonneg_direct
    globalBounds.numeratorUpper_nonnegative globalBounds.inverseUpper_positive.le
  have movement := Rational.Box.normSq_sub_le_diagonalSq
    ((assigned.domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
    ((assigned.domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
  have weightBound := Arithmetic.mul_le_mul_direct (bounds.product_le globalBounds piece.column
    piece.row)
    movement (Gaussian.Norm.Basic.normSq_nonneg _) globalNonnegative
  have factorBound := Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right)
    (by decide : (0 : Coordinate) ≤ 12)
  have bound := Arithmetic.mul_le_mul_direct factorBound weightBound
    (Arithmetic.mul_nonneg_direct productNonnegative (Gaussian.Norm.Basic.normSq_nonneg _))
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg residualNonnegative residualNonnegative))
  have charged : AnalyticComparison.pieceCharge assigned bounds piece index
    ≤
      24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
        fragment.face.located.face.cell.box.diagonalSq := by
    exact (by unfold AnalyticComparison.pieceCharge; ring1 :
      AnalyticComparison.pieceCharge assigned bounds piece index =
      _).trans_le
      (bound.trans_eq (by change 12 * (residual + residual) * _ = _; ring1))
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct charged (by
      decide : (0 : Coordinate) ≤ 2)).trans_lt
    ((by ring1 : 2 * (24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
      fragment.face.located.face.cell.box.diagonalSq) =
      48 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
        fragment.face.located.face.cell.box.diagonalSq).trans_lt budget.analytic_accurate)

/-- Transporting the retained face owner preserves the original selected domain step count. -/
private theorem castFace_steps {first last : Meshes.PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
    (equal : first = last) (cached : Face.DomainBanks.FaceDomains frames first)
      (sheet : Fin 2) :
    ((cached.castFace equal).domain sheet).steps = (cached.domain sheet).steps := by
  cases equal
  rfl

/-- The original fragment's selected domain steps are bounded by the retained whole-bank maximum. -/
theorem domain_steps_le (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
  : assigned.domain.steps ≤
  (FaceDomainBank.stepsBound domains) := by
  rw [assigned.domain_eq]
  unfold SheetEntries.RegularPrimitiveFragment.domainCache Face.DomainBanks.FaceDomainBank.atLocation
  rw [ScalarAccuracy.castFace_steps]
  exact FaceDomainBank.get_steps_le domains _ _

/-- The original fragment split count is at most twice the retained maximum domain steps plus five. -/
theorem split_count_le (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
  : assigned.split.count ≤ 2 *
  (FaceDomainBank.stepsBound domains) + 5 := by
  have bound := assigned.split.count_le
  have domainBound := ScalarAccuracy.domain_steps_le assigned
  omega

open Purelib.Algebra.FiniteSum.Rational in
/-- Bound a finite charge sum by its count-paid allowance.

The fixed ownership and analytic factors charge each original occurrence.
Structural summation preserves those factors and the supplied per-entry allowance. -/
private theorem charges_le {α : Type} (items : List α) (charges : α → Coordinate)
  (ownership allowance : Coordinate)
    (bounded : ∀ item ∈ items, 32 * ownership + 2 * charges item ≤ allowance) :
    32 * Aggregate.countCoordinate items.length * ownership +
      2 * Squares.coordinateSum (items.map charges) ≤
        Aggregate.countCoordinate items.length * allowance := by
  simp only [Aggregate.countCoordinate_eq]
  induction items with
  | nil => change 32 * 0 * ownership + 2 * 0 ≤ 0 * allowance; exact (by ring1 : _ = _).le
  | cons first rest ih =>
      have tail := ih (fun item member => bounded item (List.mem_cons_of_mem _ member))
      have both := add_le_add (bounded first List.mem_cons_self) tail
      simp only [List.length_cons, Algebra.NatCast.add, Nat.cast_one, List.map_cons, Squares.coordinateSum]
      exact (by ring1 : _ = _).trans_le (both.trans_eq (by ring1))

/-- The retained fragment comparison bound is at most its actual split count squared times the original paid fragment
allowance. -/
theorem BankReading.bound_le (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (scalars : FaceScalarBudgets source fragments
      tolerance domains) {points : List Normalization.InverseRootPolynomial.Gaussian} {index : Nat}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
    {shared : Face.CommonMeshes.FaceSharedMeshes
      (FaceScalarBudgets.meshes points scalars)
      numerics}
    (reading : BankReadings.BankReading assigned shared)
    (leftLater : FaceScalarBudgets.index scalars ≤
      index)
    (rightLater : FaceScalarBudgets.index scalars ≤
      request.request.index) :
    reading.bound ≤ Aggregate.countCoordinate assigned.split.count *
      (Aggregate.countCoordinate assigned.split.count * Aggregate.perTerm tolerance
        fragments) := by
  let scalar := ScalarAccuracy.scalarBudget assigned scalars
  let accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex
    (BankReadings.meshBudget assigned
      (FaceScalarBudgets.meshes points
        scalars)).accuracy index
    (BankReadings.meshReadings assigned shared).later
  have left := (ScalarAccuracy.scalarBudget_minimum_le assigned
    scalars).trans leftLater
  have right := (ScalarAccuracy.scalarBudget_minimum_le assigned
    scalars).trans rightLater
  have ownership : 32 * accuracy.globalBound < Aggregate.perTerm tolerance fragments / 2 := by
    have estimate := Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide +kernel : (0 : Coordinate) < 32) accuracy.accurate
    exact estimate.trans_eq (by
      change 32 * (Aggregate.perTerm tolerance fragments / 64) = Aggregate.perTerm
        tolerance fragments / 2
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = Aggregate.perTerm tolerance fragments * (32 * (64 :
          Coordinate)⁻¹) := by
          ring1
        _ = _ := by rw [show (32 : Coordinate) * (64 :
          Coordinate)⁻¹ = (2 : Coordinate)⁻¹ by
          decide +kernel])
  have pieceBound : ∀ piece ∈ assigned.split.pieces,
      32 * accuracy.globalBound + 2 * AnalyticComparison.pieceCharge
        assigned
        (BankReadings.meshBudget assigned
          (FaceScalarBudgets.meshes points
          scalars)).bounds piece index ≤ Aggregate.perTerm tolerance fragments := by
    intro piece _
    have analytic := ScalarAccuracy.pieceCharge_accurate assigned
      (BankReadings.meshBudget assigned
        (FaceScalarBudgets.meshes points
        scalars)).bounds scalar.certificate piece index left right
    rw [scalar.certificate.perFragment_eq] at analytic
    exact ((Arithmetic.add_lt_add_direct ownership analytic).trans_eq (by
      rw [show Aggregate.perTerm tolerance fragments / 2 + Aggregate.perTerm tolerance
        fragments / 2 = (Aggregate.perTerm tolerance fragments / 2) * 2 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))).le
  rw [reading.bound_eq, reading.analyticCharge_eq]
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct _
    ((Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)).trans_eq (Aggregate.countCoordinate_eq
      _).symm)
  have paid := ScalarAccuracy.charges_le assigned.split.pieces _
    accuracy.globalBound (Aggregate.perTerm tolerance fragments) pieceBound
  rw [← assigned.split.count_eq] at paid
  exact paid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy
