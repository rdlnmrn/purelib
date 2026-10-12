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

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {source :
    Hyperelliptic.Differentials.Basic.Differential genus}
  {axes : Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)} {interval :
    Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes parent partition
    interval}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {count : Nat} {target : Normalization.InverseRootPolynomial.Coordinate} {request :
    Readings.UniformPreparedRequests.LocalRequest parent count target}
  {fragments : Nat} {tolerance : Normalization.InverseRootPolynomial.Coordinate}

/-- Read the original fragment's scalar budget through its retained face, sheet and domain equalities. -/
@[expose] def scalarBudget (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      tolerance domains) : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget
      assigned.domain source fragments tolerance :=
  (((Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.get budgets
    fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain assigned.domain_eq.symm

/-- The original fragment mesh budget is exactly the mesh constructed from its retained scalar budget. -/
theorem meshBudget_scalar (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      tolerance domains) (points : List Normalization.InverseRootPolynomial.Gaussian) :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshBudget assigned
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points budgets) =
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget assigned budgets).meshBudget points := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshBudget
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget
  rw [Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes_get, ←
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget.castFace_meshes,
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget.meshes_atSheet,
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget.castDomain_meshBudget]
  rfl

/-- The original fragment's minimum comparison stage is below the retained common face-budget stage. -/
theorem scalarBudget_minimum_le (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      tolerance domains) :
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget assigned budgets).certificate.minimumIndex
      ≤ Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index budgets := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget
  rw [Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.DomainScalarBudget.castDomain_minimumIndex]
  exact ((Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget.atSheet _
    _).certificate.grid_ge.trans
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget.atSheet_le _ _)).trans
    ((Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudget.castFace_index _ _).trans_le
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.get_le budgets _))

/-- Every original inverse model's residual at a later index is below the common one-sixteenth geometric residual. -/
private theorem uniform_residual {polynomial : Normalization.InverseRootPolynomial.Polynomial} {box :
  Normalization.InverseRootPolynomial.Box} (model : Normalization.InverseRootPolynomial.Model polynomial box)
    {minimum index : Nat} (later : minimum ≤ index) :
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius model.bound index ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius (1 / 16) minimum :=
  (quarterRadius_antitone model.bound_nonnegative later).trans (by
    simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) minimum))

/-- Both sufficiently late original polynomial readings make twice the analytic piece charge smaller than half its
retained fragment allowance. -/
theorem pieceCharge_accurate (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings.FragmentBounds assigned.domain.patch source)
    {globalBounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds fragment.face.located.face.clearance
      (Readings.PreparedPrimitiveSamples.differentialNumerator source)}
    (budget : Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy globalBounds assigned.domain.steps fragments
      tolerance)
    (piece : Paths.RectangularSegmentSplitting.SegmentPiece assigned.domain.geometry fragment.located.first
      fragment.located.last) (index : Nat)
    (leftLater : budget.minimumIndex ≤ index) (rightLater : budget.minimumIndex ≤ request.request.index) :
    2 * Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.pieceCharge assigned bounds piece index <
      budget.perFragment / 2 := open Purelib.Data in by
  let residual := Rational.Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex
  have residualNonnegative : 0 ≤ residual := Rational.Geometric.Basic.quarterRadius_nonneg (by decide +kernel) _
  have left := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.uniform_residual
    (assigned.domain.patch.transported.cell piece.column piece.row).model
    (leftLater.trans (Nat.le_add_right _ 2))
  have right := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.uniform_residual
    request.neighborhood.base.model rightLater
  have productNonnegative : 0 ≤ bounds.numerator piece.column piece.row * bounds.inverse :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell piece.column piece.row).numeratorUpper_nonnegative
      (bounds.atCell piece.column piece.row).inverseUpper_positive.le
  have globalNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    globalBounds.numeratorUpper_nonnegative globalBounds.inverseUpper_positive.le
  have movement := Rational.Box.normSq_sub_le_diagonalSq
    ((assigned.domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
    ((assigned.domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
  have weightBound := Fraction.Order.Arithmetic.mul_le_mul_direct (bounds.product_le globalBounds piece.column
    piece.row)
    movement (Gaussian.Norm.Basic.normSq_nonneg _) globalNonnegative
  have factorBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add left right)
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 12)
  have bound := Fraction.Order.Arithmetic.mul_le_mul_direct factorBound weightBound
    (Fraction.Order.Arithmetic.mul_nonneg_direct productNonnegative (Gaussian.Norm.Basic.normSq_nonneg _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg residualNonnegative residualNonnegative))
  have charged : Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.pieceCharge assigned bounds piece index
    ≤
      24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
        fragment.face.located.face.cell.box.diagonalSq := by
    exact (by unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.pieceCharge; ring1 :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.pieceCharge assigned bounds piece index =
      _).trans_le
      (bound.trans_eq (by change 12 * (residual + residual) * _ = _; ring1))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct charged (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_lt
    ((by ring1 : 2 * (24 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
      fragment.face.located.face.cell.box.diagonalSq) =
      48 * residual * (globalBounds.numeratorUpper * globalBounds.inverseUpper) *
        fragment.face.located.face.cell.box.diagonalSq).trans_lt budget.analytic_accurate)

/-- Transporting the retained face owner preserves the original selected domain step count. -/
private theorem castFace_steps {first last : Meshes.PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
    (equal : first = last) (cached : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains frames first)
      (sheet : Fin 2) :
    ((cached.castFace equal).domain sheet).steps = (cached.domain sheet).steps := by
  cases equal
  rfl

/-- The original fragment's selected domain steps are bounded by the retained whole-bank maximum. -/
theorem domain_steps_le (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
  : assigned.domain.steps ≤
  (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains) := by
  rw [assigned.domain_eq]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.domainCache
  rw [Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.castFace_steps]
  exact Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.get_steps_le domains _ _

/-- The original fragment split count is at most twice the retained maximum domain steps plus five. -/
theorem split_count_le (assigned :
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
  : assigned.split.count ≤ 2 *
  (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains) + 5 := by
  have bound := assigned.split.count_le
  have domainBound := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.domain_steps_le assigned
  omega

open Purelib.Algebra.FiniteSum.Rational in
/-- Bound a finite charge sum by its count-paid allowance.

The fixed ownership and analytic factors charge each original occurrence.
Structural summation preserves those factors and the supplied per-entry allowance. -/
private theorem charges_le {α : Type} (items : List α) (charges : α → Normalization.InverseRootPolynomial.Coordinate)
  (ownership allowance : Normalization.InverseRootPolynomial.Coordinate)
    (bounded : ∀ item ∈ items, 32 * ownership + 2 * charges item ≤ allowance) :
    32 * Rational.Budget.Aggregate.countCoordinate items.length * ownership +
      2 * Purelib.Algebra.FiniteSum.Rational.Squares.coordinateSum (items.map charges) ≤
        Rational.Budget.Aggregate.countCoordinate items.length * allowance := by
  simp only [Rational.Budget.Aggregate.countCoordinate_eq]
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
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    (scalars : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets source fragments
      tolerance domains) {points : List Normalization.InverseRootPolynomial.Gaussian} {index : Nat}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points scalars)
      numerics}
    (reading : Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.BankReading assigned shared)
    (leftLater : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index scalars ≤
      index)
    (rightLater : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index scalars ≤
      request.request.index) :
    reading.bound ≤ Rational.Budget.Aggregate.countCoordinate assigned.split.count *
      (Rational.Budget.Aggregate.countCoordinate assigned.split.count * Rational.Budget.Aggregate.perTerm tolerance
        fragments) := by
  let scalar := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget assigned scalars
  let accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshBudget assigned
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points
        scalars)).accuracy index
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshReadings assigned shared).later
  have left := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget_minimum_le assigned
    scalars).trans leftLater
  have right := (Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.scalarBudget_minimum_le assigned
    scalars).trans rightLater
  have ownership : 32 * accuracy.globalBound < Rational.Budget.Aggregate.perTerm tolerance fragments / 2 := by
    have estimate := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 32) accuracy.accurate
    exact estimate.trans_eq (by
      change 32 * (Rational.Budget.Aggregate.perTerm tolerance fragments / 64) = Rational.Budget.Aggregate.perTerm
        tolerance fragments / 2
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = Rational.Budget.Aggregate.perTerm tolerance fragments * (32 * (64 :
          Normalization.InverseRootPolynomial.Coordinate)⁻¹) := by
          ring1
        _ = _ := by rw [show (32 : Normalization.InverseRootPolynomial.Coordinate) * (64 :
          Normalization.InverseRootPolynomial.Coordinate)⁻¹ = (2 : Normalization.InverseRootPolynomial.Coordinate)⁻¹ by
          decide +kernel])
  have pieceBound : ∀ piece ∈ assigned.split.pieces,
      32 * accuracy.globalBound + 2 * Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.pieceCharge
        assigned
        (Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshBudget assigned
          (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points
          scalars)).bounds piece index ≤ Rational.Budget.Aggregate.perTerm tolerance fragments := by
    intro piece _
    have analytic := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.pieceCharge_accurate assigned
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.meshBudget assigned
        (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes points
        scalars)).bounds scalar.certificate piece index left right
    rw [scalar.certificate.perFragment_eq] at analytic
    exact ((Fraction.Order.Arithmetic.add_lt_add_direct ownership analytic).trans_eq (by
      rw [show Rational.Budget.Aggregate.perTerm tolerance fragments / 2 + Rational.Budget.Aggregate.perTerm tolerance
        fragments / 2 = (Rational.Budget.Aggregate.perTerm tolerance fragments / 2) * 2 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))).le
  rw [reading.bound_eq, reading.analyticCharge_eq]
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
    ((Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)).trans_eq (Rational.Budget.Aggregate.countCoordinate_eq
      _).symm)
  have paid := Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy.charges_le assigned.split.pieces _
    accuracy.globalBound (Rational.Budget.Aggregate.perTerm tolerance fragments) pieceBound
  rw [← assigned.split.count_eq] at paid
  exact paid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy
