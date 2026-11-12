module
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarAccuracy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank

section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Full fragment-count payment for original request sums

The preselected scalar allowance pays both Cauchy factors, including every
analytic piece inside every original grid fragment.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {domains :
    Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {count : Nat} {target : Fraction.Rational} {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational}
    {index pieces : Nat}
  {scalars : FaceScalarBudgets source pieces
    tolerance domains} {numerics : Face.PrimitiveData.FacePrimitiveBank source index
    domains}
  {shared : Face.CommonMeshes.FaceSharedMeshes
    (FaceScalarBudgets.meshes points scalars)
    numerics}

/-- Increasing a finite count preserves the order of its squared multiple of a nonnegative rational allowance. -/
private theorem square_count_mono {first last : Nat} (bound : first ≤ last) {allowance : Fraction.Rational}
    (nonnegative : 0 ≤ allowance) :
    Aggregate.countCoordinate first * (Aggregate.countCoordinate first * allowance) ≤
      Aggregate.countCoordinate last * (Aggregate.countCoordinate last * allowance) :=
      by
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.mul_le_mul bound bound)) nonnegative
  simpa only [Aggregate.countCoordinate_eq, Algebra.NatCast.mul, mul_assoc] using estimate

namespace RegularPrimitiveFragments.SheetEntries.BankReadings

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming FragmentSheets -> SheetEntries

variable {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source} {partition :
  Rectangle.AxisPartition 0 1 (axes.parameters parent)}
  {request : Readings.UniformPreparedRequests.LocalRequest parent count target}
  {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval} {fragments :
    RegularFaces.RegularPrimitiveFragments axes parent partition intervals}
  {entries : FragmentSheets domains
    request fragments}

/-- The original fragment charge sum is bounded by its actual interval count and the retained squared analytic-piece
allowance. -/
theorem chargeSum_scalar_le (readings :
  BankReadings shared
  entries) (positive : 0 < tolerance)
    (leftLater : FaceScalarBudgets.index scalars ≤
      index)
    (rightLater : FaceScalarBudgets.index scalars ≤
      request.request.index) :
    readings.chargeSum ≤ Aggregate.countCoordinate intervals.length *
      (Aggregate.countCoordinate (2 *
        FaceDomainBank.stepsBound domains + 5) *
        (Aggregate.countCoordinate (2 *
          FaceDomainBank.stepsBound domains + 5) *
          Aggregate.perTerm tolerance pieces)) := by
  induction readings with
  | nil =>
    change (0 : Fraction.Rational) ≤ Aggregate.countCoordinate 0 * _; rw
      [Aggregate.countCoordinate_eq, Nat.cast_zero, Fraction.Field.zero_mul_direct]
  | @cons interval intervals head tail entry entries first rest ih =>
      have localBound := (ScalarAccuracy.BankReading.bound_le
        entry scalars first leftLater rightLater).trans
        (SharedSums.square_count_mono
          (ScalarAccuracy.split_count_le entry)
          (Aggregate.perTerm_positive positive pieces).le)
      exact (add_le_add localBound ih).trans_eq (by
        simp only [List.length_cons, Aggregate.countCoordinate_eq, Algebra.NatCast.add, Nat.cast_one]
        ring1)

end RegularPrimitiveFragments.SheetEntries.BankReadings

namespace RegularPrimitiveSplits.SheetEntries

open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)} {splits :
  PreparedPrimitiveSplits.PrimitiveSplits axes parents}
  {fragments : RegularFaces.RegularPrimitiveSplits (base := base) axes
    splits} {requests : Readings.UniformPreparedRequests.RequestedParents count target parents}
  {entries : SheetEntries domains fragments requests}

/-- The complete original split-parent charge sum is bounded by its actual fragment count and retained analytic-piece
allowance. -/
theorem BankReadings.chargeSum_scalar_le (readings :
  BankReadings shared
  entries) (positive : 0 < tolerance)
    (leftLater : FaceScalarBudgets.index scalars ≤
      index)
    (rightLater : Readings.PreparedControlledPrimitiveRequests.IndicesAbove
      (FaceScalarBudgets.index scalars) requests) :
    readings.chargeSum ≤ Aggregate.countCoordinate splits.count *
      (Aggregate.countCoordinate (2 *
        FaceDomainBank.stepsBound domains + 5) *
        (Aggregate.countCoordinate (2 *
          FaceDomainBank.stepsBound domains + 5) *
          Aggregate.perTerm tolerance pieces)) := by
  induction readings with
  | nil =>
    change (0 : Fraction.Rational) ≤ Aggregate.countCoordinate 0 * _; rw
      [Aggregate.countCoordinate_eq, Nat.cast_zero, Fraction.Field.zero_mul_direct]
  | cons first rest ih =>
      have bound := add_le_add (first.chargeSum_scalar_le positive leftLater rightLater.1) (ih rightLater.2)
      exact bound.trans_eq (by
        simp only [PreparedPrimitiveSplits.PrimitiveSplits.count,
          Geometry.Rectangle.AxisPartition.count_eq, Aggregate.countCoordinate_eq,
          Algebra.NatCast.add]
        ring1)

/-- The retained complete-sum allowance is strictly below the target when the actual fragment and analytic-piece counts
fit the prepaid bound. -/
theorem SharedSum.bound_lt (summary :
  SharedSum shared entries)
  (positive : 0 < tolerance)
    (leftLater : FaceScalarBudgets.index scalars ≤
      index)
    (rightLater : Readings.PreparedControlledPrimitiveRequests.IndicesAbove
      (FaceScalarBudgets.index scalars) requests)
    (countBound : splits.count * (2 *
      FaceDomainBank.stepsBound domains + 5) ≤
      pieces) : summary.bound < tolerance := by
  rw [summary.bound_eq, summary.fragmentCount_eq, summary.chargeSum_eq]
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (summary.readings.chargeSum_scalar_le positive leftLater rightLater)
    ((Fraction.Cast.Order.natCast_le_direct (Nat.zero_le splits.count)).trans_eq
      (Aggregate.countCoordinate_eq _).symm)
  have regroup : Aggregate.countCoordinate splits.count * (Aggregate.countCoordinate
    splits.count *
      (Aggregate.countCoordinate (2 *
        FaceDomainBank.stepsBound domains + 5) *
        (Aggregate.countCoordinate (2 *
        FaceDomainBank.stepsBound domains + 5) *
        Aggregate.perTerm tolerance pieces))) =
      Aggregate.countCoordinate (splits.count * (2 *
        FaceDomainBank.stepsBound domains + 5)) *
        (Aggregate.countCoordinate (splits.count * (2 *
          FaceDomainBank.stepsBound domains + 5)) *
          Aggregate.perTerm tolerance pieces) := by
    simp only [Aggregate.countCoordinate_eq, Algebra.NatCast.mul]
    ring1
  exact (estimate.trans_eq regroup).trans_lt
    ((SharedSums.square_count_mono countBound
      (Aggregate.perTerm_positive positive pieces).le).trans_lt (by
      rw [Aggregate.countCoordinate_eq]
      exact Aggregate.count_mul_perTerm_lt positive pieces))

end RegularPrimitiveSplits.SheetEntries
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums

end
