module
import Purelib.Data.Nat.Multiplication
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.WindowSize
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid.WindowSize

public section

/-! Pay the complete retained boundary count before choosing any Newton grid. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget

open Purelib.Data
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest outerCount)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfaceRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

namespace NewtonPreparation.AreaRequest

/-- The actual selected Newton grid's regular-face count is bounded by the square of the original pre-grid outer count.
-/
theorem regulars_count (request : AreaRequest preparation target radius) :
    request.grid.faces.regulars.length ≤ (NewtonPreparation.outerCount preparation) ^ 2 := by
  have classified := request.grid.faces.length_eq
  have cells := Polynomial.Geometry.Grid.WindowSize.cells_length_le request.grid.shrunk.prepared.grid
  have lines : request.lineCount ≤ request.count := by have cap := request.lineCount_le; omega
  have cap : request.lineCount ^ 2 ≤ request.count ^ 2 := by
    rw [Nat.Multiplication.pow_two, Nat.Multiplication.pow_two]
    exact Nat.mul_le_mul lines lines
  rw [← request.lineCount_eq] at cells
  rw [request.count_eq] at cap
  exact (Nat.le_add_right _ _).trans (classified.le.trans (cells.trans cap))

end NewtonPreparation.AreaRequest

namespace ProtectedObservations.SynchronizedSurfaceRequests
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface (ConjugateRequest)

/-- Its count argument is fixed from the original grid, before band selection. -/
@[expose] def remainingBoundaryTarget (genus count : Nat) (allowance : Rational) : Rational :=
  ConjugateRequest.energyAllowanceTarget genus allowance /
    (256 * ((Aggregate.countCoordinate count) ^ 8 + 1))

/-- The eighth power of a rational count is nonnegative. -/
private theorem eighth_nonnegative (count : Rational) : 0 ≤ count ^ 8 :=
  (Arithmetic.sq_nonneg_direct (count ^ 4)).trans_eq (by ring1)

/-- The fixed boundary-count allowance denominator is strictly positive. -/
private theorem denominator_positive (count : Nat) : 0 < (256 : Rational) * ((count : Rational) ^ 8 +
  1) :=
  Arithmetic.mul_pos_direct (by decide +kernel)
    (Arithmetic.add_pos_of_nonneg_of_pos_direct
    (eighth_nonnegative
    _) (by decide +kernel))

/-- A positive original energy allowance gives a positive retained boundary target. -/
theorem remainingBoundaryTarget_positive {genus count : Nat} {allowance : Rational} (positive : 0 < allowance)
  :
    0 <
      remainingBoundaryTarget
      genus count allowance := by
  unfold
    remainingBoundaryTarget
  rw [Aggregate.countCoordinate_eq]
  exact Field.div_pos_direct (ConjugateRequest.energyAllowanceTarget_positive positive)
    (denominator_positive
    count)

/-- Nonnegative regular and hole counts bounded by the original squared count have their fourth and mixed count factors
bounded by twice its eighth power. -/
private theorem count_factor {regulars holes count : Rational}
    (regularsNonnegative : 0 ≤ regulars) (holesNonnegative : 0 ≤ holes)
    (regularsLe : regulars ≤ count ^ 2) (holesLe : holes ≤ count ^ 2) :
    regulars ^ 4 + holes ^ 2 * regulars ^ 2 ≤ 2 * count ^ 8 := by
  have regularSquares : regulars ^ 2 ≤ count ^ 4 :=
    (Arithmetic.pow_le_pow_direct regularsNonnegative regularsLe 2).trans_eq (by ring1)
  have holeSquares : holes ^ 2 ≤ count ^ 4 :=
    (Arithmetic.pow_le_pow_direct holesNonnegative holesLe 2).trans_eq (by ring1)
  have fourthNonnegative : 0 ≤ count ^ 4 := (Arithmetic.sq_nonneg_direct (count ^ 2)).trans_eq (by ring1)
  have fourth : regulars ^ 4 ≤ count ^ 8 := by
    have bound := Arithmetic.mul_le_mul_direct regularSquares regularSquares
      (Arithmetic.sq_nonneg_direct regulars) fourthNonnegative
    exact (show regulars ^ 4 = regulars ^ 2 * regulars ^ 2 by ring1).trans_le (bound.trans_eq (by ring1))
  have mixed : holes ^ 2 * regulars ^ 2 ≤ count ^ 8 :=
    (Arithmetic.mul_le_mul_direct holeSquares regularSquares (Arithmetic.sq_nonneg_direct
      regulars) fourthNonnegative).trans_eq (by ring1)
  exact (Arithmetic.add_le_add_direct fourth mixed).trans_eq (by ring1)

/-- All counting factors and the coefficient norm are paid uniformly. -/
theorem remainingBoundaryTarget_paid {genus count regulars holes : Nat} {allowance component : Rational}
    (positive : 0 < allowance) (componentNonnegative : 0 ≤ component)
    (componentLe : component ≤
      remainingBoundaryTarget
      genus count allowance)
    (regularsLe : regulars ≤ count ^ 2) (holesLe : holes ≤ count ^ 2) (coefficientNorm : Rational) :
    128 * ((regulars : Rational) ^ 4 + (holes : Rational) ^ 2 * (regulars : Rational) ^ 2) *
      ((genus : Rational) ^ 2 * coefficientNorm ^ 2 * component) ≤ (4 * (allowance * coefficientNorm)) ^ 2 :=
        by
  have regularCap : (regulars : Rational) ≤ (count : Rational) ^ 2 := by
    have cap := Fraction.Cast.Order.natCast_le_direct regularsLe
    rewrite [Algebra.NatCast.pow] at cap
    exact cap
  have holeCap : (holes : Rational) ≤ (count : Rational) ^ 2 := by
    have cap := Fraction.Cast.Order.natCast_le_direct holesLe
    rewrite [Algebra.NatCast.pow] at cap
    exact cap
  have factor :=
    count_factor
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le regulars))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le holes)) regularCap holeCap
  have product : (256 * ((count : Rational) ^ 8 + 1)) *
    remainingBoundaryTarget
    genus count allowance =
      ConjugateRequest.energyAllowanceTarget genus allowance := by
    unfold
      remainingBoundaryTarget
    rw [Aggregate.countCoordinate_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _
      (denominator_positive
      count).ne'
  have scalar : 128 * ((regulars : Rational) ^ 4 + (holes : Rational) ^ 2 * (regulars :
    Rational) ^ 2) * component ≤
      ConjugateRequest.energyAllowanceTarget genus allowance := by
    have enlarged : 128 * ((regulars : Rational) ^ 4 + (holes : Rational) ^ 2 * (regulars :
      Rational) ^ 2) ≤
        256 * ((count : Rational) ^ 8 + 1) :=
      (Arithmetic.mul_le_mul_of_nonneg_left_direct factor (by
          decide +kernel : (0 : Rational) ≤ 128)).trans
        (by have h : (256 : Rational) * (count : Rational) ^ 8 ≤ 256 * ((count : Rational) ^
          8 + 1) := Arithmetic.mul_le_mul_of_nonneg_left_direct (le_add_of_nonneg_right
            (by decide +kernel : (0 : Rational) ≤ 1))
              (by decide +kernel : (0 : Rational) ≤ 256)
            exact (show 128 * (2 * (count : Rational) ^ 8) = 256 * (count : Rational) ^ 8 by
              ring1).trans_le h)
    exact (Arithmetic.mul_le_mul_direct enlarged componentLe componentNonnegative
      (denominator_positive
      count).le).trans_eq product
  calc
    _ = ((genus : Rational) ^ 2 *
        (128 * ((regulars : Rational) ^ 4 + (holes : Rational) ^ 2 * (regulars : Rational) ^
          2) * component)) * coefficientNorm ^ 2 := by ring1
    _ ≤ ((genus : Rational) ^ 2 * ConjugateRequest.energyAllowanceTarget genus allowance) * coefficientNorm ^ 2
      :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct scalar (Arithmetic.sq_nonneg_direct
        _)) (Arithmetic.sq_nonneg_direct _)
    _ ≤ (4 * allowance) ^ 2 * coefficientNorm ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (ConjugateRequest.energyAllowanceTarget_paid positive)
        (Arithmetic.sq_nonneg_direct _)
    _ = _ := by ring1

end ProtectedObservations.SynchronizedSurfaceRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.BoundaryBudget
