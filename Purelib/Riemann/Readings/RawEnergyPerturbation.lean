module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Tactic.Ring
public import Purelib.Topology.Surface.Cut.PrimitiveJumps

public section

/-! Homogeneous perturbation of the raw period energy from entrywise matrix
errors. Every conjugate basis pair and both handle factors are retained. -/
namespace Purelib.Riemann.Readings.RawEnergyPerturbation

open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj normSq_mul)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_mul_left sumFin_mul_right)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair (conj_sub)
open Purelib.Integration.Energy.Polygon (energyBoundaryArea periodPairingEnergy_eq_boundaryArea_im_div_four)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (boundaryEnergy_sub_budget_le)
open _root_.Purelib.LinearAlgebra.Gaussian.Energy (GaussianVector)
open Purelib.LinearAlgebra.Gaussian.Energy (periodCombination unnormalizedEnergyForm)
open Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes (edgeArea_energy_combination)
open Purelib.Topology.Surface.Boundary.HandleAreaBounds.PrimitivePoint (area_difference_bound)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Algebra in
open Purelib.Data in
/-- The undoubled finite boundary pairing of two basis differentials. -/
@[expose] def rawPairArea {size : Nat} (a b : GaussianMatrix size) (first second : Fin size) : Gaussian.Basic.Canonical
  :=
  FiniteSum.Fin.sumFin fun cycle => edgeArea ⟨conj (a first cycle), a second cycle⟩ ⟨conj (b first cycle), b second
    cycle⟩

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Expand raw boundary energy into all conjugate coefficient-weighted basis pairings.

The exact finite identity retains every ordered differential pair and the factor of two in the energy boundary area. -/
theorem raw_boundary_combination {size : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector size) (a b :
  GaussianMatrix size) :
    Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients a)
      (Gaussian.Energy.periodCombination coefficients b) =
      2 * FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
        (coefficients first) * coefficients second * rawPairArea a b first second)) := by
  unfold Energy.Polygon.energyBoundaryArea
  unfold rawPairArea
  rw [← Periods.BilinearCombination.sumFin_combination, ← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [Polygon.Stokes.commutatorBoundaryArea_eq]
  change 2 * edgeArea _ _ = 2 * _
  apply congrArg (fun value : Gaussian.Basic.Canonical => 2 * value)
  unfold Gaussian.Energy.periodCombination
  rw [Matrix.Multiplication.vectorMatrix_apply,
    Matrix.Multiplication.vectorMatrix_apply]
  exact Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes.edgeArea_energy_combination coefficients (fun row =>
    a row cycle) (fun row => b row cycle)

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Data in
/-- Bound each basis pairing's perturbation from uniform squared entry errors.

For nonnegative magnitude and error with error at most one, the squared difference is at most the squared matrix size
times 32 times the incremented magnitude and error. -/
theorem rawPairArea_difference_bound {size : Nat} (a b changedA changedB : GaussianMatrix size)
    {magnitude error : Rat.Fraction.Rational} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small :
      error ≤ 1)
    (aBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (a row cycle) ≤ magnitude)
    (bBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (b row cycle) ≤ magnitude)
    (aError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedA row cycle - a row cycle) ≤ error)
    (bError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedB row cycle - b row cycle) ≤ error)
    (first second : Fin size) :
    Data.Gaussian.Norm.Basic.normSq (rawPairArea changedA changedB first second - rawPairArea a b first second) ≤
      (size : Rat.Fraction.Rational) ^ 2 * (32 * (magnitude + 1) * error) := by
  unfold rawPairArea
  rw [← FiniteSum.Fin.sumFin_sub]
  apply Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
  intro cycle
  apply Surface.Boundary.HandleAreaBounds.PrimitivePoint.area_difference_bound nonnegative errorNonnegative small
  · constructor
    · have scalar := (Gaussian.Norm.Basic.normSq_conj (a first cycle)).trans_le (aBound first cycle)
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
    · have scalar := aBound second cycle
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  · constructor
    · have scalar := (Gaussian.Norm.Basic.normSq_conj (b first cycle)).trans_le (bBound first cycle)
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
    · have scalar := bBound second cycle
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  · constructor
    · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj (changedA first cycle) -
        Data.Gaussian.Basic.conj (a first cycle)) ≤ error
      rw [← Surface.Sewing.SewnConjugateSamples.ConjugatePair.conj_sub, Gaussian.Norm.Basic.normSq_conj]
      exact aError first cycle
    · have scalar := aError second cycle
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical, Polygon.Stokes.PrimitivePoint.sub] using
        scalar
  · constructor
    · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj (changedB first cycle) -
        Data.Gaussian.Basic.conj (b first cycle)) ≤ error
      rw [← Surface.Sewing.SewnConjugateSamples.ConjugatePair.conj_sub, Gaussian.Norm.Basic.normSq_conj]
      exact bError first cycle
    · have scalar := bError second cycle
      simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical, Polygon.Stokes.PrimitivePoint.sub] using
        scalar

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the full raw boundary perturbation homogeneously in the coefficients.

Uniform squared entry error at most one gives the explicit weight 128 times the fourth power of matrix size and
incremented magnitude, multiplied by the squared coefficient norm squared. -/
theorem raw_boundary_difference_bound {size : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector size)
    (a b changedA changedB : GaussianMatrix size)
    {magnitude error : Rat.Fraction.Rational} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small :
      error ≤ 1)
    (aBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (a row cycle) ≤ magnitude)
    (bBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (b row cycle) ≤ magnitude)
    (aError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedA row cycle - a row cycle) ≤ error)
    (bError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedB row cycle - b row cycle) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq (Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination
      coefficients changedA) (Gaussian.Energy.periodCombination coefficients changedB) -
      Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients a)
        (Gaussian.Energy.periodCombination coefficients b)) ≤
      128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude + 1) * error * (FiniteSum.Fin.sumFin (fun row =>
        Data.Gaussian.Norm.Basic.normSq (coefficients row))) ^ 2 := by
  let errors := fun first second => rawPairArea changedA changedB first second - rawPairArea a b first second
  have estimate := Periods.BilinearCombination.combination_bound (fun row => Data.Gaussian.Basic.conj (coefficients
    row))
    (fun row => coefficients row) errors
    (rawPairArea_difference_bound a b changedA changedB nonnegative errorNonnegative small aBound bBound aError bError)
  rw [FiniteSum.Fin.sumFin_congr (fun row => Gaussian.Norm.Basic.normSq_conj (coefficients row))] at estimate
  have read : Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients changedA)
    (Gaussian.Energy.periodCombination coefficients changedB) -
      Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients a)
        (Gaussian.Energy.periodCombination coefficients b) =
      2 * FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
        (coefficients first) * coefficients second * errors first second)) := by
    rw [raw_boundary_combination, raw_boundary_combination, ← mul_sub]
    apply congrArg (fun value : Gaussian.Basic.Canonical => 2 * value)
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro first
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro second
    unfold errors
    ring1
  rw [read, Gaussian.Norm.Basic.normSq_mul, show Data.Gaussian.Norm.Basic.normSq (2 : Gaussian.Basic.Canonical) = 4
    by decide]
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct estimate (by
      decide : (0 : Rat.Fraction.Rational) ≤ 4)).trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Pay a homogeneous raw-energy loss from entrywise matrix error.

The nonnegative allowance must cover the weighted error by sixteen times its square; the resulting energy loss is
allowance times the coefficient squared norm. -/
theorem raw_energy_sub_allowance_le {size : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector size)
    (a b changedA changedB : GaussianMatrix size)
    {magnitude error allowance : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (allowanceNonnegative : 0 ≤ allowance)
    (paid : 128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude + 1) * error ≤ 16 * allowance ^ 2)
    (aBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (a row cycle) ≤ magnitude)
    (bBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (b row cycle) ≤ magnitude)
    (aError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedA row cycle - a row cycle) ≤ error)
    (bError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedB row cycle - b row cycle) ≤ error) :
    Gaussian.Energy.unnormalizedEnergyForm coefficients changedA changedB - allowance * FiniteSum.Fin.sumFin (fun row =>
      Data.Gaussian.Norm.Basic.normSq (coefficients row)) ≤
      Gaussian.Energy.unnormalizedEnergyForm coefficients a b := by
  let norm := FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq (coefficients row))
  have normNonnegative : 0 ≤ norm :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.IndexedBudget.sumFin_le (fun row => Gaussian.Norm.Basic.normSq_nonneg (coefficients
        row)))
  have squared := raw_boundary_difference_bound coefficients a b changedA changedB
    nonnegative errorNonnegative small aBound bBound aError bError
  have budget : 128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude + 1) * error * norm ^ 2 ≤ (4 * (allowance * norm))
    ^ 2 :=
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct norm)).trans_eq (by ring1)
  have comparison := boundaryEnergy_sub_budget_le
    (Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients changedA)
      (Gaussian.Energy.periodCombination coefficients changedB))
    (Energy.Polygon.energyBoundaryArea (Gaussian.Energy.periodCombination coefficients a)
      (Gaussian.Energy.periodCombination coefficients b))
    (allowance * norm) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct allowanceNonnegative normNonnegative)
      (squared.trans budget)
  unfold Gaussian.Energy.unnormalizedEnergyForm
  rw [Energy.Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four,
    Energy.Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four]
  exact comparison

open Purelib.Approximation in
open Purelib.Data in
/-- Select the entrywise squared-error target paying a raw-energy allowance.

Cap the weighted allowance at one; the definition also covers empty matrices and zero magnitude bounds. -/
@[expose] def rawEnergyMatrixTarget (size : Nat) (magnitude allowance : Rat.Fraction.Rational) : Rat.Fraction.Rational
  :=
  min 1 (Rational.Budget.Weighted.allowance (16 * allowance ^ 2) (128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude
    + 1)))

open Purelib.Data in
/-- The finite raw-energy matrix weight is nonnegative for a nonnegative magnitude. -/
private theorem rawEnergyMatrixWeight_nonnegative (size : Nat) {magnitude : Rat.Fraction.Rational} (nonnegative : 0 ≤
  magnitude) :
    0 ≤ 128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude + 1) :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Rat.Fraction.Order.Arithmetic.pow_nonneg_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le size)) 4))
      (add_nonneg nonnegative (by decide))

open Purelib.Approximation in
open Purelib.Data in
/-- A positive energy allowance gives a positive selected matrix target. -/
theorem rawEnergyMatrixTarget_positive (size : Nat) {magnitude allowance : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ magnitude) (positive : 0 < allowance) :
    0 < rawEnergyMatrixTarget size magnitude allowance :=
  Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide) (Rational.Budget.Weighted.allowance_positive
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) (Rat.Fraction.Order.Arithmetic.pow_pos_direct
      positive 2))
    (rawEnergyMatrixWeight_nonnegative size nonnegative))

open Purelib.Data in
/-- The selected matrix error target is at most one. -/
theorem rawEnergyMatrixTarget_small (size : Nat) (magnitude allowance : Rat.Fraction.Rational) :
    rawEnergyMatrixTarget size magnitude allowance ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _

open Purelib.Approximation in
open Purelib.Data in
/-- The selected matrix target pays the full weighted squared energy allowance. -/
theorem rawEnergyMatrixTarget_paid (size : Nat) {magnitude allowance : Rat.Fraction.Rational} (nonnegative : 0 ≤
  magnitude) :
    128 * (size : Rat.Fraction.Rational) ^ 4 * (magnitude + 1) * rawEnergyMatrixTarget size magnitude allowance ≤ 16 *
      allowance ^ 2 :=
  (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _
    _) (rawEnergyMatrixWeight_nonnegative size nonnegative)).trans
    (Rational.Budget.Weighted.mul_allowance_le (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct allowance))
      (rawEnergyMatrixWeight_nonnegative size nonnegative))

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- The selected entrywise tolerance pays the requested homogeneous energy allowance.

For a positive allowance and bounded original entries, the certified entry errors imply the raw-energy comparison
without a separate payment premise. -/
theorem raw_energy_sub_selected_allowance_le {size : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  size)
    (a b changedA changedB : GaussianMatrix size) {magnitude allowance : Rat.Fraction.Rational}
    (nonnegative : 0 ≤ magnitude) (positive : 0 < allowance)
    (aBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (a row cycle) ≤ magnitude)
    (bBound : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (b row cycle) ≤ magnitude)
    (aError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedA row cycle - a row cycle) ≤
      rawEnergyMatrixTarget size magnitude allowance)
    (bError : ∀ row cycle, Data.Gaussian.Norm.Basic.normSq (changedB row cycle - b row cycle) ≤
      rawEnergyMatrixTarget size magnitude allowance) :
    Gaussian.Energy.unnormalizedEnergyForm coefficients changedA changedB - allowance * FiniteSum.Fin.sumFin (fun row =>
      Data.Gaussian.Norm.Basic.normSq (coefficients row)) ≤
      Gaussian.Energy.unnormalizedEnergyForm coefficients a b :=
  raw_energy_sub_allowance_le coefficients a b changedA changedB nonnegative
    (rawEnergyMatrixTarget_positive size nonnegative positive).le (rawEnergyMatrixTarget_small size magnitude allowance)
    positive.le (rawEnergyMatrixTarget_paid size nonnegative) aBound bBound aError bError

end Purelib.Riemann.Readings.RawEnergyPerturbation
