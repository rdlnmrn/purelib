module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Gaussian.Energy

public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Quantitative A-period separation from homogeneous raw coercivity and a finite B-action bound. -/
namespace Purelib.Riemann.Integration.RawActionLower

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_mul_left)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.LinearAlgebra.Gaussian.Energy (GaussianVector)
open Purelib.LinearAlgebra.Gaussian.Energy (GaussianMatrix periodPairingEnergy periodCombination unnormalizedEnergyForm)

open Purelib.Data in
/-- Bound a weighted Gaussian alternating product by the two weighted squared norms. -/
private theorem cross_bound (a b : Gaussian.Basic.Canonical) (first last : Rat.Fraction.Rational) :
    2 * first * last * ((b * conj a - a * conj b).im / 2) ≤ first ^ 2 * Gaussian.Basic.Canonical.normSq a + last ^ 2 *
      Gaussian.Basic.Canonical.normSq b := by
  have half : (b * conj a - a * conj b).im / 2 = a.re * b.im - a.im * b.re := by
    apply Rat.Fraction.Field.mul_right_cancel_of_ne (show (2 : Rat.Fraction.Rational) ≠ 0 by decide)
    rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    change b.re * (-a.im) + b.im * a.re - (a.re * (-b.im) + a.im * b.re) = _
    ring1
  rw [half]
  have nonnegative := add_nonneg (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (first * a.re - last * b.im))
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (first * a.im + last * b.re))
  apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  apply Eq.mp (congrArg (fun value : Rat.Fraction.Rational => 0 ≤ value) ?_) nonnegative
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical a,
    ← Gaussian.Norm.Basic.normSq_eq_canonical b]
  change _ = first ^ 2 * (a.re ^ 2 + a.im ^ 2) + last ^ 2 * (b.re ^ 2 + b.im ^ 2) - _
  ring1

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the finite period-pairing energy by weighted squared vector norms.

The rational weights are arbitrary; the inequality sums the scalar Gaussian square bounds over the common finite index
set. -/
theorem pairing_young_bound {size : Nat} (a b : LinearAlgebra.Gaussian.Energy.GaussianVector size) (first last :
  Rat.Fraction.Rational) :
    2 * first * last * Gaussian.Energy.periodPairingEnergy a b ≤ first ^ 2 * coefficientNormSq a + last ^ 2 *
      coefficientNormSq b := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun index => cross_bound (a index) (b index) first
    last)
  rw [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_left,
    FiniteSum.Fin.sumFin_mul_left] at bound
  apply (Eq.le ?_).trans bound
  unfold Gaussian.Energy.periodPairingEnergy
  have distributed : FiniteSum.Fin.sumFin (fun index => (b index * conj (a index) - a index * conj (b index)).im / 2) =
      FiniteSum.Fin.sumFin (fun index => (b index * conj (a index) - a index * conj (b index)).im) / 2 := by
    apply (FiniteSum.Fin.sumFin_congr (fun index => Rat.Fraction.Field.div_eq_mul_inv_direct _ _)).trans
    exact (FiniteSum.Fin.sumFin_mul_right _ _).trans (Rat.Fraction.Field.div_eq_mul_inv_direct _ _).symm
  rw [distributed]
  apply congrArg (fun value : Rat.Fraction.Rational => 2 * first * last * (value / 2))
  exact FiniteSum.Fin.sumFin_congr (fun index => rfl)

open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Derive an A-action lower bound from coercive pairing and bounded B-action.

For positive coercivity and B-action constants, the A-action squared norm is at least their squared-coercivity-to-bound
ratio times the coefficient norm. -/
theorem a_action_lower {size : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector size) (a b :
  Gaussian.Energy.GaussianMatrix size)
    (lower bound : Rat.Fraction.Rational) (lowerPositive : 0 < lower) (boundPositive : 0 < bound)
    (coercive : lower * coefficientNormSq coefficients ≤ Gaussian.Energy.unnormalizedEnergyForm coefficients a b)
    (bounded : coefficientNormSq (Gaussian.Energy.periodCombination coefficients b) ≤ bound * coefficientNormSq
      coefficients) :
    lower ^ 2 / bound * coefficientNormSq coefficients ≤ coefficientNormSq (Gaussian.Energy.periodCombination
      coefficients a) := by
  have multiplied : 2 * bound * lower * (lower * coefficientNormSq coefficients) ≤
      2 * bound * lower * Gaussian.Energy.unnormalizedEnergyForm coefficients a b :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coercive
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        boundPositive.le) lowerPositive.le)
  have right : bound ^ 2 * coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) +
      lower ^ 2 * coefficientNormSq (Gaussian.Energy.periodCombination coefficients b) ≤
        bound ^ 2 * coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) +
          lower ^ 2 * (bound * coefficientNormSq coefficients) :=
    Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl _)
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct lower))
  have comparison : 2 * bound * lower * (lower * coefficientNormSq coefficients) ≤
      bound ^ 2 * coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) +
        lower ^ 2 * (bound * coefficientNormSq coefficients) :=
    multiplied.trans ((pairing_young_bound (Gaussian.Energy.periodCombination coefficients a)
      (Gaussian.Energy.periodCombination coefficients b) bound lower).trans right)
  have cancelled : lower ^ 2 * coefficientNormSq coefficients ≤
      coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) * bound := by
    apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := bound) _ boundPositive
    apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    have difference := Rat.Fraction.Order.Arithmetic.sub_nonneg_direct comparison
    have identity : bound ^ 2 * coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) +
        lower ^ 2 * (bound * coefficientNormSq coefficients) -
          2 * bound * lower * (lower * coefficientNormSq coefficients) =
        (coefficientNormSq (Gaussian.Energy.periodCombination coefficients a) * bound) * bound -
          (lower ^ 2 * coefficientNormSq coefficients) * bound := by ring1
    rw [identity] at difference
    exact difference
  apply Rat.Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := bound) _ boundPositive
  calc
    _ = (lower ^ 2 / bound * bound) * coefficientNormSq coefficients := by ring1
    _ = lower ^ 2 * coefficientNormSq coefficients := by
      rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ boundPositive.ne']
    _ ≤ _ := cancelled

end Purelib.Riemann.Integration.RawActionLower
