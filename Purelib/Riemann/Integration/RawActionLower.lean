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

open Purelib.Data.Rat.Fraction.Order

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
    2 * first * last * ((b * conj a - a * conj b).im / 2) ≤ first ^ 2 * normSq a + last ^ 2 *
      normSq b := by
  have half : (b * conj a - a * conj b).im / 2 = a.re * b.im - a.im * b.re := by
    apply Rat.Fraction.Field.mul_right_cancel_of_ne (show (2 : Rat.Fraction.Rational) ≠ 0 by decide)
    rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    change b.re * (-a.im) + b.im * a.re - (a.re * (-b.im) + a.im * b.re) = _
    ring1
  rw [half]
  have nonnegative := add_nonneg (Arithmetic.sq_nonneg_direct (first * a.re - last * b.im))
    (Arithmetic.sq_nonneg_direct (first * a.im + last * b.re))
  apply Arithmetic.le_of_sub_nonneg_direct
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
theorem pairing_young_bound {size : Nat} (a b : GaussianVector size) (first last :
  Rat.Fraction.Rational) :
    2 * first * last * periodPairingEnergy a b ≤ first ^ 2 * coefficientNormSq a + last ^ 2 *
      coefficientNormSq b := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun index => cross_bound (a index) (b index) first
    last)
  rw [sumFin_mul_left, sumFin_add, sumFin_mul_left,
    sumFin_mul_left] at bound
  apply (Eq.le ?_).trans bound
  unfold periodPairingEnergy
  have distributed : sumFin (fun index => (b index * conj (a index) - a index * conj (b index)).im / 2) =
      sumFin (fun index => (b index * conj (a index) - a index * conj (b index)).im) / 2 := by
    apply (sumFin_congr (fun index => Rat.Fraction.Field.div_eq_mul_inv_direct _ _)).trans
    exact (FiniteSum.Fin.sumFin_mul_right _ _).trans (Rat.Fraction.Field.div_eq_mul_inv_direct _ _).symm
  rw [distributed]
  apply congrArg (fun value : Rat.Fraction.Rational => 2 * first * last * (value / 2))
  exact sumFin_congr (fun index => rfl)

open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Derive an A-action lower bound from coercive pairing and bounded B-action.

For positive coercivity and B-action constants, the A-action squared norm is at least their squared-coercivity-to-bound
ratio times the coefficient norm. -/
theorem a_action_lower {size : Nat} (coefficients : GaussianVector size) (a b :
  GaussianMatrix size)
    (lower bound : Rat.Fraction.Rational) (lowerPositive : 0 < lower) (boundPositive : 0 < bound)
    (coercive : lower * coefficientNormSq coefficients ≤ unnormalizedEnergyForm coefficients a b)
    (bounded : coefficientNormSq (periodCombination coefficients b) ≤ bound * coefficientNormSq
      coefficients) :
    lower ^ 2 / bound * coefficientNormSq coefficients ≤ coefficientNormSq (periodCombination
      coefficients a) := by
  have multiplied : 2 * bound * lower * (lower * coefficientNormSq coefficients) ≤
      2 * bound * lower * unnormalizedEnergyForm coefficients a b :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct coercive
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
        boundPositive.le) lowerPositive.le)
  have right : bound ^ 2 * coefficientNormSq (periodCombination coefficients a) +
      lower ^ 2 * coefficientNormSq (periodCombination coefficients b) ≤
        bound ^ 2 * coefficientNormSq (periodCombination coefficients a) +
          lower ^ 2 * (bound * coefficientNormSq coefficients) :=
    Arithmetic.add_le_add_direct (le_refl _)
      (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
      (Arithmetic.sq_nonneg_direct lower))
  have comparison : 2 * bound * lower * (lower * coefficientNormSq coefficients) ≤
      bound ^ 2 * coefficientNormSq (periodCombination coefficients a) +
        lower ^ 2 * (bound * coefficientNormSq coefficients) :=
    multiplied.trans ((pairing_young_bound (periodCombination coefficients a)
      (periodCombination coefficients b) bound lower).trans right)
  have cancelled : lower ^ 2 * coefficientNormSq coefficients ≤
      coefficientNormSq (periodCombination coefficients a) * bound := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := bound) _ boundPositive
    apply Arithmetic.le_of_sub_nonneg_direct
    have difference := Arithmetic.sub_nonneg_direct comparison
    have identity : bound ^ 2 * coefficientNormSq (periodCombination coefficients a) +
        lower ^ 2 * (bound * coefficientNormSq coefficients) -
          2 * bound * lower * (lower * coefficientNormSq coefficients) =
        (coefficientNormSq (periodCombination coefficients a) * bound) * bound -
          (lower ^ 2 * coefficientNormSq coefficients) * bound := by ring1
    rw [identity] at difference
    exact difference
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := bound) _ boundPositive
  calc
    _ = (lower ^ 2 / bound * bound) * coefficientNormSq coefficients := by ring1
    _ = lower ^ 2 * coefficientNormSq coefficients := by
      rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ boundPositive.ne']
    _ ≤ _ := cancelled

end Purelib.Riemann.Integration.RawActionLower
