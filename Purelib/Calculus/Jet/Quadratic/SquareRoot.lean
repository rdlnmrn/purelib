module

public import Purelib.Calculus.Jet.Quadratic.Composition
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Finite Taylor certificates for an affine radicand

Two displayed square-root readings retain their own square residuals.
Factoring the square difference at their displayed nonzero sum derives root
movement and an explicit quadratic remainder factor; composing
with a reciprocal certificate gives the inverse-root coefficient. These are
finite rational estimates, without a differentiability or integral claim.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.SquareRoot

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The exact Gaussian half used in the affine square-root coefficient. -/
@[expose] def half : Canonical := ⟨1 / 2, 0⟩

/-- Twice the retained Gaussian half is exactly one. -/
private theorem half_double : half * 2 = 1 := by decide +kernel

/-- The retained Gaussian half has squared norm at most one. -/
private theorem half_norm_le : Norm.Basic.normSq half ≤ 1 := by decide +kernel

/-- The combined square error of two readings of an affine radicand. -/
@[expose] def error (first last increment coefficient : Canonical) : Canonical :=
  last * last - first * first + increment * coefficient

/-- Both original square residuals pay the error in the affine square relation. -/
theorem error_le {first last radicand increment coefficient : Canonical}
    {firstAllowance lastAllowance : Fraction.Rational}
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstAllowance)
    (lastResidual : Norm.Basic.normSq
      (last * last - (radicand - increment * coefficient)) ≤ lastAllowance) :
    Norm.Basic.normSq (error first last increment coefficient) ≤
      2 * (firstAllowance + lastAllowance) := by
  have identity : error first last increment coefficient =
      (last * last - (radicand - increment * coefficient)) -
        (first * first - radicand) := by
    unfold error
    ring1
  rewrite [identity]
  calc
    _ ≤ 2 * (Norm.Basic.normSq (last * last - (radicand - increment * coefficient)) +
        Norm.Basic.normSq (first * first - radicand)) := Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (lastAllowance + firstAllowance) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct lastResidual firstResidual) (by decide +kernel)
    _ = _ := by ring1

/-- Square residuals and the actual reciprocal of the signed sum bound root movement.

The first and last readings are distinct inputs. Their sum is required to be
nonzero, and its displayed reciprocal remains in the computed bound.
-/
theorem movement_le {first last radicand increment coefficient : Canonical}
    {firstAllowance lastAllowance : Fraction.Rational}
    (sumNonzero : first + last ≠ 0)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstAllowance)
    (lastResidual : Norm.Basic.normSq
      (last * last - (radicand - increment * coefficient)) ≤ lastAllowance) :
    Norm.Basic.normSq (last - first) ≤
      (4 * (firstAllowance + lastAllowance) +
        2 * Norm.Basic.normSq increment * Norm.Basic.normSq coefficient) *
          Norm.Basic.normSq ((first + last)⁻¹) := by
  have inverseCancel : (first + last)⁻¹ * (first + last) = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul (first + last) sumNonzero
  have factorization : last - first =
      (error first last increment coefficient - increment * coefficient) *
        (first + last)⁻¹ := by
    apply Gaussian.Field.mul_right_cancel_of_ne sumNonzero
    calc
      (last - first) * (first + last) =
          error first last increment coefficient - increment * coefficient := by
        unfold error
        ring1
      _ = ((error first last increment coefficient - increment * coefficient) *
          (first + last)⁻¹) * (first + last) := by
        rewrite [Gaussian.Basic.mul_assoc, inverseCancel, Gaussian.Basic.mul_one]
        rfl
  rewrite [factorization, Norm.Basic.normSq_mul]
  apply Arithmetic.mul_le_mul_of_nonneg_right_direct _
    (Norm.Basic.normSq_nonneg _)
  calc
    _ ≤ 2 * (Norm.Basic.normSq (error first last increment coefficient) +
        Norm.Basic.normSq (increment * coefficient)) := Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (2 * (firstAllowance + lastAllowance) +
        Norm.Basic.normSq increment * Norm.Basic.normSq coefficient) := by
      rewrite [Norm.Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (error_le firstResidual lastResidual)
          (Fraction.Order.Basic.le_refl _)) (by decide +kernel)
    _ = _ := by ring1

/-- The explicit root-movement factor when both square residuals are paid at quadratic accuracy. -/
@[expose] def movementFactor (first last coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational) : Fraction.Rational :=
  (4 * (firstFactor + lastFactor) + 2 * Norm.Basic.normSq coefficient) *
    Norm.Basic.normSq ((first + last)⁻¹)

/-- The computed Taylor factor pays both square residuals and the squared root-movement factor. -/
@[expose] def remainderFactor (first last coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational) : Fraction.Rational :=
  2 * (2 * (firstFactor + lastFactor) +
    movementFactor first last coefficient firstFactor lastFactor ^ 2) *
      Norm.Basic.normSq first⁻¹

/-- The actual two finite readings construct a root Taylor certificate for the affine radicand.

The input residual budgets scale as the square of increment quadrance. The
unit increment bound turns them into a linear root-movement bound, and the
resulting quadratic factor is computed from those budgets and the original
readings' reciprocals. No remainder or movement bound is supplied by the caller.
-/
@[expose] def certificate (first last radicand increment coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor)
    (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq
      (last * last - (radicand - increment * coefficient)) ≤
        lastFactor * Norm.Basic.normSq increment ^ 2) : Certificate increment := by
  let movement := movementFactor first last coefficient firstFactor lastFactor
  let remainder := half *
    (error first last increment coefficient - (last - first) ^ 2) * first⁻¹
  have inverseCancel : first⁻¹ * first = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul first firstNonzero
  have expansion : last - first - increment * (-(half * coefficient * first⁻¹)) = remainder := by
    apply Gaussian.Field.mul_right_cancel_of_ne firstNonzero
    calc
      (last - first - increment * (-(half * coefficient * first⁻¹))) * first =
          (last - first) * first + half * increment * coefficient * (first⁻¹ * first) := by ring1
      _ = (last - first) * first + half * increment * coefficient := by
        rewrite [inverseCancel, Gaussian.Basic.mul_one]
        rfl
      _ = half * (error first last increment coefficient - (last - first) ^ 2) := by
        calc
          _ = half * (2 * (last - first) * first + increment * coefficient) := by
            rewrite [show (last - first) * first = (half * 2) * ((last - first) * first) by
              rewrite [half_double, Gaussian.Basic.one_mul]; rfl]
            ring1
          _ = _ := by unfold error; ring1
      _ = remainder * first := by
        dsimp only [remainder]
        rewrite [Gaussian.Basic.mul_assoc, inverseCancel, Gaussian.Basic.mul_one]
        rfl
  have incrementSquareLe : Norm.Basic.normSq increment ^ 2 ≤ Norm.Basic.normSq increment := by
    rewrite [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct unit
      (Norm.Basic.normSq_nonneg increment)).trans_eq (Fraction.Field.mul_one_direct _)
  have factorsNonnegative : 0 ≤ firstFactor + lastFactor :=
    Arithmetic.add_le_add_direct firstFactorNonnegative lastFactorNonnegative
  have movementBound : Norm.Basic.normSq (last - first) ≤ movement * Norm.Basic.normSq increment := by
    calc
      _ ≤ (4 * (firstFactor * Norm.Basic.normSq increment ^ 2 +
          lastFactor * Norm.Basic.normSq increment ^ 2) +
          2 * Norm.Basic.normSq increment * Norm.Basic.normSq coefficient) *
          Norm.Basic.normSq ((first + last)⁻¹) :=
        movement_le sumNonzero firstResidual lastResidual
      _ ≤ (4 * (firstFactor * Norm.Basic.normSq increment +
          lastFactor * Norm.Basic.normSq increment) +
          2 * Norm.Basic.normSq increment * Norm.Basic.normSq coefficient) *
          Norm.Basic.normSq ((first + last)⁻¹) := by
        apply Arithmetic.mul_le_mul_of_nonneg_right_direct _ (Norm.Basic.normSq_nonneg _)
        apply Arithmetic.add_le_add_direct _ (Fraction.Order.Basic.le_refl _)
        apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide +kernel)
        exact Arithmetic.add_le_add_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct incrementSquareLe firstFactorNonnegative)
          (Arithmetic.mul_le_mul_of_nonneg_left_direct incrementSquareLe lastFactorNonnegative)
      _ = _ := by dsimp only [movement, movementFactor]; ring1
  have movementSquare : Norm.Basic.normSq ((last - first) ^ 2) ≤
      movement ^ 2 * Norm.Basic.normSq increment ^ 2 := by
    calc
      _ = Norm.Basic.normSq (last - first) ^ 2 := by
        rewrite [pow_two, Norm.Basic.normSq_mul, pow_two]
        rfl
      _ ≤ (movement * Norm.Basic.normSq increment) ^ 2 :=
        Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) movementBound 2
      _ = _ := by ring1
  have errorBound : Norm.Basic.normSq (error first last increment coefficient) ≤
      2 * (firstFactor + lastFactor) * Norm.Basic.normSq increment ^ 2 :=
    (error_le firstResidual lastResidual).trans_eq (by ring1)
  refine
    { base := first
      slope := -(half * coefficient * first⁻¹)
      output := last
      remainder := remainder
      expansion := expansion
      factor := remainderFactor first last coefficient firstFactor lastFactor
      factor_nonneg := ?_
      remainder_le := ?_ }
  · unfold remainderFactor
    exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel) factorsNonnegative)
          (Arithmetic.sq_nonneg_direct _))) (Norm.Basic.normSq_nonneg _)
  · simp only [← Norm.Basic.normSq_eq_canonical]
    dsimp only [remainder]
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    calc
      _ ≤ 1 * (2 * (Norm.Basic.normSq (error first last increment coefficient) +
          Norm.Basic.normSq ((last - first) ^ 2))) * Norm.Basic.normSq first⁻¹ := by
        apply Arithmetic.mul_le_mul_of_nonneg_right_direct _ (Norm.Basic.normSq_nonneg _)
        exact Arithmetic.mul_le_mul_of_nonneg_left_direct
          ((Norm.Bounds.normSq_sub_le_two _ _).trans_eq (by ring1))
          (Norm.Basic.normSq_nonneg half) |>.trans
            (Arithmetic.mul_le_mul_of_nonneg_right_direct half_norm_le
              (Arithmetic.mul_nonneg_direct (by decide +kernel)
                (Arithmetic.add_le_add_direct (Norm.Basic.normSq_nonneg _)
                  (Norm.Basic.normSq_nonneg _))))
      _ ≤ 1 * (2 * (2 * (firstFactor + lastFactor) * Norm.Basic.normSq increment ^ 2 +
          movement ^ 2 * Norm.Basic.normSq increment ^ 2)) * Norm.Basic.normSq first⁻¹ := by
        apply Arithmetic.mul_le_mul_of_nonneg_right_direct _ (Norm.Basic.normSq_nonneg _)
        exact Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct errorBound movementSquare) (by decide +kernel))
          (by decide +kernel)
      _ = _ := by dsimp only [remainderFactor, movement]; ring1

/-- Exact reciprocal expansion at the actual displacement between two nonzero readings.

The remainder is the squared displacement times the two retained inverse
factors. Its factor is computed by multiplicativity of Gaussian quadrance.
-/
@[expose] def reciprocalCertificate (first last : Canonical)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) : Certificate (last - first) := by
  have firstCancel : first⁻¹ * first = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul first firstNonzero
  have lastCancel : last⁻¹ * last = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul last lastNonzero
  have reciprocalDifference : last⁻¹ - first⁻¹ = -(last - first) * first⁻¹ * last⁻¹ := by
    apply Gaussian.Field.mul_right_cancel_of_ne lastNonzero
    apply Gaussian.Field.mul_right_cancel_of_ne firstNonzero
    calc
      (last⁻¹ - first⁻¹) * last * first =
          (last⁻¹ * last) * first - (first⁻¹ * first) * last := by ring1
      _ = first - last := by
        simp only [firstCancel, lastCancel, Gaussian.Basic.one_mul, -eq_self, -iff_self]
        rfl
      _ = (-(last - first) * first⁻¹ * last⁻¹) * last * first := by
        calc
          _ = -(last - first) * (first⁻¹ * first) * (last⁻¹ * last) := by
            rewrite [firstCancel, lastCancel]; ring1
          _ = _ := by ring1
  have inverseIdentity : first⁻¹ * first⁻¹ - first⁻¹ * last⁻¹ =
      (last - first) * first⁻¹ * first⁻¹ * last⁻¹ := by
    calc
      _ = -first⁻¹ * (last⁻¹ - first⁻¹) := by ring1
      _ = _ := by rewrite [reciprocalDifference]; ring1
  refine
    { base := first⁻¹
      slope := -(first⁻¹ * first⁻¹)
      output := last⁻¹
      remainder := (last - first) ^ 2 * (first⁻¹ * first⁻¹ * last⁻¹)
      expansion := ?_
      factor := Norm.Basic.normSq (first⁻¹ * first⁻¹ * last⁻¹)
      factor_nonneg := Norm.Basic.normSq_nonneg _
      remainder_le := ?_ }
  · calc
      _ = (last - first) * (first⁻¹ * first⁻¹ - first⁻¹ * last⁻¹) := by
        rewrite [reciprocalDifference]
        ring1
      _ = _ := by rewrite [inverseIdentity]; ring1
  · simp only [← Norm.Basic.normSq_eq_canonical]
    rewrite [Norm.Basic.normSq_mul, pow_two, Norm.Basic.normSq_mul]
    exact Fraction.Order.Basic.le_refl _ |>.trans_eq (by ring1)

/-- Compose the computed root expansion with its exact reciprocal expansion.

Both original finite readings remain the base and output owners. The generic
quadratic composition machinery computes and proves the inverse-root remainder
factor rather than asking for a new inverse-root comparison certificate.
-/
@[expose] def inverseCertificate (first last radicand increment coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor)
    (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0)
    (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq
      (last * last - (radicand - increment * coefficient)) ≤
        lastFactor * Norm.Basic.normSq increment ^ 2) : Certificate increment :=
  (certificate first last radicand increment coefficient firstFactor lastFactor
    firstFactorNonnegative lastFactorNonnegative firstNonzero sumNonzero unit
      firstResidual lastResidual).compose
    (reciprocalCertificate first last firstNonzero lastNonzero)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)

/-- The inverse-root expansion retains the original first reciprocal as its base. -/
theorem inverseCertificate_base (first last radicand increment coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - (radicand - increment * coefficient)) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (inverseCertificate first last radicand increment coefficient firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).base = first⁻¹ := rfl

/-- The inverse-root expansion retains the original last reciprocal as its output. -/
theorem inverseCertificate_output (first last radicand increment coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - (radicand - increment * coefficient)) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (inverseCertificate first last radicand increment coefficient firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).output = last⁻¹ := rfl

/-- The computed inverse-root coefficient is the affine radicand coefficient over twice the first root cube. -/
theorem inverseCertificate_slope (first last radicand increment coefficient : Canonical)
    (firstFactor lastFactor : Fraction.Rational)
    (firstFactorNonnegative : 0 ≤ firstFactor) (lastFactorNonnegative : 0 ≤ lastFactor)
    (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - (radicand - increment * coefficient)) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (inverseCertificate first last radicand increment coefficient firstFactor lastFactor
      firstFactorNonnegative lastFactorNonnegative firstNonzero lastNonzero sumNonzero unit
        firstResidual lastResidual).slope = half * coefficient * first⁻¹ ^ 3 := by
  change (-(half * coefficient * first⁻¹)) * -(first⁻¹ * first⁻¹) = _
  ring1

end Purelib.Calculus.Jet.Quadratic.SquareRoot
