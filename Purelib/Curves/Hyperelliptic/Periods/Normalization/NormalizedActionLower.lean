module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Readings.NamedMatrixActionBound
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

@[expose] public section

/-! A sample-independent normalized energy floor from the actual finite
A-action bound, with the canonical scalar denominator accounted for. -/
namespace Purelib.Curves.Hyperelliptic.Periods.Normalization.NormalizedActionLower

open Purelib.Riemann.Periods.PeriodMatrix (PeriodData sampledMatrix)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (RationalVector NonzeroVector)
open Purelib.Riemann.Readings.NamedMatrixActionBound (UniformActionBound)
open Purelib.LinearAlgebra.Gaussian.Energy (gaussianVectorOfRational gaussianVectorOfRational_apply
  gaussianOfRational_ne_zero scaledNormalizedCoefficients periodCombination periodCombination_scaled_a)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate (synchronizedScaledInverse)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  (data : PeriodData curve) (bound :
    UniformActionBound data.aMatrix)

/-- Embedding a retained nonzero rational vector gives a strictly positive finite Gaussian coefficient norm. -/
theorem embedded_norm_positive (vector : QuadraticForm.RationalVector genus) (nonzero : QuadraticForm.NonzeroVector
  vector) :
    0 < PreparedObservationCoercivity.coefficientNormSq (Energy.gaussianVectorOfRational vector) := by
  apply PreparedObservationCoercivity.coefficientNormSq_positive
  refine ⟨nonzero.index, ?_⟩
  rw [Energy.gaussianVectorOfRational_apply]
  exact Energy.gaussianOfRational_ne_zero nonzero.coefficient_nonzero

/-- The synchronized A-action of scaled normalized coefficients has norm equal to the inverse scalar squared norm times
the original vector norm. -/
theorem scaled_action_norm (index : Nat) (vector : QuadraticForm.RationalVector genus) :
    Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq (Energy.periodCombination
      (Purelib.LinearAlgebra.Gaussian.Energy.scaledNormalizedCoefficients data index vector)
      (PeriodMatrix.sampledMatrix data.aMatrix index)) =
    Data.Gaussian.Norm.Basic.normSq (Certificate.synchronizedScaledInverse data index).scalar *
      Purelib.Riemann.Readings.PreparedObservationCoercivity.coefficientNormSq (Energy.gaussianVectorOfRational vector)
      := by
  unfold Energy.scaledNormalizedCoefficients
  rw [Energy.periodCombination_scaled_a]
  unfold PreparedObservationCoercivity.coefficientNormSq
  rw [FiniteSum.Fin.sumFin_congr (fun row => by rw [Data.Vector.Basic.vectorOfFn_apply, ←
    Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq_mul,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical])]
  rw [FiniteSum.Fin.sumFin_mul_right]
  exact _root_.mul_comm _ _

/-- A retained uniform A-action bound transports the raw energy floor to normalized coordinates.

The original scalar squared norm and action scale remain explicit positive denominators; the conclusion uses the same
synchronized coefficients and sampled energy. -/
theorem normalized_lower (index : Nat) (vector : QuadraticForm.RationalVector genus)
    (scalarPositive : 0 < Data.Gaussian.Norm.Basic.normSq (Certificate.synchronizedScaledInverse data
      index).scalar)
    (lower : Fraction.Rational) (lowerNonnegative : 0 ≤ lower) (energy : Fraction.Rational)
    (energyLower : lower * PreparedObservationCoercivity.coefficientNormSq (Energy.scaledNormalizedCoefficients data
      index vector) ≤ energy) :
    lower * PreparedObservationCoercivity.coefficientNormSq (Energy.gaussianVectorOfRational vector) / bound.scale ≤
      energy / Data.Gaussian.Norm.Basic.normSq (Certificate.synchronizedScaledInverse data index).scalar := by
  have action := bound.action_bound index (Energy.scaledNormalizedCoefficients data index vector)
  rw [scaled_action_norm] at action
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct action lowerNonnegative
  have energyBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct energyLower bound.scale_positive.le
  apply (Fraction.Order.Field.le_div_iff_pos scalarPositive).mpr
  calc
    _ = (lower * (Data.Gaussian.Norm.Basic.normSq (Certificate.synchronizedScaledInverse data index).scalar *
        PreparedObservationCoercivity.coefficientNormSq (Energy.gaussianVectorOfRational vector))) / bound.scale := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ ≤ energy := (Fraction.Order.Field.div_le_iff_pos bound.scale_positive).mpr (by
      calc
        _ ≤ lower * (bound.scale * PreparedObservationCoercivity.coefficientNormSq (Energy.scaledNormalizedCoefficients
          data index vector)) := multiplied
        _ = bound.scale * (lower * PreparedObservationCoercivity.coefficientNormSq (Energy.scaledNormalizedCoefficients
          data index vector)) := by
          ring1
        _ ≤ bound.scale * energy := energyBound
        _ = energy * bound.scale  := _root_.mul_comm _ _)

end Purelib.Curves.Hyperelliptic.Periods.Normalization.NormalizedActionLower
