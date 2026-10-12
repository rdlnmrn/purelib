module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Divisibility.Half
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Pair.LinearCombination

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.GaussianInt.Divisibility

open Purelib.Data.GaussianInt.Pair

open Purelib.Data.GaussianInt.Pair.Basic

section
@[expose] public section

/-!
# Local finite successors of best Gaussian approximations

This file replaces the existential division in the centered coefficient
coset by an executable coordinate calculation.  It then uses the consecutive
index dichotomy and the no-repeated-index theorem to build a finite successor
search from one adjacent best pair rather than from the full source rectangle.
-/

namespace Purelib.Data.GaussianInt.Pair.Division

/-- Execute quadrance-two Gaussian division on both coordinates of the retained pair. -/
def dividePairByNormTwo (divisor : GaussianInt) (pair : ConvergentPair) :
  ConvergentPair :=
  { numerator := Half.divideByNormTwo divisor pair.numerator
    denominator := Half.divideByNormTwo divisor pair.denominator }

/-- Pairwise quadrance-two division cancels scaling by the displayed divisor. -/
theorem dividePairByNormTwo_scalePair
    (divisor : GaussianInt) (pair : ConvergentPair) (divisorNorm : GaussianInt.normNat divisor = 2) :
    dividePairByNormTwo divisor
        (LinearCombination.scalePair divisor pair) = pair := by
  apply LinearCombination.pair_ext
  · exact Half.divideByNormTwo_mul divisor pair.numerator divisorNorm
  · exact Half.divideByNormTwo_mul divisor pair.denominator divisorNorm

/-- Recover a pair by executable quadrance-two division from a retained scaling identity. -/
theorem eq_dividePairByNormTwo_of_scalePair_eq
    (divisor : GaussianInt) (pair combination : ConvergentPair)
    (divisorNorm : GaussianInt.normNat divisor = 2)
    (identity : LinearCombination.scalePair divisor pair = combination) :
    pair = dividePairByNormTwo divisor combination := by
  rw [← identity, dividePairByNormTwo_scalePair divisor pair divisorNorm]

/-- A consecutive-pair determinant quadrance scales by the leading coefficient's
quadrance under an exact linear combination. -/
theorem coefficientIndexQuadrance_eq_of_linearCombination
    (previous current next : ConvergentPair)
    (leftCoefficient rightCoefficient : GaussianInt)
    (identity : next =
      LinearCombination.linearCombination previous current
        leftCoefficient rightCoefficient) :
    LinearCombination.coefficientIndexQuadrance current next =
      GaussianInt.normNat leftCoefficient *
        LinearCombination.coefficientIndexQuadrance previous current := by
  rw [LinearCombination.coefficientIndexQuadrance, identity,
    LinearCombination.coefficientDeterminant_right_linearCombination,
    GaussianInt.normNat_neg, GaussianInt.normNat_mul]
  rfl

/-- An exact scaled linear-combination identity equates the two corresponding
coefficient-weighted determinant quadrances. -/
theorem coefficientIndexQuadrance_scale_eq_of_scalePair_eq
    (previous current next : ConvergentPair)
    (scale leftCoefficient rightCoefficient : GaussianInt)
    (identity :
      LinearCombination.scalePair scale next =
        LinearCombination.linearCombination previous current
          leftCoefficient rightCoefficient) :
    GaussianInt.normNat scale *
        LinearCombination.coefficientIndexQuadrance current next =
      GaussianInt.normNat leftCoefficient *
        LinearCombination.coefficientIndexQuadrance previous current := by
  have determinantIdentity := congrArg
    (LinearCombination.coefficientDeterminant current) identity
  rw [LinearCombination.coefficientDeterminant_scalePair_right,
    LinearCombination.coefficientDeterminant_right_linearCombination]
      at determinantIdentity
  have normIdentity := congrArg GaussianInt.normNat determinantIdentity
  rw [GaussianInt.normNat_mul,
    GaussianInt.normNat_neg,
    GaussianInt.normNat_mul] at normIdentity
  exact normIdentity

/-- Scaling both coordinates of an integral pair by one leaves the pair unchanged. -/
theorem scalePair_one (pair : ConvergentPair) :
    LinearCombination.scalePair 1 pair = pair := by
  apply LinearCombination.pair_ext <;>
    apply GaussianInt.ext <;>
      simp only [LinearCombination.scalePair,
        GaussianInt.mul_re,
        GaussianInt.mul_im,
        GaussianInt.one_re,
        GaussianInt.one_im] <;>
      ring1
end Purelib.Data.GaussianInt.Pair.Division

end
