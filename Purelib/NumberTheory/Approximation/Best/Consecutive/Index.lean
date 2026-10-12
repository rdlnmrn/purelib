module
import Purelib.Data.Nat.Order
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Algebra.NatCast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Divisibility.Basic
import Purelib.Data.GaussianInt.Divisibility.NormTwo
import Purelib.Data.GaussianInt.Division.NearestGeometry
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.GCD
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Basic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Conjugate
import Purelib.Tactic.Ring

public section

open Purelib.Data

open Purelib.NumberTheory.Approximation

section

/-!
# Coefficient indices of consecutive Gaussian approximations

The retained Gaussian-integer pairs determine a coefficient lattice and its
natural determinant quadrance. Exact finite remainder geometry bounds that
index by two and distinguishes the coefficient span from its centered coset.
-/

namespace Purelib.NumberTheory.Approximation.Best.Consecutive.Index

/-- A best pair has no displayed nonunit common Gaussian-integer scale. -/
theorem IsBest.scalingCoefficient_norm_eq_one
    {source : Gaussian.Basic.Canonical} {reference quotient : GaussianInt.Pair.Basic.ConvergentPair} {coefficient :
      GaussianInt}
    (best : Best.Basic.IsBest source reference)
    (quotientDenominatorNonzero : quotient.denominator ≠ 0)
    (scaled : reference = GaussianInt.Pair.LinearCombination.scalePair coefficient quotient) :
    GaussianInt.normNat coefficient = 1 := open Purelib.Data.Rat in by
  have coefficientNonzero : coefficient ≠ 0 := by
    intro coefficientZero
    apply best.1
    rw [scaled, coefficientZero]
    change (0 : GaussianInt) * quotient.denominator = 0
    exact GaussianInt.zero_mul _
  have coefficientPositive := GaussianInt.normNat_pos coefficientNonzero
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro coefficientGreaterThanOne
    have quotientDenominatorPositive := GaussianInt.normNat_pos quotientDenominatorNonzero
    have denominatorSmaller :
        Best.Error.denominatorQuadrance quotient < Best.Error.denominatorQuadrance reference := by
      rw [scaled, Best.Error.denominatorQuadrance_scalePair]
      have scaledStrict :
          Best.Error.denominatorQuadrance quotient <
            GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance quotient := by
        change GaussianInt.normNat quotient.denominator <
          GaussianInt.normNat coefficient * GaussianInt.normNat quotient.denominator
        simpa only [Nat.one_mul, -eq_self, -iff_self] using
          Nat.mul_lt_mul_of_pos_right coefficientGreaterThanOne
            quotientDenominatorPositive
      exact scaledStrict
    have bestStrict := best.2.1 quotient quotientDenominatorNonzero
      denominatorSmaller
    have quotientErrorLeReference :
        Best.Error.errorQuadrance source quotient ≤ Best.Error.errorQuadrance source reference := by
      rw [scaled, Best.Error.errorQuadrance_scalePair]
      have oneLeCoefficient :
          (1 : Fraction.Rational) ≤ (GaussianInt.normNat coefficient : Fraction.Rational) :=
        Fraction.Cast.Order.natCast_le_direct coefficientPositive
      calc
        Best.Error.errorQuadrance source quotient =
            (1 : Fraction.Rational) * Best.Error.errorQuadrance source quotient := by ring1
        _ ≤ (GaussianInt.normNat coefficient : Fraction.Rational) *
              Best.Error.errorQuadrance source quotient :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            oneLeCoefficient (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source quotient))
    exact (not_lt_of_ge quotientErrorLeReference) bestStrict
  · exact coefficientPositive

/-- The quotient denominator in a displayed scaling of a best pair is
automatically nonzero, so the scale itself must be a unit. -/
theorem IsBest.scalingCoefficient_norm_eq_one_of_scaled
    {source : Gaussian.Basic.Canonical} {reference quotient : GaussianInt.Pair.Basic.ConvergentPair}
    {coefficient : GaussianInt}
    (best : Best.Basic.IsBest source reference)
    (scaled : reference = GaussianInt.Pair.LinearCombination.scalePair coefficient quotient) :
    GaussianInt.normNat coefficient = 1 := by
  have quotientDenominatorNonzero : quotient.denominator ≠ 0 := by
    intro quotientDenominatorZero
    apply best.1
    rw [scaled]
    change coefficient * quotient.denominator = 0
    rw [quotientDenominatorZero,
      GaussianInt.mul_zero]
  exact (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one best) quotientDenominatorNonzero scaled

/-! ## Explicit coefficient bases from the Gaussian Euclidean algorithm -/

/-- Divide both coefficients of a pair by their computed Gaussian gcd. -/
@[expose] def gcdQuotientPair (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : GaussianInt.Pair.Basic.ConvergentPair :=
  let certificate := GaussianInt.GCD.extendedGCD
    pair.numerator pair.denominator
  { numerator := certificate.leftQuotient
    denominator := certificate.rightQuotient }

/-- Dividing a nonzero denominator by the retained common gcd leaves a nonzero quotient denominator. -/
theorem gcdQuotientPair_denominator_ne_zero
    {pair : GaussianInt.Pair.Basic.ConvergentPair} (denominatorNonzero : pair.denominator ≠ 0) :
    (gcdQuotientPair pair).denominator ≠ 0 := by
  let certificate := GaussianInt.GCD.extendedGCD
    pair.numerator pair.denominator
  change certificate.rightQuotient ≠ 0
  intro quotientZero
  have factor := certificate.right_factor
  rw [quotientZero,
    GaussianInt.mul_zero] at factor
  exact denominatorNonzero factor

/-- The original pair is its computed gcd times the pair of retained Euclidean quotients. -/
theorem pair_eq_scalePair_euclideanGCD (pair :
  GaussianInt.Pair.Basic.ConvergentPair) :
    let certificate := GaussianInt.GCD.extendedGCD
      pair.numerator pair.denominator
    pair = GaussianInt.Pair.LinearCombination.scalePair certificate.gcd (gcdQuotientPair pair) :=
      by
  dsimp only
  apply GaussianInt.Pair.LinearCombination.pair_ext
  · exact (GaussianInt.GCD.extendedGCD
      pair.numerator pair.denominator).left_factor
  · exact (GaussianInt.GCD.extendedGCD
      pair.numerator pair.denominator).right_factor

/-- Bestness forces the computed common Gaussian divisor to be a unit. -/
theorem IsBest.euclideanGCD_norm_eq_one
    {source : Gaussian.Basic.Canonical} {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source reference) :
    GaussianInt.normNat (GaussianInt.GCD.extendedGCD
      reference.numerator reference.denominator).gcd = 1 := by
  exact (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one best)
    (gcdQuotientPair_denominator_ne_zero best.1)
    (pair_eq_scalePair_euclideanGCD reference)

/-- Complete a displayed pair to a coefficient basis using its computed
Bezout coefficients, normalized by the conjugate of its unit gcd. -/
@[expose] def bezoutComplement (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : GaussianInt.Pair.Basic.ConvergentPair :=
  let certificate := GaussianInt.GCD.extendedGCD
    pair.numerator pair.denominator
  let unitScale := GaussianInt.conj certificate.gcd
  { numerator := -(unitScale * certificate.rightCoefficient)
    denominator := unitScale * certificate.leftCoefficient }

/-- A best pair and its computed Bezout complement have determinant one. -/
theorem
  IsBest.coefficientDeterminant_bezoutComplement_eq_one
    {source : Gaussian.Basic.Canonical} {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source reference) :
    GaussianInt.Pair.LinearCombination.coefficientDeterminant reference (bezoutComplement
      reference) = 1 := by
  let certificate := GaussianInt.GCD.extendedGCD
    reference.numerator reference.denominator
  have bezout := certificate.bezout
  have gcdNorm := (Best.Consecutive.Index.IsBest.euclideanGCD_norm_eq_one best)
  have conjugateProduct : GaussianInt.conj certificate.gcd * certificate.gcd = 1 := by
    rw [GaussianInt.mul_comm,
      GaussianInt.mul_conj, gcdNorm]
    rfl
  calc
    GaussianInt.Pair.LinearCombination.coefficientDeterminant reference (bezoutComplement
      reference) =
        GaussianInt.conj certificate.gcd *
          (certificate.leftCoefficient * reference.numerator +
            certificate.rightCoefficient * reference.denominator) := by
      apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.coefficientDeterminant, GaussianInt.Pair.Basis.determinant,
          bezoutComplement,
          certificate,
          GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im, -eq_self, -iff_self] <;>
        ring1
    _ = GaussianInt.conj certificate.gcd * certificate.gcd := by rw [← bezout]
    _ = 1 := conjugateProduct

/-- A best pair and its computed Bézout complement have coefficient-index quadrance one. -/
theorem
  IsBest.coefficientIndexQuadrance_bezoutComplement_eq_one
    {source : Gaussian.Basic.Canonical} {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source reference) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance reference (bezoutComplement
      reference) = 1 := by
  rw [GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance,
    (Best.Consecutive.Index.IsBest.coefficientDeterminant_bezoutComplement_eq_one best)]
  rfl

/-- First integral coordinate of `candidate` in the explicit basis completed
from the best pair `reference`. -/
@[expose] def bezoutBasisFirstCoefficient (reference
  candidate : GaussianInt.Pair.Basic.ConvergentPair) : GaussianInt :=
  GaussianInt.Pair.LinearCombination.coefficientDeterminant candidate (bezoutComplement
    reference)

/-- The computed Bezout complement gives explicit integral coordinates for
every ambient coefficient pair. -/
theorem IsBest.linearCombination_bezoutBasis
    {source : Gaussian.Basic.Canonical} {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source reference) (candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.Pair.LinearCombination.linearCombination reference (bezoutComplement reference)
        (bezoutBasisFirstCoefficient reference candidate)
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant reference candidate) = candidate := by
  have expansion := GaussianInt.Pair.LinearCombination.linearCombination_cramer_of_index_one
    reference (bezoutComplement reference) candidate
      (Best.Consecutive.Index.IsBest.coefficientIndexQuadrance_bezoutComplement_eq_one best)
  dsimp only at expansion
  rw [(Best.Consecutive.Index.IsBest.coefficientDeterminant_bezoutComplement_eq_one best)] at expansion
  rw [show GaussianInt.conj (1 : GaussianInt) = 1 by rfl] at expansion
  simpa only [bezoutBasisFirstCoefficient,
    GaussianInt.one_mul, -eq_self, -iff_self] using expansion

/-- In the index-two case the coefficient of `lower` in the explicit Bezout
basis expansion of `upper` lies in the nondivisible residue class.  Otherwise
`upper` would have a nonunit common Gaussian factor. -/
theorem
  IsBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source lower) (upperBest : Best.Basic.IsBest source upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    ¬ GaussianInt.Divisibility.Basic.Divides (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper)
      (bezoutBasisFirstCoefficient lower upper) := by
  intro divisible
  rcases divisible with ⟨quotient, coefficientIdentity⟩
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  have basisExpansion := (Best.Consecutive.Index.IsBest.linearCombination_bezoutBasis lowerBest) upper
  have scaled :
      upper = GaussianInt.Pair.LinearCombination.scalePair determinantValue
        (GaussianInt.Pair.LinearCombination.linearCombination lower complement quotient 1) := by
    calc
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement
          (bezoutBasisFirstCoefficient lower upper) determinantValue :=
        basisExpansion.symm
      _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
          (determinantValue * quotient) (determinantValue * 1) := by
        rw [coefficientIdentity]
        apply GaussianInt.Pair.LinearCombination.pair_ext <;>
          apply GaussianInt.ext <;>
          simp only [GaussianInt.Pair.LinearCombination.linearCombination,
            GaussianInt.add_re,
            GaussianInt.add_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im,
            GaussianInt.one_re,
            GaussianInt.one_im, -eq_self, -iff_self] <;>
          ring1
      _ = GaussianInt.Pair.LinearCombination.scalePair determinantValue
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement quotient 1) :=
        GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
          determinantValue quotient 1
  have determinantUnit :=
    (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled upperBest) scaled
  change GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1 at determinantUnit
  rw [indexTwo] at determinantUnit
  exact (show (2 : Nat) ≠ 1 by decide) determinantUnit

/-- Every ambient coefficient pair lies either in the ordinary span of two
index-two best pairs or in their centered coset.  The proof uses the explicit
Bezout basis of `lower`; no quotient lattice is formed. -/
theorem
  IsBest.inCoefficientSpan_or_inCenteredCoefficientCoset_of_index_two
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source lower) (upperBest : Best.Basic.IsBest source upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.Pair.LinearCombination.InCoefficientSpan lower upper candidate ∨
      GaussianInt.Pair.LinearCombination.InCenteredCoefficientCoset lower upper candidate := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  let upperCoefficient := bezoutBasisFirstCoefficient lower upper
  let candidateCoefficient := bezoutBasisFirstCoefficient lower candidate
  let candidateComplementCoefficient :=
    GaussianInt.Pair.LinearCombination.coefficientDeterminant lower candidate
  have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
    simpa only [determinantValue, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
      using indexTwo
  have upperCoefficientNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue upperCoefficient := by
    simpa only [determinantValue, upperCoefficient, -eq_self, -iff_self] using
      (Best.Consecutive.Index.IsBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two lowerBest)
        upperBest indexTwo
  have upperExpansion := (Best.Consecutive.Index.IsBest.linearCombination_bezoutBasis lowerBest) upper
  have candidateExpansion := (Best.Consecutive.Index.IsBest.linearCombination_bezoutBasis lowerBest) candidate
  have upperExpansion' :
      GaussianInt.Pair.LinearCombination.linearCombination lower complement upperCoefficient determinantValue =
        upper := by
    simpa only [complement, upperCoefficient, determinantValue, -eq_self, -iff_self] using
      upperExpansion
  have candidateExpansion' :
      GaussianInt.Pair.LinearCombination.linearCombination lower complement candidateCoefficient
          candidateComplementCoefficient = candidate := by
    simpa only [complement, candidateCoefficient,
      candidateComplementCoefficient, -eq_self, -iff_self] using candidateExpansion
  rcases GaussianInt.Divisibility.NormTwo.coordinateEven_or_coordinateOdd
      candidateComplementCoefficient with complementEven | complementOdd
  · have complementCoefficientDivisible :
        GaussianInt.Divisibility.Basic.Divides determinantValue
          candidateComplementCoefficient :=
      (GaussianInt.Divisibility.NormTwo.divides_iff_coordinateEven_of_norm_two
        determinantNorm).mpr complementEven
    left
    rcases complementCoefficientDivisible with
      ⟨quotient, complementCoefficientIdentity⟩
    refine ⟨candidateCoefficient - upperCoefficient * quotient,
      quotient, ?_⟩
    calc
      candidate = GaussianInt.Pair.LinearCombination.linearCombination lower complement candidateCoefficient
          candidateComplementCoefficient := candidateExpansion'.symm
      _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
          ((candidateCoefficient - upperCoefficient * quotient) +
            quotient * upperCoefficient)
          (quotient * determinantValue) := by
        rw [complementCoefficientIdentity]
        apply GaussianInt.Pair.LinearCombination.pair_ext <;>
          apply GaussianInt.ext <;>
          simp only [GaussianInt.Pair.LinearCombination.linearCombination,
            GaussianInt.add_re,
            GaussianInt.add_im,
            GaussianInt.sub_re,
            GaussianInt.sub_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im, -eq_self, -iff_self] <;>
          ring1
      _ = GaussianInt.Pair.LinearCombination.linearCombination lower
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement upperCoefficient
            determinantValue)
          (candidateCoefficient - upperCoefficient * quotient)
          quotient :=
        (GaussianInt.Pair.LinearCombination.linearCombination_nested_right lower complement upperCoefficient
          determinantValue
          (candidateCoefficient - upperCoefficient * quotient) quotient).symm
      _ = GaussianInt.Pair.LinearCombination.linearCombination lower upper
          (candidateCoefficient - upperCoefficient * quotient) quotient := by
        rw [upperExpansion']
  · have complementCoefficientNotDivisible :
        ¬ GaussianInt.Divisibility.Basic.Divides determinantValue
          candidateComplementCoefficient :=
      (GaussianInt.Divisibility.NormTwo.not_divides_iff_coordinateOdd_of_norm_two
        determinantNorm).mpr complementOdd
    right
    change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue leftCoefficient ∧
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue rightCoefficient ∧
      GaussianInt.Pair.LinearCombination.scalePair determinantValue candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient
    refine ⟨determinantValue * candidateCoefficient -
        upperCoefficient * candidateComplementCoefficient,
      candidateComplementCoefficient, ?_,
      complementCoefficientNotDivisible, ?_⟩
    · intro leftDivisible
      have productNotDivisible :=
        GaussianInt.Divisibility.NormTwo.not_divides_mul_of_norm_two
          determinantNorm upperCoefficientNotDivisible
            complementCoefficientNotDivisible
      apply productNotDivisible
      rcases leftDivisible with ⟨quotient, leftIdentity⟩
      refine ⟨candidateCoefficient - quotient, ?_⟩
      have recoverProduct :
          upperCoefficient * candidateComplementCoefficient =
            determinantValue * candidateCoefficient -
              (determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.sub_re,
            GaussianInt.sub_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im, -eq_self, -iff_self] <;>
          ring1
      have factorDifference :
          determinantValue * candidateCoefficient -
              determinantValue * quotient =
            determinantValue * (candidateCoefficient - quotient) := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.sub_re,
            GaussianInt.sub_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im, -eq_self, -iff_self] <;>
          ring1
      calc
        upperCoefficient * candidateComplementCoefficient =
            determinantValue * candidateCoefficient -
              (determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) :=
          recoverProduct
        _ = determinantValue * candidateCoefficient -
              determinantValue * quotient := by rw [leftIdentity]
        _ = determinantValue * (candidateCoefficient - quotient) :=
          factorDifference
    · calc
        GaussianInt.Pair.LinearCombination.scalePair determinantValue candidate =
            GaussianInt.Pair.LinearCombination.scalePair determinantValue
              (GaussianInt.Pair.LinearCombination.linearCombination lower complement candidateCoefficient
                candidateComplementCoefficient) :=
          congrArg (GaussianInt.Pair.LinearCombination.scalePair determinantValue) candidateExpansion'.symm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (determinantValue * candidateCoefficient)
            (determinantValue * candidateComplementCoefficient) :=
          (GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            determinantValue candidateCoefficient
              candidateComplementCoefficient).symm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            ((determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) +
              candidateComplementCoefficient * upperCoefficient)
            (candidateComplementCoefficient * determinantValue) := by
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.sub_re,
              GaussianInt.sub_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement upperCoefficient
              determinantValue)
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient :=
          (GaussianInt.Pair.LinearCombination.linearCombination_nested_right lower complement upperCoefficient
            determinantValue
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient).symm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower upper
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient := by rw [upperExpansion']

/-- Conversely, any two cleared coefficients in the nondivisible class give
an ambient pair in the centered coset.  The witness is computed in the Bezout
basis of `lower`. -/
theorem
  IsBest.exists_centeredCoefficientPair_of_index_two
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source lower) (upperBest : Best.Basic.IsBest source upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient : GaussianInt)
    (leftNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) leftCoefficient)
    (rightNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) rightCoefficient) :
    ∃ candidate : GaussianInt.Pair.Basic.ConvergentPair,
      GaussianInt.Pair.LinearCombination.scalePair (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower
        upper) candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  let upperCoefficient := bezoutBasisFirstCoefficient lower upper
  have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
    simpa only [determinantValue, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
      using indexTwo
  have upperCoefficientNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue upperCoefficient := by
    simpa only [determinantValue, upperCoefficient, -eq_self, -iff_self] using
      (Best.Consecutive.Index.IsBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two lowerBest)
        upperBest indexTwo
  have productNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue
        (upperCoefficient * rightCoefficient) :=
    GaussianInt.Divisibility.NormTwo.not_divides_mul_of_norm_two
      determinantNorm upperCoefficientNotDivisible rightNotDivisible
  have coefficientSumDivisible :=
    GaussianInt.Divisibility.NormTwo.divides_add_of_not_divides_of_norm_two
      determinantNorm leftNotDivisible productNotDivisible
  rcases coefficientSumDivisible with ⟨quotient, coefficientIdentity⟩
  let candidate := GaussianInt.Pair.LinearCombination.linearCombination lower complement quotient rightCoefficient
  refine ⟨candidate, ?_⟩
  have upperExpansion := (Best.Consecutive.Index.IsBest.linearCombination_bezoutBasis lowerBest) upper
  have upperExpansion' :
      GaussianInt.Pair.LinearCombination.linearCombination lower complement upperCoefficient determinantValue =
        upper := by
    simpa only [complement, upperCoefficient, determinantValue, -eq_self, -iff_self] using
      upperExpansion
  change GaussianInt.Pair.LinearCombination.scalePair determinantValue candidate =
    GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient
  calc
    GaussianInt.Pair.LinearCombination.scalePair determinantValue candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower complement
          (determinantValue * quotient)
          (determinantValue * rightCoefficient) :=
      (GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
        determinantValue quotient rightCoefficient).symm
    _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
        (leftCoefficient + rightCoefficient * upperCoefficient)
        (rightCoefficient * determinantValue) := by
      rw [← coefficientIdentity]
      apply GaussianInt.Pair.LinearCombination.pair_ext <;>
        apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.linearCombination,
          GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im, -eq_self, -iff_self] <;>
        ring1
    _ = GaussianInt.Pair.LinearCombination.linearCombination lower
        (GaussianInt.Pair.LinearCombination.linearCombination lower complement upperCoefficient
          determinantValue)
        leftCoefficient rightCoefficient :=
      (GaussianInt.Pair.LinearCombination.linearCombination_nested_right lower complement upperCoefficient
        determinantValue leftCoefficient rightCoefficient).symm
    _ = GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient := by
      rw [upperExpansion']

/-- Put an arbitrary second pair into a nearest-remainder normal form relative
to the explicit Bezout basis completed from a best first pair.  The returned
coefficient has at most half the determinant quadrance. -/
theorem IsBest.exists_reducedCoefficientBasis
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source lower)
    (determinantNonzero : GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper ≠ 0) :
    ∃ coefficient : GaussianInt, ∃ complement : GaussianInt.Pair.Basic.ConvergentPair,
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) ∧
      2 * GaussianInt.normNat coefficient ≤ GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ∧
      (4 ≤ GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper →
        2 * (GaussianInt.normNat coefficient + 1) ≤
            GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ∨
          ∃ factor : GaussianInt,
            GaussianInt.normNat factor = 2 ∧
              GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper = coefficient * factor) := by
  let basisComplement := bezoutComplement lower
  let firstCoefficient := bezoutBasisFirstCoefficient lower upper
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let quotientFraction : GaussianInt.Fraction :=
    { numerator := firstCoefficient
      denominator := determinantValue
      denominatorNonzero := determinantNonzero }
  let quotient := GaussianInt.Division.Nearest.digit quotientFraction
  let coefficient := GaussianInt.Division.Nearest.remainder quotientFraction
  let adjustedComplement :=
    GaussianInt.Pair.LinearCombination.linearCombination lower basisComplement quotient 1
  refine ⟨coefficient, adjustedComplement, ?_, ?_, ?_⟩
  · have basisExpansion := (Best.Consecutive.Index.IsBest.linearCombination_bezoutBasis best) upper
    have division :=
      GaussianInt.Division.Nearest.digit_mul_denominator_add_remainder quotientFraction
    dsimp only [quotientFraction, firstCoefficient, determinantValue,
      quotient, coefficient, -eq_self, -iff_self] at division
    have firstIdentity :
        firstCoefficient = coefficient + determinantValue * quotient := by
      calc
        firstCoefficient = quotient * determinantValue + coefficient :=
          division.symm
        _ = coefficient + determinantValue * quotient := by
          apply GaussianInt.ext <;>
            simp only [GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
    calc
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower basisComplement firstCoefficient
          determinantValue := basisExpansion.symm
      _ = GaussianInt.Pair.LinearCombination.linearCombination lower adjustedComplement coefficient
          determinantValue := by
        rw [firstIdentity]
        apply GaussianInt.Pair.LinearCombination.pair_ext <;>
          apply GaussianInt.ext <;>
          simp only [GaussianInt.Pair.LinearCombination.linearCombination, adjustedComplement,
            GaussianInt.add_re,
            GaussianInt.add_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im,
            GaussianInt.one_re,
            GaussianInt.one_im, -eq_self, -iff_self] <;>
          ring1
  · simpa only [coefficient, quotientFraction, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance,
      determinantValue, -eq_self, -iff_self] using
      GaussianInt.Division.Nearest.twice_remainder_norm_le_denominator quotientFraction
  · intro indexAtLeastFour
    simpa only [coefficient, quotientFraction, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance,
      determinantValue, -eq_self, -iff_self] using
      GaussianInt.Division.NearestGeometry.remainder_clearance_or_diagonal_factor
        quotientFraction indexAtLeastFour

/-- A unit-coefficient normal form with determinant quadrance at least four
exhibits its complement inside the mixed cylinder.  This is the exact finite
calculation used to exclude the quadrance-four and quadrance-five index
cases. -/
theorem
  AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
    {source : Gaussian.Basic.Canonical} {lower upper complement : GaussianInt.Pair.Basic.ConvergentPair}
    {coefficient : GaussianInt}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper)
    (normalForm :
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper))
    (clearance :
      2 * (GaussianInt.normNat coefficient + 1) ≤
        GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper) :
    GaussianInt.Pair.LinearCombination.PairNonzero complement ∧
      Best.Consecutive.Basic.InOpenMixedCylinder source lower upper complement := open Purelib.Data.Rat in by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let indexValue := GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper
  have upperErrorSmaller :
      Best.Error.errorQuadrance source upper < Best.Error.errorQuadrance source lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have denominatorOrdered :
      Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper :=
    consecutive.2.2.1
  have coefficientNonzero : coefficient ≠ 0 := by
    intro coefficientZero
    have scaled :
        upper = GaussianInt.Pair.LinearCombination.scalePair determinantValue
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientZero]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.zero_re,
              GaussianInt.zero_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.scalePair determinantValue
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) :=
          GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    change GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1 at determinantUnit
    rw [coefficientZero] at clearance
    change 2 * (GaussianInt.normNat (0 : GaussianInt) + 1) ≤
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper at clearance
    have zeroNorm : GaussianInt.normNat (0 : GaussianInt) = 0 := rfl
    rw [zeroNorm] at clearance
    rw [determinantUnit] at clearance
    exact ((show ¬2 * (0 + 1) ≤ 1 by decide) clearance).elim
  have denominatorIdentity :=
    congrArg (fun pair : GaussianInt.Pair.Basic.ConvergentPair => pair.denominator) normalForm
  simp only [GaussianInt.Pair.LinearCombination.linearCombination, -eq_self, -iff_self] at denominatorIdentity
  have complementNonzero : GaussianInt.Pair.LinearCombination.PairNonzero complement := by
    apply (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair complement).mpr
    intro complementZero
    have scaled : upper = GaussianInt.Pair.LinearCombination.scalePair coefficient lower := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.scalePair coefficient lower := by
          rw [complementZero]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.Pair.LinearCombination.scalePair, GaussianInt.Pair.LinearCombination.zeroPair,
              GaussianInt.zero_re,
              GaussianInt.zero_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
    have coefficientUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    have denominatorEqual := congrArg Best.Error.denominatorQuadrance scaled
    rw [Best.Error.denominatorQuadrance_scalePair, coefficientUnit, Nat.one_mul]
        at denominatorEqual
    exact (Nat.ne_of_lt denominatorOrdered) denominatorEqual.symm
  have errorIdentity := congrArg (Best.Error.error source) normalForm
  rw [Best.Error.error_linearCombination] at errorIdentity
  have scaledErrorIdentity :
      GaussianInt.toGaussian determinantValue * Best.Error.error source complement =
        Best.Error.error source upper - GaussianInt.toGaussian coefficient * Best.Error.error source lower := by
    calc
      GaussianInt.toGaussian determinantValue * Best.Error.error source complement =
          (GaussianInt.toGaussian coefficient * Best.Error.error source lower +
              GaussianInt.toGaussian determinantValue * Best.Error.error source complement) -
            GaussianInt.toGaussian coefficient * Best.Error.error source lower := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, -eq_self, -iff_self] <;>
          ring1
      _ = Best.Error.error source upper -
          GaussianInt.toGaussian coefficient * Best.Error.error source lower :=
        congrArg
          (fun value => value -
            GaussianInt.toGaussian coefficient * Best.Error.error source lower)
          errorIdentity.symm
  have errorDifferenceBound :
      Data.Gaussian.Norm.Basic.normSq
          (Best.Error.error source upper - GaussianInt.toGaussian coefficient * Best.Error.error source lower) ≤
        2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := by
    calc
      Data.Gaussian.Norm.Basic.normSq
          (Best.Error.error source upper - GaussianInt.toGaussian coefficient * Best.Error.error source lower) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (Best.Error.error source upper) +
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian coefficient * Best.Error.error source lower)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ = 2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := by
        rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
        unfold Best.Error.errorQuadrance
        ring1
  have scaledErrorBound :
      (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source complement ≤
        2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := by
    calc
      (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source complement =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian determinantValue) *
            Data.Gaussian.Norm.Basic.normSq (Best.Error.error source complement) := by
        rw [GaussianInt.normSq_toGaussian]
        rfl
      _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian determinantValue * Best.Error.error source
        complement) :=
        (Gaussian.Norm.Basic.normSq_mul _ _).symm
      _ = Data.Gaussian.Norm.Basic.normSq
          (Best.Error.error source upper - GaussianInt.toGaussian coefficient * Best.Error.error source lower) :=
        congrArg Data.Gaussian.Norm.Basic.normSq scaledErrorIdentity
      _ ≤ 2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) := errorDifferenceBound
  have errorInteriorStrict :
      2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) <
        2 * ((GaussianInt.normNat coefficient : Fraction.Rational) + 1) *
          Best.Error.errorQuadrance source lower := by
    have sumStrict :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        upperErrorSmaller
          ((GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower)
    have scaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Fraction.Rational) < 2 by decide) sumStrict
    calc
      2 * (Best.Error.errorQuadrance source upper +
          (GaussianInt.normNat coefficient : Fraction.Rational) *
            Best.Error.errorQuadrance source lower) <
          2 * (Best.Error.errorQuadrance source lower +
            (GaussianInt.normNat coefficient : Fraction.Rational) *
              Best.Error.errorQuadrance source lower) := scaled
      _ = 2 * ((GaussianInt.normNat coefficient : Fraction.Rational) + 1) *
          Best.Error.errorQuadrance source lower := by ring1
  have clearanceErrorLeIndexError :
      2 * ((GaussianInt.normNat coefficient : Fraction.Rational) + 1) *
          Best.Error.errorQuadrance source lower ≤
        (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source lower := by
    have castClearance :
        ((2 * (GaussianInt.normNat coefficient + 1) : Nat) : Fraction.Rational) ≤
          (indexValue : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_le_direct clearance
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        castClearance (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source lower))
    calc
      2 * ((GaussianInt.normNat coefficient : Fraction.Rational) + 1) *
          Best.Error.errorQuadrance source lower =
          ((2 * (GaussianInt.normNat coefficient + 1) : Nat) : Fraction.Rational) *
            Best.Error.errorQuadrance source lower := by
        rw [Algebra.NatCast.mul, Algebra.NatCast.add, Nat.cast_ofNat, Nat.cast_one]
      _ ≤ (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source lower := scaled
  have errorScaledStrict :
      (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source complement <
        (indexValue : Fraction.Rational) * Best.Error.errorQuadrance source lower :=
    scaledErrorBound.trans_lt
      (errorInteriorStrict.trans_le clearanceErrorLeIndexError)
  have indexPositive : (0 : Fraction.Rational) < (indexValue : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      ((Nat.mul_pos (by decide) (Nat.zero_lt_succ (GaussianInt.normNat coefficient))).trans_le
        clearance)
  have complementErrorSmaller :
      Best.Error.errorQuadrance source complement < Best.Error.errorQuadrance source lower := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := (indexValue : Fraction.Rational))
    · simpa only [_root_.mul_comm, -eq_self, -iff_self] using errorScaledStrict
    · exact indexPositive
  have scaledDenominatorIdentity :
      determinantValue * complement.denominator =
        upper.denominator - coefficient * lower.denominator := by
    calc
      determinantValue * complement.denominator =
          (coefficient * lower.denominator +
              determinantValue * complement.denominator) -
            coefficient * lower.denominator := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.add_re,
            GaussianInt.add_im,
            GaussianInt.sub_re,
            GaussianInt.sub_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im, -eq_self, -iff_self] <;>
          ring1
      _ = upper.denominator - coefficient * lower.denominator :=
        congrArg (fun value => value - coefficient * lower.denominator)
          denominatorIdentity.symm
  have denominatorDifferenceBound :
      GaussianInt.normNat (upper.denominator - coefficient * lower.denominator) ≤
        2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) := by
    calc
      GaussianInt.normNat (upper.denominator - coefficient * lower.denominator) ≤
          2 * (GaussianInt.normNat upper.denominator +
            GaussianInt.normNat (coefficient * lower.denominator)) :=
        by
          have bound := GaussianInt.Norm.Bounds.normNat_add_le_two
            (upper.denominator) (-(coefficient * lower.denominator))
          rw [← GaussianInt.sub_eq_add_neg, GaussianInt.normNat_neg] at bound
          exact bound
      _ = 2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) := by
        rw [GaussianInt.normNat_mul]
        rfl
  have scaledDenominatorBound :
      indexValue * Best.Error.denominatorQuadrance complement ≤
        2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) := by
    calc
      indexValue * Best.Error.denominatorQuadrance complement =
          GaussianInt.normNat (determinantValue * complement.denominator) := by
        rw [GaussianInt.normNat_mul]
        rfl
      _ = GaussianInt.normNat (upper.denominator - coefficient * lower.denominator) :=
        congrArg GaussianInt.normNat scaledDenominatorIdentity
      _ ≤ 2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) :=
        denominatorDifferenceBound
  have coefficientNormPositive : 0 < GaussianInt.normNat coefficient :=
    GaussianInt.normNat_pos coefficientNonzero
  have coefficientDenominatorStrict :
      GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower <
        GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance upper :=
    Nat.mul_lt_mul_of_pos_left denominatorOrdered coefficientNormPositive
  have denominatorInteriorStrict :
      2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) <
        2 * (GaussianInt.normNat coefficient + 1) *
          Best.Error.denominatorQuadrance upper := by
    calc
      2 * (Best.Error.denominatorQuadrance upper +
          GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance lower) <
          2 * (Best.Error.denominatorQuadrance upper +
            GaussianInt.normNat coefficient * Best.Error.denominatorQuadrance upper) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.add_lt_add_left coefficientDenominatorStrict _)
          (by decide)
      _ = 2 * (GaussianInt.normNat coefficient + 1) *
          Best.Error.denominatorQuadrance upper := by
        ring1
  have clearanceDenominatorLeIndexDenominator :
      2 * (GaussianInt.normNat coefficient + 1) * Best.Error.denominatorQuadrance upper ≤
        indexValue * Best.Error.denominatorQuadrance upper :=
    Nat.mul_le_mul_right (Best.Error.denominatorQuadrance upper) clearance
  have denominatorScaledStrict :
      indexValue * Best.Error.denominatorQuadrance complement <
        indexValue * Best.Error.denominatorQuadrance upper :=
    scaledDenominatorBound.trans_lt
      (denominatorInteriorStrict.trans_le
        clearanceDenominatorLeIndexDenominator)
  exact ⟨complementNonzero,
    complementErrorSmaller,
    Nat.Order.lt_of_mul_lt_mul_left denominatorScaledStrict⟩

/-- A unit-coefficient normal form of index at least four places its nonzero complement inside the mixed cylinder.

The two best pairs retain their original strictly ordered denominator levels. -/
theorem
  AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm
    {source : Gaussian.Basic.Canonical} {lower upper complement : GaussianInt.Pair.Basic.ConvergentPair}
    {coefficient : GaussianInt}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source lower upper)
    (normalForm :
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper))
    (coefficientUnit : GaussianInt.normNat coefficient = 1)
    (indexAtLeastFour : 4 ≤ GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper) :
    GaussianInt.Pair.LinearCombination.PairNonzero complement ∧
      Best.Consecutive.Basic.InOpenMixedCylinder source lower upper complement := by
  apply (Best.Consecutive.Index.AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
    consecutive)
    normalForm
  rw [coefficientUnit]
  exact indexAtLeastFour

/-- The determinant quadrance of consecutive best pairs cannot be four. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_ne_four
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≠ 4 := by
  intro indexFour
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, coefficientBound, _⟩ :=
    (Best.Consecutive.Index.IsBest.exists_reducedCoefficientBasis consecutive.1) determinantNonzero
  have coefficientSmall : GaussianInt.normNat coefficient < 4 := by
    apply Nat.Order.lt_of_mul_lt_mul_left
    exact coefficientBound.trans_lt (indexFour.trans_lt (by decide))
  rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
      coefficient coefficientSmall with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientEqZero :=
      GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero coefficientZero
    have scaled :
        upper = GaussianInt.Pair.LinearCombination.scalePair determinantValue
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientEqZero]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.zero_re,
              GaussianInt.zero_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.scalePair determinantValue
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) :=
          GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    have determinantNorm : GaussianInt.normNat determinantValue = 4 := indexFour
    rw [determinantUnit] at determinantNorm
    exact (by decide : (1 : Nat) ≠ 4) determinantNorm
  · have witness :=
      (Best.Consecutive.Index.AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm consecutive)
        normalForm coefficientUnit indexFour.ge
    have cylinderEmpty :=
      (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · have coefficientIsDiagonal :=
      GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two coefficientDiagonal
    have determinantNorm : GaussianInt.normNat determinantValue = 4 := indexFour
    obtain ⟨factor, _, determinantFactor⟩ :=
      GaussianInt.Norm.Small.exists_diagonal_right_factor_of_four_and_diagonal
        determinantNorm coefficientIsDiagonal
    have scaled :
        upper = GaussianInt.Pair.LinearCombination.scalePair coefficient
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement 1 factor) := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (coefficient * 1) (coefficient * factor) := by
          rw [determinantFactor]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.scalePair coefficient
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement 1 factor) :=
          GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            coefficient 1 factor
    have coefficientMustBeUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    rw [coefficientDiagonal] at coefficientMustBeUnit
    exact (by decide : (2 : Nat) ≠ 1) coefficientMustBeUnit

/-- The determinant quadrance of consecutive best pairs cannot be five. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_ne_five
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≠ 5 := by
  intro indexFive
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, coefficientBound, _⟩ :=
    (Best.Consecutive.Index.IsBest.exists_reducedCoefficientBasis consecutive.1) determinantNonzero
  have coefficientSmall : GaussianInt.normNat coefficient < 4 := by
    apply Nat.Order.lt_of_mul_lt_mul_left
    exact coefficientBound.trans_lt (indexFive.trans_lt (by decide))
  rcases GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
      coefficient coefficientSmall with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientEqZero :=
      GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero coefficientZero
    have scaled :
        upper = GaussianInt.Pair.LinearCombination.scalePair determinantValue
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientEqZero]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.zero_re,
              GaussianInt.zero_im,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.scalePair determinantValue
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement 0 1) :=
          GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    have determinantNorm : GaussianInt.normNat determinantValue = 5 := indexFive
    rw [determinantUnit] at determinantNorm
    exact (by decide : (1 : Nat) ≠ 5) determinantNorm
  · have witness :=
      (Best.Consecutive.Index.AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm consecutive)
        normalForm coefficientUnit
          (indexFive.symm ▸ (show 4 ≤ 5 by decide))
    have cylinderEmpty :=
      (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · have determinantNorm : GaussianInt.normNat determinantValue = 5 := indexFive
    obtain ⟨unit, shift, unitNorm, coefficientShift⟩ :=
      GaussianInt.Norm.Small.exists_unit_shift_of_norm_five_and_two determinantNorm
        coefficientDiagonal
    let adjustedComplement :=
      GaussianInt.Pair.LinearCombination.linearCombination lower complement shift 1
    have adjustedNormalForm :
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower adjustedComplement unit
          determinantValue := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (unit + determinantValue * shift) determinantValue := by
          rw [coefficientShift]
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower adjustedComplement unit
            determinantValue := by
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination, adjustedComplement,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
    have witness :=
      (Best.Consecutive.Index.AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm consecutive)
        adjustedNormalForm unitNorm
          (indexFive.symm ▸ (show 4 ≤ 5 by decide))
    have cylinderEmpty :=
      (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty adjustedComplement witness.1 witness.2

/-- Consecutive best pairs have determinant quadrance at most two.  The proof
uses only the computed Bezout basis, one nearest Gaussian remainder, the
half-open-square boundary calculation, and the empty mixed cylinder. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_le_two
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤ 2 := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  let indexValue := GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper
  have indexPositive := consecutive.coefficientIndexQuadrance_pos
  apply Nat.le_of_not_gt
  intro indexGreaterThanTwo
  have indexAtLeastFour : 4 ≤ indexValue := by
    apply Nat.le_of_not_gt
    intro indexBelowFour
    have cases :=
      GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
        determinantValue indexBelowFour
    change GaussianInt.normNat determinantValue = 0 ∨
      GaussianInt.normNat determinantValue = 1 ∨ GaussianInt.normNat determinantValue = 2 at cases
    change 0 < GaussianInt.normNat determinantValue at indexPositive
    change 2 < GaussianInt.normNat determinantValue at indexGreaterThanTwo
    rcases cases with zero | one | two
    · rw [zero] at indexPositive
      exact (Nat.not_lt_zero 0 indexPositive).elim
    · rw [one] at indexGreaterThanTwo
      exact ((show ¬2 < 1 by decide) indexGreaterThanTwo).elim
    · rw [two] at indexGreaterThanTwo
      exact (Nat.lt_irrefl 2 indexGreaterThanTwo).elim
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, _, boundaryAlternative⟩ :=
    (Best.Consecutive.Index.IsBest.exists_reducedCoefficientBasis consecutive.1) determinantNonzero
  rcases boundaryAlternative indexAtLeastFour with clearance | factorCase
  · have witness :=
      (Best.Consecutive.Index.AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
        consecutive)
        normalForm clearance
    have cylinderEmpty :=
      (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · obtain ⟨factor, factorNorm, determinantFactor⟩ := factorCase
    have determinantFactorValue : determinantValue = coefficient * factor :=
      determinantFactor
    have scaled :
        upper = GaussianInt.Pair.LinearCombination.scalePair coefficient
          (GaussianInt.Pair.LinearCombination.linearCombination lower complement 1 factor) := by
      calc
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower complement
            (coefficient * 1) (coefficient * factor) := by
          rw [determinantFactorValue]
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = GaussianInt.Pair.LinearCombination.scalePair coefficient
            (GaussianInt.Pair.LinearCombination.linearCombination lower complement 1 factor) :=
          GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower complement
            coefficient 1 factor
    have coefficientUnit :=
      (Best.Consecutive.Index.IsBest.scalingCoefficient_norm_eq_one_of_scaled consecutive.2.1) scaled
    have indexEqTwo : indexValue = 2 := by
      calc
        indexValue = GaussianInt.normNat determinantValue := rfl
        _ = GaussianInt.normNat (coefficient * factor) := by rw [determinantFactorValue]
        _ = GaussianInt.normNat coefficient * GaussianInt.normNat factor := GaussianInt.normNat_mul _ _
        _ = 2 := by rw [coefficientUnit, factorNorm]
    change GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2 at indexEqTwo
    rw [indexEqTwo] at indexGreaterThanTwo
    exact (Nat.lt_irrefl 2 indexGreaterThanTwo).elim

/-- Exact sharp index dichotomy for consecutive best pairs. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 1 ∨
      GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2 := by
  have positive := consecutive.coefficientIndexQuadrance_pos
  have upperBound := (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
  let index := GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper
  change 0 < index at positive
  change index ≤ 2 at upperBound
  change index = 1 ∨ index = 2
  by_cases indexOne : index = 1
  · exact Or.inl indexOne
  · have twoLe : 2 ≤ index :=
      Nat.lt_of_le_of_ne positive (Ne.symm indexOne)
    exact Or.inr (Nat.le_antisymm upperBound twoLe)

/-- Exact coefficient-lattice classification for consecutive best pairs.  In
the index-one case every ambient pair has integral coordinates in the two
pairs.  In the index-two case every ambient pair has either integral
coordinates or the displayed centered-coset certificate. -/
theorem
  AreConsecutiveBest.coefficientSpan_or_centeredCoset
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.Pair.LinearCombination.InCoefficientSpan lower upper candidate ∨
      GaussianInt.Pair.LinearCombination.InCenteredCoefficientCoset lower upper candidate := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two consecutive) with
    indexOne | indexTwo
  · left
    let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
    refine ⟨GaussianInt.conj determinantValue * GaussianInt.Pair.LinearCombination.coefficientDeterminant candidate
      upper,
      GaussianInt.conj determinantValue * GaussianInt.Pair.LinearCombination.coefficientDeterminant lower candidate, ?_⟩
    have expansion :=
      GaussianInt.Pair.LinearCombination.linearCombination_cramer_of_index_one lower upper candidate indexOne
    dsimp only at expansion
    exact expansion.symm
  · exact
      (Best.Consecutive.Index.IsBest.inCoefficientSpan_or_inCenteredCoefficientCoset_of_index_two consecutive.1)
        consecutive.2.1 indexTwo candidate

/-- The reverse half of the centered description: in the index-two case any
two nondivisible cleared coefficients determine an ambient displayed pair. -/
theorem
  AreConsecutiveBest.exists_centeredCoefficientPair
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient : GaussianInt)
    (leftNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) leftCoefficient)
    (rightNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) rightCoefficient) :
    ∃ candidate : GaussianInt.Pair.Basic.ConvergentPair,
      GaussianInt.Pair.LinearCombination.scalePair (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower
        upper) candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower upper leftCoefficient rightCoefficient :=
  (Best.Consecutive.Index.IsBest.exists_centeredCoefficientPair_of_index_two consecutive.1)
    consecutive.2.1 indexTwo leftCoefficient rightCoefficient
      leftNotDivisible rightNotDivisible
end Purelib.NumberTheory.Approximation.Best.Consecutive.Index

end
