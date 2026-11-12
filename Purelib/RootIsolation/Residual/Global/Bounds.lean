module

import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Subtraction

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian

/-!
# Coefficient bounds for global residual exclusion

The leading-monomial estimate gives a positive residual threshold outside the
coefficient-computed isolation square. Separate annular and far-field bounds
use the original polynomial, its leading coefficient and the displayed sample.
-/

namespace Purelib.RootIsolation.Residual.Global.Bounds

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.RootIsolation

/-- A point outside the coefficient-computed closed square has larger squared norm.

One of the four endpoint comparisons fails. The corresponding signed
coordinate then exceeds the positive radius, while negation preserves its square. -/
public theorem radiusSq_lt_normSq_of_not_largeSquare_contains
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (sample :
      Gaussian.Basic.Canonical)
    (outside : ¬(Bounds.RootRadius.Box.largeSquareBox p).Contains sample) :
    Bounds.RootRadius.denseLargeSquareRadius p ^ 2 < Gaussian.Norm.Basic.normSq sample := by
  let radius := Bounds.RootRadius.denseLargeSquareRadius p
  have radiusPositive : 0 < radius := Bounds.RootRadius.denseLargeSquareRadius_pos p
  by_cases left : -radius ≤ sample.re
  · by_cases right : sample.re ≤ radius
    · by_cases bottom : -radius ≤ sample.im
      · by_cases top : sample.im ≤ radius
        · exact (outside (by
            change -radius ≤ sample.re ∧ sample.re ≤ radius ∧
              -radius ≤ sample.im ∧ sample.im ≤ radius
            exact ⟨left, right, bottom, top⟩)).elim
        · have beyond : radius < sample.im := lt_of_not_ge top
          change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
          have bound := Bounds.Square.radius_sq_lt_normSq_of_lt radiusPositive beyond
            (x := sample.im) (y := sample.re)
          simpa only [Fraction.Field.add_comm] using bound
      · have beyondNegative : sample.im < -radius := lt_of_not_ge bottom
        have beyond : radius < -sample.im := by
          have negated := Arithmetic.neg_lt_neg_direct
            beyondNegative
          calc
            radius = -(-radius) := by ring1
            _ < -sample.im := negated
        change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
        have bound := Bounds.Square.radius_sq_lt_normSq_of_lt radiusPositive beyond
          (x := -sample.im) (y := sample.re)
        have squareIdentity : (-sample.im) ^ 2 = sample.im ^ 2 := by ring1
        rw [squareIdentity] at bound
        simpa only [Fraction.Field.add_comm] using bound
    · have beyond : radius < sample.re := lt_of_not_ge right
      change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
      exact Bounds.Square.radius_sq_lt_normSq_of_lt radiusPositive beyond
  · have beyondNegative : sample.re < -radius := lt_of_not_ge left
    have beyond : radius < -sample.re := by
      have negated := Arithmetic.neg_lt_neg_direct
        beyondNegative
      calc
        radius = -(-radius) := by ring1
        _ < -sample.re := negated
    change radius ^ 2 < sample.re ^ 2 + sample.im ^ 2
    have bound := Bounds.Square.radius_sq_lt_normSq_of_lt radiusPositive beyond
      (x := -sample.re) (y := sample.im)
    have squareIdentity : (-sample.re) ^ 2 = sample.re ^ 2 := by ring1
    rw [squareIdentity] at bound
    exact bound

/-- Bound the leading monomial on the annulus ending at twice the squared square radius.

The leading coefficient's squared norm multiplies the radius bound raised
to the polynomial's natural degree. -/
@[expose] public def annularLeadingUpper (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) : Fraction.Rational :=
  Gaussian.Norm.Basic.normSq p.leadingCoeff *
    (2 * Bounds.RootRadius.denseLargeSquareRadius p ^ 2) ^ p.natDegree

/-- The annular leading-monomial bound is positive for positive natural degree.

Positive degree supplies a nonzero leading coefficient, and the positive
computed radius makes the remaining natural power positive. -/
public theorem annularLeadingUpper_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    0 < annularLeadingUpper p := by
  have polynomialNonzero := Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingPositive := Gaussian.Norm.Basic.normSq_pos (Dense.Basic.DensePolynomial.leadingCoeff_ne_zero
    polynomialNonzero)
  have radialPositive : 0 < 2 * Bounds.RootRadius.denseLargeSquareRadius p ^ 2 :=
    Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.pow_pos_direct
        (Bounds.RootRadius.denseLargeSquareRadius_pos p) 2)
  exact Arithmetic.mul_pos_direct leadingPositive
    (Arithmetic.pow_pos_direct radialPositive p.natDegree)

/-- Compute the residual threshold excluding samples outside the isolation square.

The minimum retains the far-field dominance margin and the annular gap
quotient with its coefficient-computed leading-monomial denominator. -/
@[expose] public def outsideResidualThreshold (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) : Fraction.Rational :=
  min (Bounds.LeadingDominance.largeSquareDominanceMargin p)
    (Bounds.LeadingDominance.largeSquareDominanceMargin p ^ 2 / (4 *
      annularLeadingUpper p))

/-- The outside-residual threshold is positive for a positive-degree polynomial.

Both entries of the retained minimum are positive: the dominance margin
and its squared quotient by four times the annular leading bound. -/
public theorem outsideResidualThreshold_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    0 < outsideResidualThreshold p := by
  have marginPositive := Bounds.LeadingDominance.largeSquareDominanceMargin_pos degreePositive
  exact Basic.lt_min marginPositive
    (Field.div_pos_direct
      (Arithmetic.pow_pos_direct marginPositive 2)
      (Arithmetic.mul_pos_direct (by decide)
        (annularLeadingUpper_pos degreePositive)))

section
/-- The leading monomial obeys the annular squared-norm bound.

The sample's squared-norm bound is raised to the original natural degree
and scaled by the nonnegative squared norm of the leading coefficient. -/
private theorem leadingNormSq_le_annularUpper
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {sample : Gaussian.Basic.Canonical}
    (normUpper : Gaussian.Norm.Basic.normSq sample ≤ 2 *
      Bounds.RootRadius.denseLargeSquareRadius p ^ 2) :
    Gaussian.Norm.Basic.normSq ((Coefficients.LeadingSplit.leadingMonomial
      p).eval sample) ≤ annularLeadingUpper p := by
  rw [Coefficients.LeadingSplit.leadingMonomial_eval degreePositive, Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Power.normSq_pow]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg sample)
      normUpper p.natDegree)
    (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)
end

/-- The annular dominance gap gives an explicit residual lower bound between one and two squared large-square radii.

The denominator uses the retained annular upper bound for the leading monomial. -/
public theorem outside_residual_lower_annulus
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {sample : Gaussian.Basic.Canonical}
    (normLower : Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Gaussian.Norm.Basic.normSq
      sample)
    (normUpper : Gaussian.Norm.Basic.normSq sample ≤ 2 *
      Bounds.RootRadius.denseLargeSquareRadius p ^ 2) :
    Bounds.LeadingDominance.largeSquareDominanceMargin p ^ 2 / (4 *
      annularLeadingUpper p) ≤
      Gaussian.Norm.Basic.normSq (p.eval sample) := by
  let leading := (Coefficients.LeadingSplit.leadingMonomial p).eval sample
  let lower := (Coefficients.Tail.lowerTermsPolynomial p).eval sample
  let margin := Bounds.LeadingDominance.largeSquareDominanceMargin p
  have marginPositive : 0 < margin :=
    Bounds.LeadingDominance.largeSquareDominanceMargin_pos degreePositive
  have gap : margin ≤ Gaussian.Norm.Basic.normSq leading - Gaussian.Norm.Basic.normSq lower := by
    simpa only [leading, lower, margin] using
      Bounds.LeadingDominance.largeSquare_radial_dominance_margin degreePositive normLower normUpper
  have leadingPositive : 0 < Gaussian.Norm.Basic.normSq leading := by
    have differenceLeLeading : Gaussian.Norm.Basic.normSq leading -
        Gaussian.Norm.Basic.normSq lower ≤
          Gaussian.Norm.Basic.normSq leading := by
      calc
        Gaussian.Norm.Basic.normSq leading -
            Gaussian.Norm.Basic.normSq lower ≤
              Gaussian.Norm.Basic.normSq leading - 0 :=
          Arithmetic.sub_le_sub_left_direct
            (Gaussian.Norm.Basic.normSq_nonneg lower) _
        _ = Gaussian.Norm.Basic.normSq leading := by ring1
    have gapLeLeading : margin ≤ Gaussian.Norm.Basic.normSq leading :=
      gap.trans differenceLeLeading
    exact marginPositive.trans_le gapLeLeading
  have leadingUpper : Gaussian.Norm.Basic.normSq leading ≤ annularLeadingUpper p := by
    simpa only [leading] using
      leadingNormSq_le_annularUpper degreePositive normUpper
  have denominatorOrder : 4 * Gaussian.Norm.Basic.normSq leading ≤
      4 * annularLeadingUpper p :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      leadingUpper (by decide)
  have quotientOrder : margin ^ 2 / (4 * annularLeadingUpper p) ≤
      margin ^ 2 / (4 * Gaussian.Norm.Basic.normSq leading) :=
    Field.div_le_div_of_nonneg_left_direct
      (Arithmetic.pow_nonneg_direct marginPositive.le 2)
      (Arithmetic.mul_pos_direct (by decide) leadingPositive)
      denominatorOrder
  have sumLower := Gaussian.Norm.Bounds.normSq_add_lower_of_gap marginPositive gap
  calc
    margin ^ 2 / (4 * annularLeadingUpper p) ≤
        margin ^ 2 / (4 * Gaussian.Norm.Basic.normSq leading) := quotientOrder
    _ ≤ Gaussian.Norm.Basic.normSq (leading + lower) := sumLower
    _ = Gaussian.Norm.Basic.normSq (p.eval sample) := by
      rw [Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eval degreePositive]

/-- Beyond twice the squared large-square radius, the polynomial's squared residual norm exceeds its computed dominance
margin.

The finite leading-term estimate assumes natural degree at least two. -/
public theorem outside_residual_lower_far
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreeAtLeastTwo : 2 ≤
      p.natDegree)
    {sample : Gaussian.Basic.Canonical}
    (normLower : 2 * Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Gaussian.Norm.Basic.normSq
      sample) :
    Bounds.LeadingDominance.largeSquareDominanceMargin p ≤ Gaussian.Norm.Basic.normSq (p.eval
      sample) := by
  let radiusSq := Bounds.RootRadius.denseLargeSquareRadius p ^ 2
  let sampleSq := Gaussian.Norm.Basic.normSq sample
  let leadingNorm := Gaussian.Norm.Basic.normSq p.leadingCoeff
  let weight := Bounds.RootRadius.denseLowerCoefficientWeight p
  let exponent := p.natDegree - 1
  let half : Fraction.Rational := (2 : Fraction.Rational)⁻¹
  let leading := (Coefficients.LeadingSplit.leadingMonomial p).eval sample
  let lower := (Coefficients.Tail.lowerTermsPolynomial p).eval sample
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    exact Arithmetic.pow_pos_direct
      (Bounds.RootRadius.denseLargeSquareRadius_pos p) 2
  have oneLeRadiusSq : (1 : Fraction.Rational) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact Arithmetic.mul_le_mul_direct
      (Bounds.RootRadius.one_le_denseLargeSquareRadius p)
        (Bounds.RootRadius.one_le_denseLargeSquareRadius p)
      (by decide) (Bounds.RootRadius.denseLargeSquareRadius_pos p).le
  have radiusLeTwice : radiusSq ≤ 2 * radiusSq := by
    calc
      radiusSq = 1 * radiusSq := by ring1
      _ ≤ 2 * radiusSq :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Fraction.Rational) ≤ 2 by decide) radiusSqPositive.le
  have radiusSqLeSample : radiusSq ≤ sampleSq := by
    exact radiusLeTwice.trans (by
      simpa only [radiusSq, sampleSq] using normLower)
  have oneLeSample : (1 : Fraction.Rational) ≤ sampleSq :=
    oneLeRadiusSq.trans radiusSqLeSample
  have sampleNonnegative : 0 ≤ sampleSq := oneLeSample.trans' (by decide)
  have sampleUpper : sampleSq ≤ 2 * sampleSq := by
    simpa only [Fraction.Field.one_mul] using
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 : Fraction.Rational) ≤ 2 by decide) sampleNonnegative)
  have lowerBound : Gaussian.Norm.Basic.normSq lower ≤ weight * sampleSq ^ exponent := by
    simpa only [lower, weight, sampleSq, exponent] using
      Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive sampleUpper oneLeSample
  have halfSample : radiusSq ≤ sampleSq / 2 := by
    apply (Field.le_div_iff_pos
      (show (0 : Fraction.Rational) < 2 by decide)).2
    simpa only [radiusSq, sampleSq,
      Fraction.Field.mul_comm] using normLower
  have coefficientOrder : leadingNorm * radiusSq - weight ≤
      leadingNorm * (sampleSq / 2) - weight := by
    exact Arithmetic.sub_le_sub_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        halfSample (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)) weight
  have coefficientPositive : 0 < leadingNorm * radiusSq - weight := by
    dsimp only [leadingNorm, radiusSq, weight]
    exact Arithmetic.sub_pos_direct
      (Bounds.LeadingDominance.denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive)
  have powerOrder : radiusSq ^ exponent ≤ sampleSq ^ exponent :=
    Arithmetic.pow_le_pow_direct radiusSqPositive.le
      radiusSqLeSample exponent
  have scaledCoefficient :
      (leadingNorm * radiusSq - weight) * radiusSq ^ exponent ≤
        (leadingNorm * (sampleSq / 2) - weight) * sampleSq ^ exponent :=
    Arithmetic.mul_le_mul_direct coefficientOrder powerOrder
      (Arithmetic.pow_nonneg_direct radiusSqPositive.le
        exponent)
      (coefficientPositive.trans_le coefficientOrder).le
  have degreeIdentity : exponent + 1 = p.natDegree := by
    dsimp only [exponent]
    exact (Nat.add_comm _ _).trans
      (Data.Nat.Subtraction.add_sub_of_le degreePositive)
  have leadingIdentity : Gaussian.Norm.Basic.normSq leading =
      leadingNorm * sampleSq ^ p.natDegree := by
    dsimp only [leading, leadingNorm, sampleSq]
    rw [Coefficients.LeadingSplit.leadingMonomial_eval degreePositive, Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow]
  have marginToHalfDifference : Bounds.LeadingDominance.largeSquareDominanceMargin p ≤
      Gaussian.Norm.Basic.normSq leading / 2 - Gaussian.Norm.Basic.normSq lower := by
    calc
      Bounds.LeadingDominance.largeSquareDominanceMargin p =
          (leadingNorm * radiusSq - weight) * radiusSq ^ exponent := by
        rfl
      _ ≤ (leadingNorm * (sampleSq / 2) - weight) *
          sampleSq ^ exponent := scaledCoefficient
      _ = (leadingNorm * sampleSq ^ p.natDegree) / 2 -
          weight * sampleSq ^ exponent := by
        rw [← degreeIdentity, pow_succ]
        change (leadingNorm * (sampleSq * half) - weight) *
            sampleSq ^ exponent =
          (leadingNorm * (sampleSq ^ exponent * sampleSq)) * half -
            weight * sampleSq ^ exponent
        exact Fraction.Field.weighted_scale_identity leadingNorm sampleSq weight half exponent
      _ = Gaussian.Norm.Basic.normSq leading / 2 - weight * sampleSq ^ exponent := by
        rw [leadingIdentity]
      _ ≤ Gaussian.Norm.Basic.normSq leading / 2 - Gaussian.Norm.Basic.normSq lower :=
        Arithmetic.sub_le_sub_left_direct lowerBound _
  have sumLower := Gaussian.Norm.Bounds.half_normSq_sub_le_normSq_sub leading (-lower)
  have normalizedSum : leading - -lower = p.eval sample := by
    calc
      leading - -lower = leading + lower := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
            Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
          ring1
      _ = p.eval sample := Coefficients.LeadingSplit.leadingMonomial_add_lowerTerms_eval
        degreePositive sample
  calc
    Bounds.LeadingDominance.largeSquareDominanceMargin p ≤
        Gaussian.Norm.Basic.normSq leading / 2 - Gaussian.Norm.Basic.normSq lower :=
          marginToHalfDifference
    _ = Gaussian.Norm.Basic.normSq leading / 2 - Gaussian.Norm.Basic.normSq (-lower) := by
      rw [Gaussian.Norm.Basic.normSq_neg]
    _ ≤ Gaussian.Norm.Basic.normSq (leading - -lower) := sumLower
    _ = Gaussian.Norm.Basic.normSq (p.eval sample) := by rw [normalizedSum]

/-- A sample outside the large square has residual above the exclusion threshold.

The sample's squared norm selects the annular or far-field estimate; the
retained minimum lies below the matching lower bound in either case. -/
public theorem outsideResidualThreshold_le
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreeAtLeastTwo : 2 ≤
      p.natDegree)
    (sample : Gaussian.Basic.Canonical) (outside : ¬(Bounds.RootRadius.Box.largeSquareBox p).Contains
      sample) :
    outsideResidualThreshold p ≤ Gaussian.Norm.Basic.normSq (p.eval sample) := by
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have normLower :=
    (radiusSq_lt_normSq_of_not_largeSquare_contains p sample outside).le
  by_cases annular : Gaussian.Norm.Basic.normSq sample ≤
      2 * Bounds.RootRadius.denseLargeSquareRadius p ^ 2
  · exact (Basic.min_le_right _ _).trans
      (outside_residual_lower_annulus degreePositive normLower annular)
  · have far : 2 * Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Gaussian.Norm.Basic.normSq
      sample :=
      (lt_of_not_ge annular).le
    exact (Basic.min_le_left _ _).trans
      (outside_residual_lower_far degreeAtLeastTwo far)

end Purelib.RootIsolation.Residual.Global.Bounds
