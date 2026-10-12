module

import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.LeadingSplit
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial

/-!
# Quantitative radial dominance of the leading monomial

The retained finite coefficient weights and positive leading norm determine
the original radius and margin formulas on the displayed rational annulus.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance

/-- Cauchy--Schwarz bound for the normalized lower coefficient tail at a
point with a displayed squared-radius upper bound.

Positive degree makes the retained lower coefficient list nonempty.
The point quadrance is at most twice the radial square, which is at least
one; the finite coefficient weight then bounds that exact lower tail. -/
public theorem normSq_lowerTermsPolynomial_eval_le
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian.Basic.Canonical} {radialSq : Fraction.Rational}
    (normUpper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * radialSq) (oneLeRadial : 1 ≤ radialSq) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
      Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
        radialSq ^ (p.natDegree - 1) := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have coefficientLength := Dense.Gaussian.Coefficients.Tail.lowerCoefficients_length polynomialNonzero
  have coefficientsNonempty : Dense.Gaussian.Coefficients.Tail.lowerCoefficients p ≠ [] := by
    intro empty
    rw [empty] at coefficientLength
    simp only [List.length_nil] at coefficientLength
    omega
  have cauchy := Dense.Gaussian.Evaluation.Norm.normSq_evalCoeffs_le
    (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p) z
  have monomialBound := Dense.Gaussian.Evaluation.Norm.Weighted.monomialNormSqSum_le_weighted
    (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p) (Data.Gaussian.Norm.Basic.normSq z) radialSq
      coefficientsNonempty
    (Gaussian.Norm.Basic.normSq_nonneg z) normUpper oneLeRadial
  have scaledMonomial :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      monomialBound
      (Fraction.Cast.Order.natCast_le_direct
        (Nat.zero_le (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p).length))
  change Data.Gaussian.Norm.Basic.normSq (Dense.Basic.DensePolynomial.evalCoeffs z
    (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p)) ≤ _
  calc
    Data.Gaussian.Norm.Basic.normSq (Dense.Basic.DensePolynomial.evalCoeffs z
      (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p)) ≤
        ((Dense.Gaussian.Coefficients.Tail.lowerCoefficients p).length : Fraction.Rational) *
          Dense.Gaussian.Evaluation.Norm.monomialNormSqSum
            (Dense.Gaussian.Coefficients.Tail.lowerCoefficients p) (Data.Gaussian.Norm.Basic.normSq z) := cauchy
    _ ≤ ((Dense.Gaussian.Coefficients.Tail.lowerCoefficients p).length : Fraction.Rational) *
          (Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum (Dense.Gaussian.Coefficients.Tail.lowerCoefficients
            p).reverse 0 *
            radialSq ^ ((Dense.Gaussian.Coefficients.Tail.lowerCoefficients p).length - 1)) :=
      scaledMonomial
    _ = Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
          radialSq ^ (p.natDegree - 1) := by
      rw [coefficientLength]
      unfold Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight
      ring1

/-- A nonnegative lower bound on point quadrance gives the corresponding leading-monomial quadrance bound.

The radial square is nonnegative and no larger than the point quadrance.
Power monotonicity and the nonnegative leading-coefficient quadrance
preserve this bound after multiplication. -/
public theorem normSq_leadingMonomial_eval_lower
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian.Basic.Canonical} {radialSq : Fraction.Rational}
    (radialNonnegative : 0 ≤ radialSq)
    (normLower : radialSq ≤ Data.Gaussian.Norm.Basic.normSq z) :
    Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radialSq ^ p.natDegree ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) := by
  rw [Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial_eval degreePositive, Gaussian.Norm.Basic.normSq_mul,
    Gaussian.Power.normSq_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct
      radialNonnegative normLower p.natDegree)
    (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)

/-- The explicit coefficient weight is strictly smaller than the leading
coefficient norm times the squared computed radius.

Positive degree supplies a positive leading-coefficient quadrance.
The computed radius exceeds the weight divided by that quadrance and is
at least one, giving the strict squared-radius comparison. -/
public theorem denseLowerCoefficientWeight_lt_leading_radiusSq
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p <
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
        := by
  have polynomialNonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero polynomialNonzero
  have leadingPositive := Gaussian.Norm.Basic.normSq_pos leadingNonzero
  let weight := Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p
  let leadingNorm := Data.Gaussian.Norm.Basic.normSq p.leadingCoeff
  let radius := Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p
  have strictStep : weight / leadingNorm < weight / leadingNorm + 1 := by
    have added := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide : (0 : Fraction.Rational) < 1) (weight / leadingNorm)
    calc
      weight / leadingNorm = weight / leadingNorm + 0 := by ring1
      _ < weight / leadingNorm + 1 := added
  have quotientBelow : weight / leadingNorm < radius :=
    strictStep.trans_le (by
      dsimp only [radius, Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius]
      exact Fraction.Order.Basic.le_max_right _ _)
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    quotientBelow leadingPositive
  have weightBelowLinear : weight < leadingNorm * radius := by
    change weight / leadingNorm * leadingNorm < radius * leadingNorm at scaled
    have cancel : weight / leadingNorm * leadingNorm = weight :=
      Fraction.Field.div_mul_cancel_of_ne weight leadingNorm
        leadingPositive.ne'
    rw [cancel, Fraction.Field.mul_comm radius leadingNorm] at scaled
    exact scaled
  have oneLeRadius : (1 : Fraction.Rational) ≤ radius := by
    dsimp only [radius]
    exact Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius p
  have radiusNonnegative : 0 ≤ radius :=
    (by decide : (0 : Fraction.Rational) ≤ 1).trans oneLeRadius
  have radiusLeSquare : radius ≤ radius ^ 2 := by
    rw [pow_two]
    calc
      radius = radius * 1 := by ring1
      _ ≤ radius * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          oneLeRadius radiusNonnegative
  have scaledRadius : leadingNorm * radius ≤ leadingNorm * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLeSquare
      (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)
  exact weightBelowLinear.trans_le scaledRadius

/-- Strict leading-term dominance at every point whose squared norm lies
between the displayed radial square and twice that square.

The point quadrance lies between the computed radius square and twice
that square. The finite tail bound and positive leading-coefficient
estimate give strict dominance at that same point. -/
public theorem largeSquare_radial_dominance
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian.Basic.Canonical}
    (normLower : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z)
    (normUpper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^
      2) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) := by
  let radiusSq := Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
  have radiusPositive := Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p
  have radiusSqPositive : 0 < radiusSq :=
    by
      dsimp only [radiusSq]
      rw [pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        radiusPositive radiusPositive
  have oneLeRadius := Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius p
  have oneLeRadiusSq : (1 : Fraction.Rational) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p *
        Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p :=
        Fraction.Order.Arithmetic.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) radiusPositive.le
  have lowerBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq) (by simpa only [radiusSq] using normUpper)
    oneLeRadiusSq
  have weightStrict := Dense.Gaussian.Bounds.LeadingDominance.denseLowerCoefficientWeight_lt_leading_radiusSq
    degreePositive
  have powerPositive := Fraction.Order.Arithmetic.pow_pos_direct
    radiusSqPositive (p.natDegree - 1)
  have scaledStrict := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (by simpa only [radiusSq] using weightStrict) powerPositive
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have leadingRadial :
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree ≤
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
    Dense.Gaussian.Bounds.LeadingDominance.normSq_leadingMonomial_eval_lower degreePositive radiusSqPositive.le
      (by simpa only [radiusSq] using normLower)
  calc
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
        Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) := lowerBound
    _ < (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := scaledStrict
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
      leadingRadial

/-- Explicit positive gap by which the leading monomial dominates the lower
coefficient tail on the computed large-square boundary.

The coefficient-weight gap is multiplied by the degree-predecessor
radial power. Both factors use the same computed radius and retained
leading coefficient as the radial dominance estimate. -/
@[expose] public def largeSquareDominanceMargin (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Fraction.Rational :=
  (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 -
      Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p) *
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2) ^ (p.natDegree - 1)

/-- The computed leading-term dominance margin is positive for a positive-degree polynomial.

Positive degree makes the coefficient-weight gap strictly positive.
The computed positive radius also makes its retained natural power positive. -/
public theorem largeSquareDominanceMargin_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree) :
    0 < Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p := by
  apply Fraction.Order.Arithmetic.mul_pos_direct
  · exact Fraction.Order.Arithmetic.sub_pos_direct
      (Dense.Gaussian.Bounds.LeadingDominance.denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive)
  · exact Fraction.Order.Arithmetic.pow_pos_direct (by
      rw [pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct
        (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p)
          (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p)) _

/-- Quantitative form of radial dominance, retaining the same finite margin
at every point of the large-square annulus.

The point quadrance lies in the computed square annulus. Its leading
and lower-tail estimates bound their difference by the same positive
coefficient gap and degree-predecessor radial power. -/
public theorem largeSquare_radial_dominance_margin
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian.Basic.Canonical}
    (normLower : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z)
    (normUpper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^
      2) :
    Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) -
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) := by
  let radiusSq := Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct
      (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p)
        (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p)
  have oneLeRadius := Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius p
  have oneLeRadiusSq : (1 : Fraction.Rational) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p *
        Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p :=
        Fraction.Order.Arithmetic.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).le
  have lowerTermsBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have leadingBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_leadingMonomial_eval_lower degreePositive
    radiusSqPositive.le (by simpa only [radiusSq] using normLower)
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have sumBound :
      Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p +
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) := by
    calc
      Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p +
          Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
        Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p +
          Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
            radiusSq ^ (p.natDegree - 1) :=
        add_le_add (le_refl _) lowerTermsBound
      _ = (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq) *
            radiusSq ^ (p.natDegree - 1) := by
        dsimp only [Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin, radiusSq]
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
            (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
            radiusSq ^ (p.natDegree - 1 + 1) := by
        exact congrArg (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * ·)
          (pow_succ radiusSq (p.natDegree - 1)).symm
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
        rw [degreeIdentity]
      _ ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
        leadingBound
  have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
    sumBound (-Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z))
  have lowerReadback :
      (Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p + Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z)) +
        -Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) =
      Dense.Gaussian.Bounds.LeadingDominance.largeSquareDominanceMargin p := by ring1
  have upperReadback :
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) +
        -Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) =
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) -
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) := by
          ring1
  exact lowerReadback ▸ upperReadback ▸ translated

/-! ## A common outer square for several displayed polynomials -/

/-- Any positive symmetric radius at least the coefficient-computed radius
retains strict leading-term dominance on its boundary.

The symmetric radius is at least the coefficient-computed radius.
The displayed point lies in its squared annulus, so the same leading
and lower-tail comparisons apply at that larger radius. -/
public theorem symmetric_radial_dominance_of_denseRadius_le
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius)
    {z : Gaussian.Basic.Canonical}
    (normLower : radius ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z)
    (normUpper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * radius ^ 2) :
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) <
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) := by
  let radiusSq := radius ^ 2
  have radiusPositive : 0 < radius :=
    (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct radiusPositive radiusPositive
  have oneLeRadius : (1 : Fraction.Rational) ≤ radius :=
    (Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius p).trans radiusLe
  have oneLeRadiusSq : (1 : Fraction.Rational) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ radius * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) radiusPositive.le
  have lowerBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have denseSquareLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ radiusSq := by
    exact Fraction.Order.Arithmetic.pow_le_pow_direct
      (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).le radiusLe 2
  have leadingScaled :
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
        ≤
        Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denseSquareLe
      (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)
  have weightStrict : Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p <
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq :=
    (Dense.Gaussian.Bounds.LeadingDominance.denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive).trans_le
      leadingScaled
  have powerPositive := Fraction.Order.Arithmetic.pow_pos_direct
    radiusSqPositive (p.natDegree - 1)
  have scaledStrict := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    weightStrict powerPositive
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have leadingRadial :
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree ≤
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
    Dense.Gaussian.Bounds.LeadingDominance.normSq_leadingMonomial_eval_lower degreePositive radiusSqPositive.le
      (by simpa only [radiusSq] using normLower)
  calc
    Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
        Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) := lowerBound
    _ < (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := scaledStrict
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
      leadingRadial

/-- Explicit dominance margin on an arbitrary sufficiently large symmetric
square.

The retained leading quadrance, lower coefficient weight and natural
degree determine the gap at the supplied radius. Its radial power uses
the original degree predecessor. -/
@[expose] public def symmetricDominanceMargin
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (radius : Fraction.Rational) : Fraction.Rational :=
  (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radius ^ 2 -
      Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p) *
    (radius ^ 2) ^ (p.natDegree - 1)

/-- Every radius above the computed large-square radius has a positive leading-term dominance margin.

The supplied radius is at least the computed positive radius.
For positive degree, increasing that radius preserves the strict
coefficient gap and the positivity of its radial power. -/
public theorem symmetricDominanceMargin_pos
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius) :
    0 < Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius := by
  have radiusPositive := (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe
  have denseSquareLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2 ≤ radius ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).le radiusLe 2
  have leadingScaled :
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ^ 2
        ≤
        Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denseSquareLe
      (Gaussian.Norm.Basic.normSq_nonneg p.leadingCoeff)
  have weightStrict : Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p <
      Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radius ^ 2 :=
    (Dense.Gaussian.Bounds.LeadingDominance.denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive).trans_le
      leadingScaled
  apply Fraction.Order.Arithmetic.mul_pos_direct
  · exact Fraction.Order.Arithmetic.sub_pos_direct weightStrict
  · exact Fraction.Order.Arithmetic.pow_pos_direct (by
      rw [pow_two]
      exact Fraction.Order.Arithmetic.mul_pos_direct radiusPositive
        radiusPositive) _

/-- The retained margin bounds leading-minus-tail quadrance throughout a sufficiently large square annulus.

The polynomial has positive degree and point quadrance lies between the squared radius and twice that square. -/
public theorem symmetric_radial_dominance_margin
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Fraction.Rational}
    (radiusLe : Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius p ≤ radius)
    {z : Gaussian.Basic.Canonical}
    (normLower : radius ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq z)
    (normUpper : Data.Gaussian.Norm.Basic.normSq z ≤ 2 * radius ^ 2) :
    Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) -
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) := by
  let radiusSq := radius ^ 2
  have radiusPositive := (Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius_pos p).trans_le radiusLe
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_pos_direct radiusPositive radiusPositive
  have oneLeRadius : (1 : Fraction.Rational) ≤ radius :=
    (Dense.Gaussian.Bounds.RootRadius.one_le_denseLargeSquareRadius p).trans radiusLe
  have oneLeRadiusSq : (1 : Fraction.Rational) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct oneLeRadius oneLeRadius
      (by decide) radiusPositive.le
  have lowerTermsBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have leadingBound := Dense.Gaussian.Bounds.LeadingDominance.normSq_leadingMonomial_eval_lower degreePositive
    radiusSqPositive.le (by simpa only [radiusSq] using normLower)
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have sumBound :
      Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius +
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) := by
    calc
      Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius +
          Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) ≤
        Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius +
          Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight p *
            radiusSq ^ (p.natDegree - 1) :=
        add_le_add le_rfl lowerTermsBound
      _ = (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq) *
            radiusSq ^ (p.natDegree - 1) := by
        dsimp only [Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin, radiusSq]
        ring1
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
            (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff *
            radiusSq ^ (p.natDegree - 1 + 1) := by
        exact congrArg (Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * ·)
          (pow_succ radiusSq (p.natDegree - 1)).symm
      _ = Data.Gaussian.Norm.Basic.normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
        rw [degreeIdentity]
      _ ≤ Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) :=
        leadingBound
  have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
    sumBound (-Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z))
  have lowerReadback :
      (Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius + Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z)) +
        -Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) =
      Dense.Gaussian.Bounds.LeadingDominance.symmetricDominanceMargin p radius := by ring1
  have upperReadback :
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) +
        -Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) =
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.LeadingSplit.leadingMonomial p).eval z) -
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Coefficients.Tail.lowerTermsPolynomial p).eval z) := by
          ring1
  exact lowerReadback ▸ upperReadback ▸ translated

end Purelib.Polynomial.Dense.Gaussian.Bounds.LeadingDominance
