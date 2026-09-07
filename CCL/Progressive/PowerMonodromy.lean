import CCL.Progressive.FiniteMonodromy
import CCL.Transcendental.RootPowers
import RFAP.Winding.Polygon

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace CCL.PowerMonodromy

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev RootDegree := CCL.RootPowers.RootDegree
abbrev CoefficientState :=
  CCL.ProgressivePolynomialRoots.CoefficientState
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructiveGaussian.Gaussian

/-! ## An explicit-evaluation constructor for squarefree certificates -/

/-- An explicit finite Bézout evaluation identity rules out the
nonconstant-gcd branch of the executable squarefreeness decision.  The
conversion to coefficient factorization queries only the bounded candidate
list of the displayed difference polynomial. -/
def squarefreeOfEvalBezout
    (polynomial : GaussianPolynomial)
    (nonzero : polynomial.isZero = false)
    (left right : GaussianPolynomial)
    (identity : ∀ point : Gaussian,
      left.eval point * polynomial.eval point +
        right.eval point *
          (RFAP.ConstructiveGCD.derivative polynomial).eval point = 1) :
    RFAP.Squarefree.SquarefreeCertificate polynomial := by
  match outcome : RFAP.Squarefree.squarefreeOutcome polynomial nonzero with
  | .coprime certificate => exact certificate
  | .commonDivisor common =>
      let cofactor :=
        left * common.leftFactor + right * common.rightFactor
      have factorization : RFAP.Factorization.ProductIdentity
          (constant 1) common.divisor cofactor := by
        apply RFAP.Factorization.factorizationOfCandidateEvals
        intro point _member
        dsimp only [cofactor]
        rw [eval_constant, eval_add, eval_mul, eval_mul]
        calc
          1 = left.eval point * polynomial.eval point +
                right.eval point *
                  (RFAP.ConstructiveGCD.derivative polynomial).eval point :=
            (identity point).symm
          _ = common.divisor.eval point *
                (left.eval point * common.leftFactor.eval point +
                  right.eval point * common.rightFactor.eval point) := by
            rw [common.leftIdentity point, common.rightIdentity point]
            ring1
      have oneNonzero : (constant (1 : Gaussian)).isZero = false := by
        simp [isZero, normalize]
      have oneNormalized :
          (constant (1 : Gaussian)).normalize = constant 1 := by
        exact normalize_constant_of_ne (by decide)
      have cofactorNonzero : cofactor.isZero = false :=
        RFAP.Factorization.right_isZero_false oneNonzero oneNormalized
          factorization
      have degreeBalance := RFAP.Factorization.factor_natDegree_add
        oneNonzero oneNormalized common.nonzero cofactorNonzero factorization
      have degreeZero : (constant (1 : Gaussian)).natDegree = 0 := by
        simp [natDegree, degreeCount, normalize]
      rw [degreeZero] at degreeBalance
      have commonDegreeZero : common.divisor.natDegree = 0 :=
        (Nat.eq_zero_of_add_eq_zero degreeBalance).1
      exact (Nat.ne_of_gt common.positiveDegree commonDegreeZero).elim

/-! ## The displayed power polynomial -/

def polynomial (parameter : Gaussian) (degree : RootDegree) :
    GaussianPolynomial :=
  CCL.RootPowers.rootPolynomial parameter degree

theorem polynomial_normalized (parameter : Gaussian) (degree : RootDegree) :
    (polynomial parameter degree).normalize = polynomial parameter degree :=
  CCL.RootPowers.rootPolynomial_normalized parameter degree

theorem polynomial_degree (parameter : Gaussian) (degree : RootDegree) :
    (polynomial parameter degree).natDegree = degree.value :=
  CCL.RootPowers.rootPolynomial_degree parameter degree

theorem polynomial_eval (parameter point : Gaussian) (degree : RootDegree) :
    (polynomial parameter degree).eval point =
      point ^ degree.value - parameter :=
  CCL.RootPowers.rootPolynomial_eval parameter point degree

/-- The existing positive coordinate-power program is coefficientwise the
same displayed polynomial after subtracting the parameter constant. -/
theorem polynomial_eq_coordinatePower_sub_constant
    (parameter : Gaussian) (degree : RootDegree) :
    polynomial parameter degree =
      RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1) -
        constant parameter := by
  apply RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
    (polynomial_normalized parameter degree)
    (normalize_sub _ _)
  apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
  intro point _member
  rw [eval_sub, polynomial_eval,
    RFAP.GlobalWinding.coordinatePositivePower_eval, eval_constant]
  rw [Nat.sub_add_cancel degree.positive]

theorem derivative_coordinatePolynomial_eval (point : Gaussian) :
    (RFAP.ComputableDerivative.derivative
      RFAP.GlobalWinding.coordinatePolynomial).eval point = 1 := by
  rw [RFAP.ComputableDerivative.eval_derivative]
  simp only [RFAP.GlobalWinding.coordinatePolynomial,
    RFAP.ComputableDerivative.evalDerivativeCoeffs, List.foldl_cons,
    List.foldl_nil, RFAP.ComputableDerivative.evalDerivativeStep, zero_mul,
    zero_add, add_zero]

/-- Exact automatic derivative of the positive coordinate power. -/
theorem derivative_coordinatePositivePower_eval : ∀ exponent : Nat,
    ∀ point : Gaussian,
    (RFAP.ComputableDerivative.derivative
      (RFAP.GlobalWinding.coordinatePositivePower exponent)).eval point =
      ((exponent + 1 : Nat) : Gaussian) * point ^ exponent
  | 0, point => by
      change
        (RFAP.ComputableDerivative.derivative
          RFAP.GlobalWinding.coordinatePolynomial).eval point =
            (1 : Gaussian) * point ^ 0
      rw [derivative_coordinatePolynomial_eval, pow_zero]
      change (1 : Gaussian) = (1 : Gaussian) * 1
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  | exponent + 1, point => by
      rw [RFAP.GlobalWinding.coordinatePositivePower,
        RFAP.ComputableDerivative.eval_derivative_mul,
        derivative_coordinatePositivePower_eval exponent,
        RFAP.GlobalWinding.coordinatePositivePower_eval,
        RFAP.GlobalWinding.coordinatePolynomial_eval,
        derivative_coordinatePolynomial_eval]
      change
        (((exponent + 1 : Nat) : Gaussian) * point ^ exponent) * point +
            point ^ (exponent + 1) * 1 =
          ((exponent + 1 + 1 : Nat) : Gaussian) * point ^ (exponent + 1)
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_one, pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring1

/-- The derivative of `Z^d-w` is the displayed finite expression
`d Z^(d-1)`. -/
theorem derivative_eval (parameter point : Gaussian) (degree : RootDegree) :
    (RFAP.ConstructiveGCD.derivative
      (polynomial parameter degree)).eval point =
      (degree.value : Gaussian) * point ^ (degree.value - 1) := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [polynomial_eq_coordinatePower_sub_constant,
    RFAP.ComputableDerivative.eval_derivative_sub,
    derivative_coordinatePositivePower_eval]
  have derivativeConstant :
      (RFAP.ComputableDerivative.derivative
        (constant parameter)).eval point = 0 := by
    rw [RFAP.ComputableDerivative.eval_derivative]
    change
      (RFAP.ComputableDerivative.evalDerivativeCoeffs point [parameter]).2 = 0
    simp only [RFAP.ComputableDerivative.evalDerivativeCoeffs,
      List.foldl_cons, List.foldl_nil,
      RFAP.ComputableDerivative.evalDerivativeStep, zero_mul, zero_add]
  rw [derivativeConstant, RFAP.ConstructiveGaussian.Gaussian.sub_zero,
    Nat.sub_add_cancel degree.positive]

/-- The automatic derivative of `Z^d-w` is coefficientwise independent of
the displayed parameter `w`; this is an equality of finite coefficient
lists, not an inference from evaluations. -/
theorem derivative_polynomial_eq (source target : Gaussian)
    (degree : RootDegree) :
    RFAP.ConstructiveGCD.derivative (polynomial source degree) =
      RFAP.ConstructiveGCD.derivative (polynomial target degree) := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  unfold RFAP.ConstructiveGCD.derivative
    RFAP.ComputableDerivative.derivative
    RFAP.ComputableDerivative.derivativeState polynomial
    CCL.RootPowers.rootPolynomial
  simp only [List.foldl_cons, QuotientFreeList.foldl_append,
    List.foldl_nil, RFAP.ComputableDerivative.derivativeStep]

def bezoutLeft (parameter : Gaussian) : GaussianPolynomial :=
  constant (-parameter⁻¹)

def bezoutRight (parameter : Gaussian) (degree : RootDegree) :
    GaussianPolynomial :=
  scale (parameter⁻¹ * (degree.value : Gaussian)⁻¹)
    RFAP.GlobalWinding.coordinatePolynomial

/-- Uniform displayed Bézout identity for the power family away from the
parameter origin. -/
theorem bezout_identity
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (point : Gaussian) :
    (bezoutLeft parameter).eval point *
        (polynomial parameter degree).eval point +
      (bezoutRight parameter degree).eval point *
        (RFAP.ConstructiveGCD.derivative
          (polynomial parameter degree)).eval point = 1 := by
  have degreeNonzero : (degree.value : Gaussian) ≠ 0 :=
    RFAP.ConstructiveDerivativeDegree.gaussian_natCast_ne_zero degree.positive
  have parameterCancel : parameter⁻¹ * parameter = 1 := by
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
    exact RFAP.ExplicitField.mul_inv_cancel parameter parameterNonzero
  have degreeCancel :
      (degree.value : Gaussian)⁻¹ * (degree.value : Gaussian) = 1 := by
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm]
    exact RFAP.ExplicitField.mul_inv_cancel _ degreeNonzero
  simp only [bezoutLeft, bezoutRight, eval_constant, eval_scale,
    RFAP.GlobalWinding.coordinatePolynomial_eval, polynomial_eval,
    derivative_eval]
  have powerStep :
      point ^ (degree.value - 1) * point = point ^ degree.value := by
    rw [← pow_succ, Nat.sub_add_cancel degree.positive]
  calc
    -parameter⁻¹ * (point ^ degree.value - parameter) +
          parameter⁻¹ * (degree.value : Gaussian)⁻¹ * point *
            ((degree.value : Gaussian) * point ^ (degree.value - 1)) =
        parameter⁻¹ * parameter +
          parameter⁻¹ *
            ((degree.value : Gaussian)⁻¹ * (degree.value : Gaussian)) *
              point ^ degree.value -
          parameter⁻¹ * point ^ degree.value := by
      rw [← powerStep]
      ring1
    _ = 1 := by rw [parameterCancel, degreeCancel]; ring1

theorem polynomial_nonzero (parameter : Gaussian) (degree : RootDegree) :
    (polynomial parameter degree).isZero = false :=
  RFAP.Linear.isZero_false_of_natDegree_pos (by
    rw [polynomial_degree]
    exact degree.positive)

/-! ## Uniform derivative separation on the unit parameter circuit -/

/-- The triangle estimate before inserting the residual budget. -/
private theorem unit_le_twice_power_add_residual
    {parameter point : Gaussian} {exponent : Nat}
    (parameterUnit : normSq parameter = 1) :
    (1 : Coordinate) ≤
      2 * (normSq (point ^ exponent) +
        normSq (point ^ exponent - parameter)) := by
  have raw := normSq_sub_le_two
    (point ^ exponent) (point ^ exponent - parameter)
  have identity : point ^ exponent - (point ^ exponent - parameter) =
      parameter := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im] <;>
      ring1
  rw [identity, parameterUnit] at raw
  exact raw

/-- Elementary rational rearrangement of the preceding triangle estimate. -/
private theorem one_fourth_le_of_unit_triangle
    {powerNorm : Coordinate}
    (bounded : (1 : Coordinate) ≤
      2 * (powerNorm + (1 / 4 : Coordinate))) :
    (1 / 4 : Coordinate) ≤ powerNorm := by
  have halfLe : (1 / 2 : Coordinate) ≤ powerNorm + 1 / 4 := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    calc
      (1 : Coordinate) ≤ 2 * (powerNorm + (1 / 4 : Coordinate)) := bounded
      _ = (powerNorm + 1 / 4) * 2 := by ring1
  have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct
    halfLe (1 / 4 : Coordinate)
  calc
    (1 / 4 : Coordinate) = 1 / 2 - 1 / 4 := by decide
    _ ≤ (powerNorm + 1 / 4) - 1 / 4 := shifted
    _ = powerNorm := by ring1

/-- The corresponding lower residual estimate: the power quadrance cannot
fall below `1/4` while remaining within quadrance `1/4` of a unit parameter. -/
private theorem one_fourth_le_normSq_power_of_residual_le_quarter
    {parameter point : Gaussian} {exponent : Nat}
    (parameterUnit : normSq parameter = 1)
    (residualSmall : normSq (point ^ exponent - parameter) ≤
      (1 / 4 : Coordinate)) :
    (1 / 4 : Coordinate) ≤ normSq point ^ exponent := by
  have sumBound :
      normSq (point ^ exponent) +
          normSq (point ^ exponent - parameter) ≤
        normSq (point ^ exponent) + (1 / 4 : Coordinate) := by
    calc
      normSq (point ^ exponent) + normSq (point ^ exponent - parameter) =
          normSq (point ^ exponent - parameter) +
            normSq (point ^ exponent) := by ring1
      _ ≤ (1 / 4 : Coordinate) + normSq (point ^ exponent) :=
        RFAP.ConstructiveFraction.add_le_add_right_direct residualSmall _
      _ = normSq (point ^ exponent) + (1 / 4 : Coordinate) := by ring1
  have bounded : (1 : Coordinate) ≤
      2 * (normSq (point ^ exponent) + (1 / 4 : Coordinate)) :=
    (unit_le_twice_power_add_residual parameterUnit).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        sumBound (by decide))
  have lower := one_fourth_le_of_unit_triangle bounded
  simpa only [normSq_pow] using lower

/-- The purely rational last step of the separation estimate. -/
private theorem one_eighth_le_power_predecessor
    {value : Coordinate} {exponent : Nat}
    (exponentPositive : 0 < exponent)
    (quarterLePower : (1 / 4 : Coordinate) ≤ value ^ exponent)
    (nonnegative : 0 ≤ value) :
    (1 / 8 : Coordinate) ≤ value ^ (exponent - 1) := by
  have predecessorSplit : exponent - 1 + 1 = exponent :=
    Nat.sub_add_cancel exponentPositive
  have powerSplit : value ^ exponent = value ^ (exponent - 1) * value := by
    calc
      value ^ exponent = value ^ (exponent - 1 + 1) := by
        rw [predecessorSplit]
      _ = value ^ (exponent - 1) * value := by rw [pow_succ]
  by_cases atMostOne : value ≤ 1
  · have powerLePredecessor : value ^ exponent ≤
        value ^ (exponent - 1) := by
      rw [powerSplit]
      calc
        value ^ (exponent - 1) * value ≤
            value ^ (exponent - 1) * 1 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            atMostOne
            (RFAP.ConstructiveFraction.pow_nonneg_direct nonnegative _)
        _ = value ^ (exponent - 1) := by ring1
    exact (show (1 / 8 : Coordinate) ≤ 1 / 4 by decide).trans
      (quarterLePower.trans powerLePredecessor)
  · have oneLe : (1 : Coordinate) ≤ value :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct atMostOne).le
    have oneLePower : (1 : Coordinate) ≤ value ^ (exponent - 1) := by
      have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
        (show (0 : Coordinate) ≤ 1 by decide) oneLe (exponent - 1)
      simpa only [one_pow] using powered
    exact (show (1 / 8 : Coordinate) ≤ 1 by decide).trans oneLePower

/-- A positive power bounded by `5/2` already bounds its nonnegative base by
`5/2`.  The case split avoids extracting any radical. -/
private theorem value_le_five_halves_of_power_le
    {value : Coordinate} {exponent : Nat}
    (exponentPositive : 0 < exponent) (nonnegative : 0 ≤ value)
    (powerUpper : value ^ exponent ≤ (5 / 2 : Coordinate)) :
    value ≤ 5 / 2 := by
  by_cases atMostOne : value ≤ 1
  · exact atMostOne.trans (by decide)
  · have oneLe : (1 : Coordinate) ≤ value :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct atMostOne).le
    have predecessorOne : (1 : Coordinate) ≤ value ^ (exponent - 1) := by
      have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
        (show (0 : Coordinate) ≤ 1 by decide) oneLe (exponent - 1)
      simpa only [one_pow] using powered
    have split : exponent - 1 + 1 = exponent :=
      Nat.sub_add_cancel exponentPositive
    have powerSplit : value ^ exponent =
        value ^ (exponent - 1) * value := by
      calc
        value ^ exponent = value ^ (exponent - 1 + 1) := by rw [split]
        _ = value ^ (exponent - 1) * value := by rw [pow_succ]
    have valueLePower : value ≤ value ^ exponent := by
      calc
        value = value * 1 := by ring1
        _ ≤ value * value ^ (exponent - 1) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            predecessorOne nonnegative
        _ = value ^ (exponent - 1) * value := by ring1
        _ = value ^ exponent := powerSplit.symm
    exact valueLePower.trans powerUpper

/-- The unit parameter and residual budget also give the coarse radial upper
bound used only to place the ensuing rational Newton square in the global
ambient square. -/
private theorem normSq_le_five_halves_of_power_residual
    {parameter point : Gaussian} {exponent : Nat}
    (exponentPositive : 0 < exponent)
    (parameterUnit : normSq parameter = 1)
    (residualSmall : normSq (point ^ exponent - parameter) ≤
      (1 / 4 : Coordinate)) :
    normSq point ≤ 5 / 2 := by
  let residual := point ^ exponent - parameter
  have sumIdentity : point ^ exponent = residual + parameter := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [residual, sub_re, sub_im, add_re, add_im] <;>
      ring1
  have powerUpper : normSq point ^ exponent ≤ (5 / 2 : Coordinate) := by
    calc
      normSq point ^ exponent = normSq (point ^ exponent) :=
        (normSq_pow point exponent).symm
      _ = normSq (residual + parameter) := by rw [sumIdentity]
      _ ≤ 2 * (normSq residual + normSq parameter) :=
        normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 4 : Coordinate) + 1) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add residualSmall parameterUnit.le) (by decide)
      _ = 5 / 2 := by decide
  exact value_le_five_halves_of_power_le exponentPositive
    (normSq_nonneg point) powerUpper

/-- Uniform finite derivative separation for `Z^d-w` on any displayed box
when the exact parameter has quadrance one.  The threshold `1/4` and margin
`1/8` do not depend on a completed root or on a compactness argument. -/
def unitParameterDerivativeSeparation
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (_degreeAtLeastTwo : 2 ≤ degree.value)
    (ambient : RFAP.Boxes.Box) :
    RFAP.DerivativeSeparation.Certificate
      (polynomial parameter degree) ambient where
  threshold := 1 / 4
  threshold_pos := by decide
  margin := 1 / 8
  margin_pos := by decide
  lower := by
    intro point _inside residualSmall
    have powerResidual : normSq (point ^ degree.value - parameter) ≤
        (1 / 4 : Coordinate) := by
      rw [← polynomial_eval parameter point degree]
      exact residualSmall
    have powerLower := one_fourth_le_normSq_power_of_residual_le_quarter
      parameterUnit powerResidual
    have predecessorLower := one_eighth_le_power_predecessor degree.positive
      powerLower (normSq_nonneg point)
    rw [derivative_eval, normSq_mul, normSq_pow]
    have degreeCastLower : (1 : Coordinate) ≤
        (degree.value : Coordinate) :=
      RFAP.ConstructiveFraction.natCast_le_direct degree.positive
    have degreeNormLower : (1 : Coordinate) ≤
        normSq (degree.value : Gaussian) := by
      have identity : normSq (degree.value : Gaussian) =
          (degree.value : Coordinate) ^ 2 := by
        simp only [RFAP.ConstructiveGaussian.Gaussian.normSq,
          RFAP.ConstructiveGaussian.Gaussian.natCast_re,
          RFAP.ConstructiveGaussian.Gaussian.natCast_im]
        ring1
      rw [identity]
      simpa only [one_pow] using
        RFAP.ConstructiveFraction.pow_le_pow_direct
          (show (0 : Coordinate) ≤ 1 by decide) degreeCastLower 2
    calc
      (1 / 8 : Coordinate) =
          1 * (1 / 8 : Coordinate) := by ring1
      _ ≤ normSq (degree.value : Gaussian) *
          (normSq point ^ (degree.value - 1)) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct degreeNormLower
          predecessorLower (by decide)
          (normSq_nonneg (degree.value : Gaussian))

private theorem weightedNormSum_replicate_zero
    (count exponent : Nat) :
    RFAP.GlobalWinding.weightedNormSum
      (List.replicate count (0 : Gaussian)) exponent = 0 := by
  induction count generalizing exponent with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, RFAP.GlobalWinding.weightedNormSum,
        normSq_zero, inductionHypothesis]
      ring1

/-- For the sparse power polynomial the global-square coefficient weight is
exactly `d N(w)`.  In particular, parameters with equal squared norm use the
same computed ambient box; no completed circle or compactness argument is
needed to identify their finite isolations' supports. -/
theorem denseLowerCoefficientWeight_polynomial
    (parameter : Gaussian) (degree : RootDegree) :
    RFAP.GlobalWinding.denseLowerCoefficientWeight
        (polynomial parameter degree) =
      (degree.value : Coordinate) * normSq parameter := by
  rw [RFAP.GlobalWinding.denseLowerCoefficientWeight,
    polynomial_degree, RFAP.GlobalWinding.lowerCoefficients,
    polynomial_normalized]
  simp only [polynomial, CCL.RootPowers.rootPolynomial, List.tail_cons,
    List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [RFAP.GlobalWinding.weightedNormSum_append]
  simp only [RFAP.GlobalWinding.weightedNormSum, normSq_neg, pow_zero,
    List.length_singleton, Nat.zero_add, weightedNormSum_replicate_zero]
  ring1

theorem leadingCoeff_polynomial
    (parameter : Gaussian) (degree : RootDegree) :
    (polynomial parameter degree).leadingCoeff = 1 := by
  rw [RFAP.ComputablePolynomial.DensePolynomial.leadingCoeff,
    polynomial_normalized]
  rfl

/-- Equal-norm parameters in the power family have definitionally equal
coefficient-computed global square radii. -/
theorem largeSquareBox_polynomial_eq_of_normSq_eq
    {source target : Gaussian} (equalNorm : normSq source = normSq target)
    (degree : RootDegree) :
    RFAP.GlobalWinding.largeSquareBox (polynomial source degree) =
      RFAP.GlobalWinding.largeSquareBox (polynomial target degree) := by
  unfold RFAP.GlobalWinding.largeSquareBox
  congr 1
  unfold RFAP.GlobalWinding.denseLargeSquareRadius
  rw [denseLowerCoefficientWeight_polynomial,
    denseLowerCoefficientWeight_polynomial, leadingCoeff_polynomial,
    leadingCoeff_polynomial, normSq_one, equalNorm]

/-- The coefficient-scanned Taylor budget is likewise identical for
equal-quadrance parameters.  The Horner scan sees the parameter only through
the quadrance of the final coefficient `-w`. -/
theorem denseTaylorRemainderBound_polynomial_eq_of_normSq_eq
    {source target : Gaussian} (equalNorm : normSq source = normSq target)
    (degree : RootDegree) :
    RFAP.PolynomialBounds.denseTaylorRemainderBound
        (polynomial source degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial source degree)) =
      RFAP.PolynomialBounds.denseTaylorRemainderBound
        (polynomial target degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  rw [← largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
  unfold RFAP.PolynomialBounds.denseTaylorRemainderBound
    RFAP.PolynomialBounds.denseEvalTaylorRemainderBound
    RFAP.PolynomialBounds.denseHornerTaylorNormBounds
  simp only [polynomial, CCL.RootPowers.rootPolynomial, List.foldl_cons,
    QuotientFreeList.foldl_append, List.foldl_nil,
    RFAP.PolynomialBounds.HornerTaylorNormBounds.step, normSq_neg, equalNorm]

/-- The first-order Horner majorant has the same equal-quadrance invariance. -/
theorem denseLipschitzBound_polynomial_eq_of_normSq_eq
    {source target : Gaussian} (equalNorm : normSq source = normSq target)
    (degree : RootDegree) :
    RFAP.PolynomialBounds.denseLipschitzBound
        (polynomial source degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial source degree)) =
      RFAP.PolynomialBounds.denseLipschitzBound
        (polynomial target degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  rw [← largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
  unfold RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds
  simp only [polynomial, CCL.RootPowers.rootPolynomial, List.foldl_cons,
    QuotientFreeList.foldl_append, List.foldl_nil,
    RFAP.PolynomialBounds.HornerNormBounds.step, normSq_neg, equalNorm]

/-- On the unit parameter circuit the computed global square has exact
radius `d+1`. -/
theorem denseLargeSquareRadius_polynomial_of_unit
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) :
    RFAP.GlobalWinding.denseLargeSquareRadius (polynomial parameter degree) =
      (degree.value : Coordinate) + 1 := by
  unfold RFAP.GlobalWinding.denseLargeSquareRadius
  rw [denseLowerCoefficientWeight_polynomial, leadingCoeff_polynomial,
    normSq_one, parameterUnit]
  have oneLeDegree : (1 : Coordinate) ≤ (degree.value : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct degree.positive
  have expression :
      (degree.value : Coordinate) * 1 / 1 + 1 =
        (degree.value : Coordinate) + 1 := by
    have inverseOne : (1 : Coordinate)⁻¹ = 1 := by decide
    rw [RFAP.ExplicitField.div_eq_mul_inv, inverseOne]
    ring1
  rw [expression]
  exact max_eq_right (by
    calc
      (1 : Coordinate) ≤ (degree.value : Coordinate) := oneLeDegree
      _ ≤ (degree.value : Coordinate) + 1 := le_add_of_nonneg_right (by decide))

/-- Uniform squared-diameter scale below which two separated winding-one
tracks for a unit-parameter power polynomial cannot share a common box. -/
def unitUniquenessDiagonalThreshold
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  let ambient := RFAP.GlobalWinding.largeSquareBox
    (polynomial parameter degree)
  RFAP.TrackSeparation.separatedUniquenessDiagonalThreshold ambient
    (unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo
      ambient)

theorem unitUniquenessDiagonalThreshold_pos
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo :=
  RFAP.TrackSeparation.separatedUniquenessDiagonalThreshold_pos _
    (unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo _)

/-- Every exact rational point on the unit parameter circuit uses the same
displayed uniqueness scale. -/
theorem unitUniquenessDiagonalThreshold_eq_of_normSq_eq
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitUniquenessDiagonalThreshold sourceUnit degree degreeAtLeastTwo =
      unitUniquenessDiagonalThreshold targetUnit degree degreeAtLeastTwo := by
  unfold unitUniquenessDiagonalThreshold
    RFAP.TrackSeparation.separatedUniquenessDiagonalThreshold
  simp only [unitParameterDerivativeSeparation]
  rw [denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree]

/-- Fixed Newton-square radius for one unit parameter.  The four terms bound
the absolute radius, the Taylor remainder, two-track uniqueness, and the
Lipschitz variation later used by the finite lift polygon. -/
def unitRobustRadius
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let taylor := RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  min
    (min
      (min (1 / 8 : Coordinate) ((1 / 8 : Coordinate) / (72 * taylor)))
      (uniqueness / 64))
    (((1 / 8 : Coordinate) ^ 3) / lipschitz)

theorem unitRobustRadius_pos
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitRobustRadius parameterUnit degree degreeAtLeastTwo := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let taylor := RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have taylorPositive : 0 < taylor :=
    RFAP.PolynomialBounds.denseTaylorRemainderBound_pos p ambient
  have uniquenessPositive : 0 < uniqueness :=
    unitUniquenessDiagonalThreshold_pos parameterUnit degree degreeAtLeastTwo
  have lipschitzPositive : 0 < lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient
  have oneEighthPositive : (0 : Coordinate) < 1 / 8 :=
    RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 8) (by decide))
  have seventyTwoPositive : (0 : Coordinate) < 72 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide)
  have sixtyFourPositive : (0 : Coordinate) < 64 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 64) (by decide)
  have oneEighthCubedPositive : (0 : Coordinate) < (1 / 8) ^ 3 :=
    RFAP.ConstructiveFraction.pow_pos_direct oneEighthPositive 3
  unfold unitRobustRadius
  exact lt_min
    (lt_min
      (lt_min oneEighthPositive
        (RFAP.ConstructiveFraction.div_pos_direct oneEighthPositive
          (RFAP.ConstructiveFraction.mul_pos_direct seventyTwoPositive
            taylorPositive)))
      (RFAP.ConstructiveFraction.div_pos_direct uniquenessPositive
        sixtyFourPositive))
    (RFAP.ConstructiveFraction.div_pos_direct oneEighthCubedPositive
      lipschitzPositive)

theorem unitRobustRadius_le_eighth
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustRadius parameterUnit degree degreeAtLeastTwo ≤ 1 / 8 :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

/-- The fixed radius satisfies the separated Newton Taylor dominance. -/
theorem unitRobustRadius_taylor
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := polynomial parameter degree
    let ambient := RFAP.GlobalWinding.largeSquareBox p
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient *
      r ^ 2) ≤ (1 / 8 : Coordinate) := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let taylor := RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ (1 / 8 : Coordinate) / (72 * taylor) :=
    (min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_right _ _))
  have denominatorPositive : 0 < (72 : Coordinate) * taylor :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 72) (by decide))
      (RFAP.PolynomialBounds.denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (72 * taylor) ≤ (1 / 8 : Coordinate) :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct radiusLeOne
          radiusPositive.le
      _ = r := by ring1
  calc
    2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient *
        r ^ 2) = (72 * taylor) * r ^ 2 := by
      dsimp only [taylor]
      ring1
    _ ≤ (72 * taylor) * r :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        squareLeRadius denominatorPositive.le
    _ = r * (72 * taylor) := by ring1
    _ ≤ 1 / 8 := ratioScaled

/-- The hull of two overlapping radius-`r` robust squares will be below the
explicit track-uniqueness threshold. -/
theorem thirtyTwo_mul_unitRobustRadius_sq_lt_uniqueness
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    32 * unitRobustRadius parameterUnit degree degreeAtLeastTwo ^ 2 <
      unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo := by
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ uniqueness / 64 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have sixtyFourPositive : (0 : Coordinate) < 64 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 64) (by decide)
  have scaled : r * 64 ≤ uniqueness :=
    (RFAP.ConstructiveFraction.le_div_iff_pos sixtyFourPositive).mp radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq (one_mul r)
  calc
    32 * r ^ 2 ≤ 32 * r :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLeRadius
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 32) (by decide)).le
    _ < 64 * r := by
      have positiveScaled := RFAP.ConstructiveFraction.mul_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 32) (by decide)) radiusPositive
      calc
        32 * r = 0 + 32 * r := by ring1
        _ < 32 * r + 32 * r :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct positiveScaled _
        _ = 64 * r := by ring1
    _ = r * 64 := by ring1
    _ ≤ uniqueness := scaled

theorem unitRobustRadius_eq_of_normSq_eq
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustRadius sourceUnit degree degreeAtLeastTwo =
      unitRobustRadius targetUnit degree degreeAtLeastTwo := by
  unfold unitRobustRadius
  dsimp only
  rw [denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree,
    denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    unitUniquenessDiagonalThreshold_eq_of_normSq_eq sourceUnit targetUnit
      equalNorm degree degreeAtLeastTwo]

/-- The lift constraint in the robust radius bounds one full coefficientwise
Lipschitz variation budget. -/
theorem unitRobustRadius_mul_lipschitz_le
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := polynomial parameter degree
    let ambient := RFAP.GlobalWinding.largeSquareBox p
    unitRobustRadius parameterUnit degree degreeAtLeastTwo *
        RFAP.PolynomialBounds.denseLipschitzBound p ambient ≤
      (1 / 8 : Coordinate) ^ 3 := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  have lipschitzPositive : 0 < lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient
  apply (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
  exact min_le_right _ _

/-- Refinement request used before the fixed-radius Newton step.  Its four
terms respectively keep squaring harmless, enter the derivative threshold,
bound the Newton displacement by `(r/4)^2`, and place the source box itself
within the same quarter-radius scale. -/
def unitRobustSourceRadius
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let quarterRadius := r / 4
  min 1
    (min ((1 / 4 : Coordinate) / lipschitz)
      (min (((1 / 8 : Coordinate) * quarterRadius ^ 2) / lipschitz)
        (quarterRadius ^ 2)))

theorem unitRobustSourceRadius_pos
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let quarterRadius := r / 4
  have lipschitzPositive : 0 < lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient
  have quarterRadiusPositive : 0 < quarterRadius :=
    RFAP.ConstructiveFraction.div_pos_direct
      (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide))
  have quarterPositive : (0 : Coordinate) < 1 / 4 := by decide
  have eighthPositive : (0 : Coordinate) < 1 / 8 := by decide
  unfold unitRobustSourceRadius
  exact lt_min (by decide)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct quarterPositive
        lipschitzPositive)
      (lt_min
        (RFAP.ConstructiveFraction.div_pos_direct
          (RFAP.ConstructiveFraction.mul_pos_direct eighthPositive
            (RFAP.ConstructiveFraction.pow_pos_direct quarterRadiusPositive 2))
          lipschitzPositive)
        (RFAP.ConstructiveFraction.pow_pos_direct quarterRadiusPositive 2)))

theorem unitRobustSourceRadius_le_one
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤ 1 :=
  min_le_left _ _

theorem unitRobustSourceRadius_le_derivativeRatio
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := polynomial parameter degree
    let ambient := RFAP.GlobalWinding.largeSquareBox p
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (1 / 4 : Coordinate) /
        RFAP.PolynomialBounds.denseLipschitzBound p ambient :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem unitRobustSourceRadius_le_displacementRatio
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := polynomial parameter degree
    let ambient := RFAP.GlobalWinding.largeSquareBox p
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      ((1 / 8 : Coordinate) * (r / 4) ^ 2) /
        RFAP.PolynomialBounds.denseLipschitzBound p ambient :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem unitRobustSourceRadius_le_quarterRadius_sq
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (r / 4) ^ 2 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem unitRobustSourceRadius_eq_of_normSq_eq
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustSourceRadius sourceUnit degree degreeAtLeastTwo =
      unitRobustSourceRadius targetUnit degree degreeAtLeastTwo := by
  unfold unitRobustSourceRadius
  dsimp only
  rw [denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    unitRobustRadius_eq_of_normSq_eq sourceUnit targetUnit equalNorm degree
      degreeAtLeastTwo]

/-- Every displayed nonzero parameter gives a squarefree power polynomial,
with no discriminant, completed roots, or carrier-level argument. -/
def squarefree {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) :
    RFAP.Squarefree.SquarefreeCertificate
      (polynomial parameter degree) :=
  squarefreeOfEvalBezout (polynomial parameter degree)
    (polynomial_nonzero parameter degree)
    (bezoutLeft parameter) (bezoutRight parameter degree)
    (bezout_identity parameterNonzero degree)

/-! ## Exact finite coefficient frames -/

/-- A terminating coefficient channel read at its unique exact state. -/
def exactCoefficientState (value : Gaussian) : CoefficientState where
  channel := CCL.ProgressiveCoherence.CoherentNamed.exact value
  state := ()

@[simp] theorem exactCoefficientState_value (value : Gaussian) :
    (exactCoefficientState value).value = value := rfl

@[simp] theorem exactCoefficientState_allowance (value : Gaussian) :
    (exactCoefficientState value).allowance = 0 := rfl

/-- The displayed non-leading coefficient list of `Z^d-w`. -/
def coefficientValues (parameter : Gaussian) (degree : RootDegree) :
    List Gaussian :=
  List.replicate (degree.value - 1) 0 ++ [-parameter]

/-- The exact terminating coefficient table used at each rational parameter
vertex of the circuit. -/
def coefficientTable (parameter : Gaussian) (degree : RootDegree) :
    CoefficientTable where
  entries := (coefficientValues parameter degree).map exactCoefficientState

@[simp] theorem coefficientValues_length
    (parameter : Gaussian) (degree : RootDegree) :
    (coefficientValues parameter degree).length = degree.value := by
  simp only [coefficientValues, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  exact Nat.sub_add_cancel degree.positive

@[simp] theorem coefficientTable_degree
    (parameter : Gaussian) (degree : RootDegree) :
    (coefficientTable parameter degree).degree = degree.value := by
  simp only [coefficientTable,
    CCL.ProgressivePolynomialRoots.CoefficientTable.degree,
    List.length_map, coefficientValues_length]

@[simp] theorem coefficientTable_values
    (parameter : Gaussian) (degree : RootDegree) :
    (coefficientTable parameter degree).values =
      coefficientValues parameter degree := by
  simp only [coefficientTable,
    CCL.ProgressivePolynomialRoots.CoefficientTable.values, List.map_map]
  induction coefficientValues parameter degree with
  | nil => rfl
  | cons value remaining inductionHypothesis =>
      change value ::
          List.map
            (CCL.ProgressivePolynomialRoots.CoefficientState.value ∘
              exactCoefficientState) remaining =
        value :: remaining
      rw [inductionHypothesis]

@[simp] theorem coefficientTable_polynomial
    (parameter : Gaussian) (degree : RootDegree) :
    (coefficientTable parameter degree).polynomial =
      polynomial parameter degree := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [CCL.ProgressivePolynomialRoots.CoefficientTable.polynomial,
    coefficientTable_values, coefficientValues, polynomial,
    CCL.RootPowers.rootPolynomial]

/-- Exact coefficient channels already lie below every positive chamber
target; no refinement or limit claim is hidden in a circuit vertex. -/
theorem coefficientTable_allowances_lt
    (parameter : Gaussian) (degree : RootDegree)
    {target : Coordinate} (positive : 0 < target) :
    CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt
      (coefficientTable parameter degree).entries target := by
  simp only [coefficientTable]
  induction coefficientValues parameter degree with
  | nil => trivial
  | cons value remaining inductionHypothesis =>
      simp only [List.map_cons,
        CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt,
        exactCoefficientState_allowance]
      exact ⟨positive, inductionHypothesis⟩

/-- Table-specialized squarefree certificate for every nonzero circuit
vertex. -/
def coefficientTableSquarefree {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (degree : RootDegree) :
    RFAP.Squarefree.SquarefreeCertificate
      (coefficientTable parameter degree).polynomial := by
  rw [coefficientTable_polynomial]
  exact squarefree parameterNonzero degree

/-! ## Exact higher-degree chamber frames -/

/-- The complete Paper-I finite isolation input at one nonzero parameter. -/
def isolationInput
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    RFAP.BoxFTA.Input (polynomial parameter degree) where
  squarefree := squarefree parameterNonzero degree
  degreeAtLeastTwo := by
    rw [polynomial_degree]
    exact degreeAtLeastTwo

/-- The independently computed degree-many box result at one exact rational
parameter. -/
def isolationResult
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.BoxRFAPBridge.Result (polynomial parameter degree) :=
  CCL.BoxRFAPBridge.prove
    (isolationInput parameterNonzero degree degreeAtLeastTwo)

/-- The exact coefficient table and its computed complete root-owner family
as a finite-monodromy chamber frame. -/
def chamberFrame
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable parameter degree
  chamber := by
    let result := isolationResult parameterNonzero degree degreeAtLeastTwo
    let rawOwners :=
      CCL.ProgressivePolynomialRoots.OwnerFamily.ofResult result
    have countSame : (polynomial parameter degree).natDegree =
        (coefficientTable parameter degree).degree := by
      rw [polynomial_degree, coefficientTable_degree]
    let owners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (coefficientTable parameter degree).polynomial
        (coefficientTable parameter degree).degree :=
      CCL.FiniteMonodromy.castOwnerFamilyFull
        (coefficientTable_polynomial parameter degree).symm countSame rawOwners
    let squarefreeCertificate :=
      coefficientTableSquarefree parameterNonzero degree
    have tableDegreeAtLeastTwo :
        2 ≤ (coefficientTable parameter degree).degree := by
      rw [coefficientTable_degree]
      exact degreeAtLeastTwo
    exact
      { degreeAtLeastTwo := tableDegreeAtLeastTwo
        squarefree := squarefreeCertificate
        owners := owners
        referenceSmall := coefficientTable_allowances_lt parameter degree
          (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
            (coefficientTable parameter degree) squarefreeCertificate owners)
        referenceMaximality := by
          intro familyCount family pairwise
          let rawFamily : Fin familyCount →
              RFAP.ShrinkingTrack.WindingOneTrack
                (polynomial parameter degree)
                (RFAP.GlobalWinding.largeSquareBox
                  (polynomial parameter degree)) := fun index =>
            CCL.FiniteMonodromy.castWindingOneTrack
              (coefficientTable_polynomial parameter degree)
              (congrArg RFAP.GlobalWinding.largeSquareBox
                (coefficientTable_polynomial parameter degree))
              (family index)
          have rawPairwise : ∀ left right, left ≠ right →
              (rawFamily left).initial.box.Separated
                (rawFamily right).initial.box := by
            intro left right different
            simpa only [rawFamily,
              CCL.FiniteMonodromy.castWindingOneTrack_initial_box] using
              pairwise left right different
          have bound := result.boxes.maximality rawFamily rawPairwise
          exact bound.trans_eq countSame }

@[simp] theorem chamberFrame_degree
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (chamberFrame parameterNonzero degree degreeAtLeastTwo).degree =
      degree.value := by
  exact coefficientTable_degree parameter degree

@[simp] theorem chamberFrame_polynomial
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (chamberFrame parameterNonzero degree degreeAtLeastTwo).polynomial =
      polynomial parameter degree := by
  exact coefficientTable_polynomial parameter degree

/-! ## Constant-coefficient Rouché moves -/

/-- The exact constant perturbation taking `Z^d-source` to `Z^d-target`. -/
def parameterPerturbation (source target : Gaussian) : GaussianPolynomial :=
  constant (source - target)

theorem polynomial_target_eq_add_perturbation
    (source target : Gaussian) (degree : RootDegree) :
    polynomial target degree =
      polynomial source degree + parameterPerturbation source target := by
  apply RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
    (polynomial_normalized target degree)
    (normalize_add _ _)
  apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
  intro point _member
  rw [eval_add, polynomial_eval, polynomial_eval,
    parameterPerturbation, eval_constant]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, add_re, add_im] <;>
    ring1

@[simp] theorem parameterPerturbation_eval
    (source target point : Gaussian) :
    (parameterPerturbation source target).eval point = source - target := by
  exact eval_constant (source - target) point

/-- A constant parameter displacement smaller than one owner's displayed
boundary clearance supplies the complete finite Rouché comparison. -/
def ownerMoveRouche
    {source target : Gaussian} (degree : RootDegree)
    (owner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial source degree))
    (small : normSq (source - target) < owner.clearance.bound) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial source degree) (polynomial target degree) owner.box where
  perturbation := parameterPerturbation source target
  target_eq_add := polynomial_target_eq_add_perturbation source target degree
  dominance :=
    { margin := owner.clearance.bound - normSq (source - target)
      positive := RFAP.ConstructiveFraction.sub_pos_direct small
      lower := by
        intro point boundary
        rw [parameterPerturbation_eval]
        exact RFAP.ConstructiveFraction.sub_le_sub_right_direct
          (owner.clearance.lower point boundary) (normSq (source - target)) }

/-- The old rational owner box, read at the new parameter after the
constant-coefficient Rouché move. -/
def transportedOwner
    {source target : Gaussian} (degree : RootDegree)
    (owner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial source degree))
    (small : normSq (source - target) < owner.clearance.bound) :
    CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial target degree) :=
  (CCL.FiniteMonodromy.OwnerBridge.ofForward owner
    (ownerMoveRouche degree owner small)).rightOwner

private structure PathCertificateWithBound
    (real imaginary : RFAP.ComputablePolynomial.DensePolynomial Coordinate)
    (interval : RFAP.PathClearance.Interval) (boundValue : Coordinate) where
  value : RFAP.PathClearance.Certificate
    real imaginary interval
  bound : value.bound = boundValue

/-- Construct the transported affine-path certificate together with its
finite margin-and-Horner calculation.  The package is opaque to elaboration
but remains executable. -/
private opaque certifiedPathCertificateAfterMove
    {source target : Gaussian} (degree : RootDegree)
    {origin direction : Gaussian} {interval : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal (polynomial source degree)
        origin direction)
      (RFAP.PathPolynomial.pathImag (polynomial source degree)
        origin direction) interval)
    (small : normSq (source - target) < clearance.bound) :
    PathCertificateWithBound
      (RFAP.PathPolynomial.pathReal (polynomial target degree)
        origin direction)
      (RFAP.PathPolynomial.pathImag (polynomial target degree)
        origin direction) interval
      ((clearance.bound - normSq (source - target)) ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathReal (polynomial source degree)
                origin direction) interval +
            RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathImag (polynomial source degree)
                origin direction) interval))) := by
  rw [polynomial_target_eq_add_perturbation]
  let margin := clearance.bound - normSq (source - target)
  have marginPositive : 0 < margin :=
    RFAP.ConstructiveFraction.sub_pos_direct small
  have dominance : ∀ point : Coordinate, interval.Contains point →
      margin ≤
        (RFAP.PathPolynomial.pathReal (polynomial source degree)
            origin direction).eval point ^ 2 +
          (RFAP.PathPolynomial.pathImag (polynomial source degree)
            origin direction).eval point ^ 2 -
          ((RFAP.PathPolynomial.pathReal
              (parameterPerturbation source target)
                origin direction).eval point ^ 2 +
            (RFAP.PathPolynomial.pathImag
              (parameterPerturbation source target)
                origin direction).eval point ^ 2) := by
    intro point inside
    have sourceLower := clearance.lower point inside
    calc
      margin = clearance.bound - normSq (source - target) := rfl
      _ ≤
          (RFAP.PathPolynomial.pathReal (polynomial source degree)
                origin direction).eval point ^ 2 +
            (RFAP.PathPolynomial.pathImag (polynomial source degree)
                origin direction).eval point ^ 2 -
              normSq (source - target) :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct sourceLower _
      _ = _ := by
        simp only [RFAP.PathPolynomial.eval_pathReal,
          RFAP.PathPolynomial.eval_pathImag,
          parameterPerturbation_eval, normSq]
  have sumReal : ∀ point : Coordinate,
      (RFAP.PathPolynomial.pathReal
          (polynomial source degree + parameterPerturbation source target)
            origin direction).eval point =
        (RFAP.PathPolynomial.pathReal (polynomial source degree)
            origin direction).eval point +
          (RFAP.PathPolynomial.pathReal
            (parameterPerturbation source target)
              origin direction).eval point := by
    intro point
    rw [RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathReal, eval_add]
    rfl
  have sumImag : ∀ point : Coordinate,
      (RFAP.PathPolynomial.pathImag
          (polynomial source degree + parameterPerturbation source target)
            origin direction).eval point =
        (RFAP.PathPolynomial.pathImag (polynomial source degree)
            origin direction).eval point +
          (RFAP.PathPolynomial.pathImag
            (parameterPerturbation source target)
              origin direction).eval point := by
    intro point
    rw [RFAP.PathPolynomial.eval_pathImag,
      RFAP.PathPolynomial.eval_pathImag,
      RFAP.PathPolynomial.eval_pathImag, eval_add]
    rfl
  let value := RFAP.WindingHomotopy.sumCertificate_of_normDominance
    margin marginPositive dominance sumReal sumImag
  exact
    { value := value
      bound := by
        dsimp only [value]
        simpa only [margin] using
          (RFAP.WindingHomotopy.sumCertificate_of_normDominance_bound
            margin marginPositive dominance sumReal sumImag) }

/-- Transport one complete affine-path clearance under the constant
parameter displacement.  This is the line analogue of `ownerMoveRouche` and
is needed because Paper-I shrinking tracks retain clearance on all four full
ambient lines, not merely on the local owner boundary. -/
def pathCertificateAfterMove
    {source target : Gaussian} (degree : RootDegree)
    {origin direction : Gaussian} {interval : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal (polynomial source degree)
        origin direction)
      (RFAP.PathPolynomial.pathImag (polynomial source degree)
        origin direction) interval)
    (small : normSq (source - target) < clearance.bound) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal (polynomial target degree)
        origin direction)
      (RFAP.PathPolynomial.pathImag (polynomial target degree)
        origin direction) interval :=
  (certifiedPathCertificateAfterMove degree clearance small).value

/-- Exact finite margin-and-Horner calculation cached by one transported
affine-path clearance. -/
@[simp] theorem pathCertificateAfterMove_bound
    {source target : Gaussian} (degree : RootDegree)
    {origin direction : Gaussian} {interval : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal (polynomial source degree)
        origin direction)
      (RFAP.PathPolynomial.pathImag (polynomial source degree)
        origin direction) interval)
    (small : normSq (source - target) < clearance.bound) :
    (pathCertificateAfterMove degree clearance small).bound =
      (clearance.bound - normSq (source - target)) ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathReal (polynomial source degree)
                origin direction) interval +
            RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathImag (polynomial source degree)
                origin direction) interval)) :=
  (certifiedPathCertificateAfterMove degree clearance small).bound

def verticalClearanceAfterMove
    {source target : Gaussian} (degree : RootDegree)
    {ambient : RFAP.Boxes.Box} {x : Coordinate}
    (clearance : RFAP.BoxClearance.VerticalLineClearance
      (polynomial source degree) ambient x)
    (small : normSq (source - target) < clearance.bound) :
    RFAP.BoxClearance.VerticalLineClearance
      (polynomial target degree) ambient x :=
  RFAP.BoxClearance.verticalOfPathCertificate
    (polynomial target degree) ambient x
      (pathCertificateAfterMove degree clearance.toPathCertificate small)

/-- Exact transported vertical-line clearance bound. -/
@[simp] theorem verticalClearanceAfterMove_bound
    {source target : Gaussian} (degree : RootDegree)
    {ambient : RFAP.Boxes.Box} {x : Coordinate}
    (clearance : RFAP.BoxClearance.VerticalLineClearance
      (polynomial source degree) ambient x)
    (small : normSq (source - target) < clearance.bound) :
    (verticalClearanceAfterMove degree clearance small).bound =
      (clearance.bound - normSq (source - target)) ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathReal (polynomial source degree)
                (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
              (RFAP.BoxClearance.verticalInterval ambient) +
            RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathImag (polynomial source degree)
                (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
              (RFAP.BoxClearance.verticalInterval ambient))) := by
  unfold verticalClearanceAfterMove
  rw [RFAP.BoxClearance.verticalOfPathCertificate_bound,
    pathCertificateAfterMove_bound,
    RFAP.BoxClearance.VerticalLineClearance.toPathCertificate_bound]

def horizontalClearanceAfterMove
    {source target : Gaussian} (degree : RootDegree)
    {ambient : RFAP.Boxes.Box} {y : Coordinate}
    (clearance : RFAP.BoxClearance.HorizontalLineClearance
      (polynomial source degree) ambient y)
    (small : normSq (source - target) < clearance.bound) :
    RFAP.BoxClearance.HorizontalLineClearance
      (polynomial target degree) ambient y :=
  RFAP.BoxClearance.horizontalOfPathCertificate
    (polynomial target degree) ambient y
      (pathCertificateAfterMove degree clearance.toPathCertificate small)

/-- Exact transported horizontal-line clearance bound. -/
@[simp] theorem horizontalClearanceAfterMove_bound
    {source target : Gaussian} (degree : RootDegree)
    {ambient : RFAP.Boxes.Box} {y : Coordinate}
    (clearance : RFAP.BoxClearance.HorizontalLineClearance
      (polynomial source degree) ambient y)
    (small : normSq (source - target) < clearance.bound) :
    (horizontalClearanceAfterMove degree clearance small).bound =
      (clearance.bound - normSq (source - target)) ^ 2 /
        (4 * max 1
          (RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathReal (polynomial source degree)
                (RFAP.Winding.horizontalBase y)
                  RFAP.Winding.horizontalDirection)
              (RFAP.BoxClearance.horizontalInterval ambient) +
            RFAP.PathClearance.evalSqBound
              (RFAP.PathPolynomial.pathImag (polynomial source degree)
                (RFAP.Winding.horizontalBase y)
                  RFAP.Winding.horizontalDirection)
              (RFAP.BoxClearance.horizontalInterval ambient))) := by
  unfold horizontalClearanceAfterMove
  rw [RFAP.BoxClearance.horizontalOfPathCertificate_bound,
    pathCertificateAfterMove_bound,
    RFAP.BoxClearance.HorizontalLineClearance.toPathCertificate_bound]

/-- The globally supported Paper-I track underlying one degree-indexed owner
of the independently isolated chamber frame. -/
def isolatedTrack
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneTrack (polynomial parameter degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree)) :=
  (isolationResult parameterNonzero degree degreeAtLeastTwo).trackAt
    (Fin.cast (polynomial_degree parameter degree).symm index)

@[simp] theorem isolatedTrack_initial_box_eq_chamber_owner
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (isolatedTrack parameterNonzero degree degreeAtLeastTwo
      (Fin.cast
        (chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
        index)).initial.box =
      ((chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
        index).box := by
  simp [isolatedTrack, chamberFrame,
    CCL.FiniteMonodromy.ChamberFrame.owner,
    CCL.ProgressivePolynomialRoots.OwnerFamily.ofResult,
    CCL.BoxRFAPBridge.Result.trackAt]

@[simp] theorem isolatedTrack_initial_clearance_bound_eq_chamber_owner
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (isolatedTrack parameterNonzero degree degreeAtLeastTwo
      (Fin.cast
        (chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
        index)).initial.clearance.bound =
      ((chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
        index).clearance.bound := by
  simp [isolatedTrack, chamberFrame,
    CCL.FiniteMonodromy.ChamberFrame.owner,
    CCL.ProgressivePolynomialRoots.OwnerFamily.ofResult,
    CCL.BoxRFAPBridge.Result.trackAt]

/-! ## Uniform robust owners on the unit circuit -/

/-- One finite refinement of an independently isolated owner to the common
source scale used by the robust Newton construction. -/
def unitRobustSourceState
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial parameter degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree)) :=
  let track := isolatedTrack parameterNonzero degree degreeAtLeastTwo index
  let radius :=
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  track.refine track.initial radius
    (unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)

theorem unitRobustSourceState_diagonalSq_le_radius_sq
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ^ 2 := by
  exact (isolatedTrack parameterNonzero degree degreeAtLeastTwo index).accurate
    (isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial
    (unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo)
    (unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)

theorem unitRobustSourceState_diagonalSq_le_radius
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo := by
  let sourceRadius :=
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < sourceRadius :=
    unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo
  have squareLeRadius : sourceRadius ^ 2 ≤ sourceRadius := by
    rw [pow_two]
    calc
      sourceRadius * sourceRadius ≤ 1 * sourceRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (unitRobustSourceRadius_le_one parameterUnit degree degreeAtLeastTwo)
          radiusPositive.le
      _ = sourceRadius := by ring1
  exact (unitRobustSourceState_diagonalSq_le_radius_sq parameterNonzero
    parameterUnit degree degreeAtLeastTwo index).trans squareLeRadius

theorem unitRobustSourceState_diagonalSq_le_quarterRadius_sq
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      (unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 :=
  (unitRobustSourceState_diagonalSq_le_radius parameterNonzero parameterUnit
    degree degreeAtLeastTwo index).trans
      (unitRobustSourceRadius_le_quarterRadius_sq parameterUnit degree
        degreeAtLeastTwo)

theorem unitRobustSourceState_anchorResidual_le_threshold
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.LocalExtraction.anchorResidualBound (polynomial parameter degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree))
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box ≤ (1 / 4 : Coordinate) := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let sourceRadius :=
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  have lipschitzPositive : 0 < lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient
  have scaled : sourceRadius * lipschitz ≤ (1 / 4 : Coordinate) :=
    (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
      (unitRobustSourceRadius_le_derivativeRatio parameterUnit degree
        degreeAtLeastTwo)
  calc
    RFAP.LocalExtraction.anchorResidualBound p ambient
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box =
      lipschitz *
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.diagonalSq := rfl
    _ ≤ lipschitz * sourceRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (unitRobustSourceState_diagonalSq_le_radius parameterNonzero
          parameterUnit degree degreeAtLeastTwo index) lipschitzPositive.le
    _ = sourceRadius * lipschitz := by ring1
    _ ≤ 1 / 4 := scaled

theorem unitRobustSourceState_anchorResidual_le_displacementBudget
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.LocalExtraction.anchorResidualBound (polynomial parameter degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree))
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box ≤
      (1 / 8 : Coordinate) *
        (unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let sourceRadius :=
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  let budget := (1 / 8 : Coordinate) *
    (unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2
  have lipschitzPositive : 0 < lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient
  have scaled : sourceRadius * lipschitz ≤ budget :=
    (RFAP.ConstructiveFraction.le_div_iff_pos lipschitzPositive).mp
      (unitRobustSourceRadius_le_displacementRatio parameterUnit degree
        degreeAtLeastTwo)
  calc
    RFAP.LocalExtraction.anchorResidualBound p ambient
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box =
      lipschitz *
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.diagonalSq := rfl
    _ ≤ lipschitz * sourceRadius :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (unitRobustSourceState_diagonalSq_le_radius parameterNonzero
          parameterUnit degree degreeAtLeastTwo index) lipschitzPositive.le
    _ = sourceRadius * lipschitz := by ring1
    _ ≤ budget := scaled

/-- The source refinement determines a completely explicit Newton centre.
All hypotheses are discharged by the common unit-parameter estimates rather
than by inspecting an individual owner's boundary clearance. -/
def unitRobustNewton
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.LocalExtraction.SeparatedNewtonCenterCertificate
      (polynomial parameter degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree))
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box
      (unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo
        (RFAP.GlobalWinding.largeSquareBox
          (polynomial parameter degree))) :=
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  RFAP.LocalExtraction.computeNewtonCenterOfRawWindingSeparated
    (polynomial parameter degree)
    (by rw [polynomial_degree]; exact degree.positive)
    (unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo _)
    source.refinesAmbient source.proper source.raw.rawWinding_ne
    (unitRobustSourceState_anchorResidual_le_threshold parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)

/-- The Newton correction is at most one quarter of the robust radius in
squared norm. -/
theorem unitRobustNewton_displacement_le_quarterRadius_sq
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    normSq
        ((unitRobustNewton parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).point -
          (unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box.anchor) ≤
      (unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let q := unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4
  have budget :=
    unitRobustSourceState_anchorResidual_le_displacementBudget
      parameterNonzero parameterUnit degree degreeAtLeastTwo index
  have marginPositive : 0 < separation.margin := separation.margin_pos
  calc
    normSq (newton.point - source.box.anchor) =
        normSq (RFAP.LocalExtraction.anchorNewtonCenter p source.box -
          source.box.anchor) := by rw [newton.point_eq]
    _ ≤ RFAP.LocalExtraction.anchorResidualBound p ambient source.box /
          separation.margin := newton.displacementMargin
    _ ≤ q ^ 2 :=
      (RFAP.ConstructiveFraction.div_le_iff_pos marginPositive).mpr (by
        calc
          RFAP.LocalExtraction.anchorResidualBound p ambient source.box ≤
              separation.margin * q ^ 2 := by
            simpa only [separation, unitParameterDerivativeSeparation, q] using
              budget
          _ = q ^ 2 * separation.margin := by ring1)

/-- The anchor selected by every common source refinement lies in the same
coarse rational radial envelope. -/
theorem unitRobustSourceState_anchor_normSq_le
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    normSq
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.anchor ≤ (5 / 2 : Coordinate) := by
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  have residualSmall :
      normSq (source.box.anchor ^ degree.value - parameter) ≤
        (1 / 4 : Coordinate) := by
    rw [← polynomial_eval parameter source.box.anchor degree]
    exact newton.residual.trans
      (unitRobustSourceState_anchorResidual_le_threshold parameterNonzero
        parameterUnit degree degreeAtLeastTwo index)
  exact normSq_le_five_halves_of_power_residual degree.positive parameterUnit
    residualSmall

/-- Dividing the already small robust radius by four gives the coordinate
budget used to place the Newton centre. -/
theorem unitRobustQuarterRadius_le_quarter
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4 ≤
      (1 / 4 : Coordinate) := by
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (show (0 : Coordinate) < 4 by
      exact RFAP.ConstructiveFraction.natCast_pos_direct (by decide))).mpr
  calc
    unitRobustRadius parameterUnit degree degreeAtLeastTwo ≤
        (1 / 8 : Coordinate) :=
      unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
    _ ≤ 1 := by decide
    _ = (1 / 4 : Coordinate) * 4 := by decide

/-- The fixed-radius Newton square attached to one degree-indexed owner. -/
def unitRobustBox
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) : RFAP.Boxes.Box :=
  RFAP.AffineWinding.centeredSquare
    (unitRobustNewton parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).point
    (unitRobustRadius parameterUnit degree degreeAtLeastTwo)
    (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le

theorem unitRobustBox_proper
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).Proper :=
  RFAP.AffineWinding.centeredSquare_proper _
    (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)

/-- Every robust Newton square lies directly in the common global square.
This is a finite coordinate calculation; it does not consume the original
owner's boundary clearance. -/
theorem unitRobustBox_refinesAmbient
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index).Refines
        (RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree)) := by
  let center := (unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index).point
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let q := r / 4
  have anchorNorm := unitRobustSourceState_anchor_normSq_le parameterNonzero
    parameterUnit degree degreeAtLeastTwo index
  have anchorBounds := RFAP.AffineWinding.coordinate_bounds_of_normSq_le
    (show (0 : Coordinate) ≤ 2 by decide)
    (anchorNorm.trans (show (5 / 2 : Coordinate) ≤ 2 ^ 2 by decide))
  have correctionBounds := RFAP.AffineWinding.coordinate_bounds_of_normSq_le
    (RFAP.ConstructiveFraction.div_nonneg_direct
      (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
      (by decide))
    (unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
  have qLe : q ≤ (1 / 4 : Coordinate) :=
    unitRobustQuarterRadius_le_quarter parameterUnit degree degreeAtLeastTwo
  have centerRealLower : -(9 / 4 : Coordinate) ≤ center.re := by
    calc
      -(9 / 4 : Coordinate) = -(1 / 4 : Coordinate) + -2 := by decide
      _ ≤ -q + -2 := add_le_add
        (RFAP.ConstructiveFraction.neg_le_neg_direct qLe) (le_refl _)
      _ ≤ (center - source.box.anchor).re + source.box.anchor.re :=
        add_le_add correctionBounds.1 anchorBounds.1
      _ = center.re := by simp only [sub_re]; ring1
  have centerRealUpper : center.re ≤ (9 / 4 : Coordinate) := by
    calc
      center.re = (center - source.box.anchor).re + source.box.anchor.re := by
        simp only [sub_re]; ring1
      _ ≤ q + 2 := add_le_add correctionBounds.2.1 anchorBounds.2.1
      _ ≤ (1 / 4 : Coordinate) + 2 := add_le_add qLe (le_refl _)
      _ = 9 / 4 := by decide
  have centerImagLower : -(9 / 4 : Coordinate) ≤ center.im := by
    calc
      -(9 / 4 : Coordinate) = -(1 / 4 : Coordinate) + -2 := by decide
      _ ≤ -q + -2 := add_le_add
        (RFAP.ConstructiveFraction.neg_le_neg_direct qLe) (le_refl _)
      _ ≤ (center - source.box.anchor).im + source.box.anchor.im :=
        add_le_add correctionBounds.2.2.1 anchorBounds.2.2.1
      _ = center.im := by simp only [sub_im]; ring1
  have centerImagUpper : center.im ≤ (9 / 4 : Coordinate) := by
    calc
      center.im = (center - source.box.anchor).im + source.box.anchor.im := by
        simp only [sub_im]; ring1
      _ ≤ q + 2 := add_le_add correctionBounds.2.2.2 anchorBounds.2.2.2
      _ ≤ (1 / 4 : Coordinate) + 2 := add_le_add qLe (le_refl _)
      _ = 9 / 4 := by decide
  have radiusLe : r ≤ (1 / 8 : Coordinate) :=
    unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
  have threeLeGlobal : (3 : Coordinate) ≤ (degree.value : Coordinate) + 1 := by
    have degreeTwo : (2 : Coordinate) ≤ (degree.value : Coordinate) :=
      RFAP.ConstructiveFraction.natCast_le_direct degreeAtLeastTwo
    calc
      (3 : Coordinate) = 2 + 1 := by decide
      _ ≤ (degree.value : Coordinate) + 1 :=
        add_le_add degreeTwo (le_refl 1)
  change
    -RFAP.GlobalWinding.denseLargeSquareRadius
        (polynomial parameter degree) ≤ center.re - r ∧
      center.re + r ≤ RFAP.GlobalWinding.denseLargeSquareRadius
        (polynomial parameter degree) ∧
      -RFAP.GlobalWinding.denseLargeSquareRadius
        (polynomial parameter degree) ≤ center.im - r ∧
      center.im + r ≤ RFAP.GlobalWinding.denseLargeSquareRadius
        (polynomial parameter degree)
  constructor
  · calc
      -RFAP.GlobalWinding.denseLargeSquareRadius
          (polynomial parameter degree) =
          -((degree.value : Coordinate) + 1) := by
        rw [denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
      _ ≤ -(3 : Coordinate) :=
        RFAP.ConstructiveFraction.neg_le_neg_direct threeLeGlobal
      _ ≤ -(9 / 4 : Coordinate) - 1 / 8 := by decide
      _ ≤ center.re - r :=
        RFAP.ConstructiveFraction.sub_le_sub_direct centerRealLower radiusLe
  constructor
  · calc
      center.re + r ≤ (9 / 4 : Coordinate) + 1 / 8 :=
        add_le_add centerRealUpper radiusLe
      _ ≤ 3 := by decide
      _ ≤ (degree.value : Coordinate) + 1 := threeLeGlobal
      _ = RFAP.GlobalWinding.denseLargeSquareRadius
          (polynomial parameter degree) := by
        rw [denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
  constructor
  · calc
      -RFAP.GlobalWinding.denseLargeSquareRadius
          (polynomial parameter degree) =
          -((degree.value : Coordinate) + 1) := by
        rw [denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]
      _ ≤ -(3 : Coordinate) :=
        RFAP.ConstructiveFraction.neg_le_neg_direct threeLeGlobal
      _ ≤ -(9 / 4 : Coordinate) - 1 / 8 := by decide
      _ ≤ center.im - r :=
        RFAP.ConstructiveFraction.sub_le_sub_direct centerImagLower radiusLe
  · calc
      center.im + r ≤ (9 / 4 : Coordinate) + 1 / 8 :=
        add_le_add centerImagUpper radiusLe
      _ ≤ 3 := by decide
      _ ≤ (degree.value : Coordinate) + 1 := threeLeGlobal
      _ = RFAP.GlobalWinding.denseLargeSquareRadius
          (polynomial parameter degree) := by
        rw [denseLargeSquareRadius_polynomial_of_unit parameterUnit degree]

/-- The quarter-radius Newton correction is, in particular, within the full
robust radius required by the winding transfer theorem. -/
theorem unitRobustNewton_displacement_le_radius_sq
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    normSq
        ((unitRobustNewton parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).point -
          (unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box.anchor) ≤
      unitRobustRadius parameterUnit degree degreeAtLeastTwo ^ 2 := by
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have quarterLe : r / 4 ≤ r :=
    (RFAP.ConstructiveFraction.div_le_iff_pos
      (show (0 : Coordinate) < 4 by
        exact RFAP.ConstructiveFraction.natCast_pos_direct (by decide))).mpr (by
      calc
        r = r * 1 := by ring1
        _ ≤ r * 4 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (by decide) (unitRobustRadius_pos parameterUnit degree
              degreeAtLeastTwo).le)
  exact (unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
    parameterUnit degree degreeAtLeastTwo index).trans
      (RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.div_nonneg_direct
          (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
          (by decide)) quarterLe 2)

/-- The robust box is definitionally the separated Newton square after
replacing the certificate's recorded point by its proved formula. -/
theorem unitRobustBox_eq_centeredNewtonSquare
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo index =
      RFAP.AffineWinding.centeredSquare
        (RFAP.LocalExtraction.anchorNewtonCenter
          (polynomial parameter degree)
          (unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box)
        (unitRobustRadius parameterUnit degree degreeAtLeastTwo)
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le := by
  unfold unitRobustBox
  rw [(unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index).point_eq]

/-- Every displayed point of a robust owner has uniformly small residual.
The estimate is obtained from the source-anchor residual, the explicit
Newton displacement, and the finite Horner Lipschitz majorant. -/
theorem unitRobustBox_residual_le
    {parameter point : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (inside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains point) :
    normSq ((polynomial parameter degree).eval point) ≤
      (1 / 32 : Coordinate) := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let lipschitz := RFAP.PolynomialBounds.denseLipschitzBound p ambient
  let eighth : Coordinate := 1 / 8
  have radiusPositive : 0 < r :=
    unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusSquareLe : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct radiusLeOne
          radiusPositive.le
      _ = r := by ring1
  have pointCenterDistance : normSq (point - newton.point) ≤ 2 * r ^ 2 := by
    exact RFAP.AffineWinding.centeredSquare_normSq_sub_center_le newton.point
      radiusPositive.le (by simpa only [unitRobustBox] using inside)
  have centerAnchorDistance :
      normSq (newton.point - source.box.anchor) ≤ r ^ 2 :=
    unitRobustNewton_displacement_le_radius_sq parameterNonzero parameterUnit
      degree degreeAtLeastTwo index
  have pointAnchorIdentity :
      point - source.box.anchor =
        (point - newton.point) + (newton.point - source.box.anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have pointAnchorDistance :
      normSq (point - source.box.anchor) ≤ 6 * r ^ 2 := by
    rw [pointAnchorIdentity]
    calc
      normSq ((point - newton.point) +
          (newton.point - source.box.anchor)) ≤
        2 * (normSq (point - newton.point) +
          normSq (newton.point - source.box.anchor)) :=
        normSq_add_le_two _ _
      _ ≤ 2 * (2 * r ^ 2 + r ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add pointCenterDistance centerAnchorDistance) (by decide)
      _ = 6 * r ^ 2 := by ring1
  have pointAmbient : ambient.Contains point :=
    (unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).contains inside
  have anchorAmbient : ambient.Contains source.box.anchor :=
    source.refinesAmbient.contains source.box.contains_anchor
  have variation :
      normSq (p.eval point - p.eval source.box.anchor) ≤
        6 * eighth ^ 3 := by
    have raw :=
      RFAP.PolynomialBounds.normSq_eval_sub_eval_le_denseLipschitzBound p
        pointAmbient anchorAmbient
    have lipschitzRadiusSquare : lipschitz * r ^ 2 ≤ eighth ^ 3 := by
      calc
        lipschitz * r ^ 2 ≤ lipschitz * r :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe
            (RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient).le
        _ = r * lipschitz := by ring1
        _ ≤ eighth ^ 3 := by
          simpa only [eighth] using
            unitRobustRadius_mul_lipschitz_le parameterUnit degree
              degreeAtLeastTwo
    calc
      normSq (p.eval point - p.eval source.box.anchor) ≤
          lipschitz * normSq (point - source.box.anchor) := raw
      _ ≤ lipschitz * (6 * r ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          pointAnchorDistance
          (RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient).le
      _ = 6 * (lipschitz * r ^ 2) := by ring1
      _ ≤ 6 * eighth ^ 3 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          lipschitzRadiusSquare (by decide)
  have quarterRadiusLeEighth : r / 4 ≤ eighth := by
    have inverseFourLeOne : (4 : Coordinate)⁻¹ ≤ 1 := by
      have quarterLeOne : (1 / 4 : Coordinate) ≤ 1 := by decide
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct] at quarterLeOne
      calc
        (4 : Coordinate)⁻¹ = 1 * (4 : Coordinate)⁻¹ := by ring1
        _ ≤ 1 := quarterLeOne
    calc
      r / 4 ≤ r := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        calc
          r * (4 : Coordinate)⁻¹ ≤ r * 1 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              inverseFourLeOne radiusPositive.le
          _ = r := by ring1
      _ ≤ eighth := by
        simpa only [eighth] using
          unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
  have anchorResidual : normSq (p.eval source.box.anchor) ≤ eighth ^ 3 := by
    have sourceBound :=
      unitRobustSourceState_anchorResidual_le_displacementBudget
      parameterNonzero parameterUnit degree degreeAtLeastTwo index
    have actual := newton.residual
    have squareBound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.div_nonneg_direct radiusPositive.le (by decide))
      quarterRadiusLeEighth 2
    calc
      normSq (p.eval source.box.anchor) ≤
          RFAP.LocalExtraction.anchorResidualBound p ambient source.box :=
        actual
      _ ≤ (1 / 8 : Coordinate) * (r / 4) ^ 2 := sourceBound
      _ ≤ eighth * eighth ^ 2 := by
        simpa only [eighth] using
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareBound
          (by decide)
      _ = eighth ^ 3 := by ring1
  have valueIdentity : p.eval point =
      (p.eval point - p.eval source.box.anchor) + p.eval source.box.anchor := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [valueIdentity]
  have coefficientBound : 14 * eighth ≤ (2 : Coordinate) := by
    simp only [eighth]
    decide
  have eighthSquareNonnegative : 0 ≤ eighth ^ 2 :=
    RFAP.ConstructiveFraction.pow_nonneg_direct
      (by simpa only [eighth] using
        (show (0 : Coordinate) ≤ 1 / 8 by decide)) 2
  have residualBudget : 14 * eighth ^ 3 ≤ 1 / 32 := by
    have squareNonnegative : 0 ≤ eighth ^ 2 :=
      eighthSquareNonnegative
    calc
      14 * eighth ^ 3 = (14 * eighth) * eighth ^ 2 := by ring1
      _ ≤ 2 * eighth ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          coefficientBound squareNonnegative
      _ = 1 / 32 := by simp only [eighth]; decide
  calc
    normSq ((p.eval point - p.eval source.box.anchor) +
        p.eval source.box.anchor) ≤
      2 * (normSq (p.eval point - p.eval source.box.anchor) +
        normSq (p.eval source.box.anchor)) := normSq_add_le_two _ _
    _ ≤ 2 * (6 * eighth ^ 3 + eighth ^ 3) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = 14 * eighth ^ 3 := by ring1
    _ ≤ 1 / 32 := residualBudget

/-- Each fixed robust owner has raw winding four. -/
theorem unitRobustBox_rawWindingFour
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.Winding.quadrupledBoxWinding (polynomial parameter degree)
      (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        index) = 4 := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have degreeTwo : 2 ≤ p.natDegree := by
    rw [polynomial_degree]
    exact degreeAtLeastTwo
  have targetRefines :
      (RFAP.AffineWinding.centeredSquare
        (RFAP.LocalExtraction.anchorNewtonCenter p source.box) r
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le).Refines
          ambient := by
    rw [← unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
      degree degreeAtLeastTwo index]
    exact unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
  have displacement :
      normSq (RFAP.LocalExtraction.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    rw [← newton.point_eq]
    exact unitRobustNewton_displacement_le_radius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index
  have taylor :
      2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient *
        r ^ 2) ≤ separation.margin := by
    simpa only [separation, unitParameterDerivativeSeparation] using
      unitRobustRadius_taylor parameterUnit degree degreeAtLeastTwo
  rw [unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
    degree degreeAtLeastTwo index]
  exact RFAP.NewtonWinding.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
    degreeTwo newton source.refinesAmbient
    (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
    targetRefines displacement taylor

/-- The coefficient-computed positive boundary clearance of a robust owner. -/
def unitRobustBoundaryClearance
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    RFAP.BoxClearance.BoundaryClearance (polynomial parameter degree)
      (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        index) := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let source := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have degreeTwo : 2 ≤ p.natDegree := by
    rw [polynomial_degree]
    exact degreeAtLeastTwo
  have targetRefines :
      (RFAP.AffineWinding.centeredSquare
        (RFAP.LocalExtraction.anchorNewtonCenter p source.box) r
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le).Refines
          ambient := by
    rw [← unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
      degree degreeAtLeastTwo index]
    exact unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
  have displacement :
      normSq (RFAP.LocalExtraction.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    rw [← newton.point_eq]
    exact unitRobustNewton_displacement_le_radius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index
  have taylor :
      2 * (36 * RFAP.PolynomialBounds.denseTaylorRemainderBound p ambient *
        r ^ 2) ≤ separation.margin := by
    simpa only [separation, unitParameterDerivativeSeparation] using
      unitRobustRadius_taylor parameterUnit degree degreeAtLeastTwo
  rw [unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
    degree degreeAtLeastTwo index]
  exact RFAP.NewtonWinding.separatedNewtonSquareBoundaryClearance degreeTwo
    newton source.refinesAmbient
    (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
    targetRefines displacement taylor

theorem unitRobustBoundaryClearance_bound
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
      let p := polynomial parameter degree
      let ambient := RFAP.GlobalWinding.largeSquareBox p
      let separation := unitParameterDerivativeSeparation parameterUnit degree
        degreeAtLeastTwo ambient
      let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
      RFAP.NewtonWinding.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
          p ambient r) := by
  unfold unitRobustBoundaryClearance
  rfl

/-- The common boundary budget expression for every robust owner at one unit
parameter.  It contains only finite coefficient majorants and the fixed
rational radius. -/
def unitRobustClearanceScale
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let separation := unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  RFAP.NewtonWinding.separatedNewtonDominanceMargin separation r ^ 2 /
    (4 * RFAP.NewtonWinding.separatedNewtonLinearizationMajorant p ambient r)

theorem unitRobustBoundaryClearance_bound_eq_scale
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
        unitRobustClearanceScale parameterUnit degree degreeAtLeastTwo := by
  exact unitRobustBoundaryClearance_bound parameterNonzero parameterUnit degree
    degreeAtLeastTwo index

/-- The common clearance scale depends on a unit parameter only through its
quadrance. -/
theorem unitRobustClearanceScale_eq_of_normSq_eq
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustClearanceScale sourceUnit degree degreeAtLeastTwo =
      unitRobustClearanceScale targetUnit degree degreeAtLeastTwo := by
  unfold unitRobustClearanceScale
    RFAP.NewtonWinding.separatedNewtonDominanceMargin
    RFAP.NewtonWinding.newtonErrorBudget
    RFAP.NewtonWinding.separatedNewtonLinearizationMajorant
  dsimp only [unitParameterDerivativeSeparation]
  rw [unitRobustRadius_eq_of_normSq_eq sourceUnit targetUnit equalNorm degree
      degreeAtLeastTwo,
    denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree,
    derivative_polynomial_eq source target degree,
    largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]

def unitReferenceParameter : Gaussian := 1

theorem unitReferenceParameter_unit : normSq unitReferenceParameter = 1 :=
  normSq_one

theorem unitReferenceParameter_nonzero : unitReferenceParameter ≠ 0 := by
  decide

/-- One parameter-free positive rational budget shared by all robust boxes on
the unit circuit. -/
def uniformRobustClearance (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  unitRobustClearanceScale unitReferenceParameter_unit degree degreeAtLeastTwo

theorem uniformRobustClearance_pos (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < uniformRobustClearance degree degreeAtLeastTwo := by
  let index : Fin degree.value := ⟨0, degree.positive⟩
  have positive :=
    (unitRobustBoundaryClearance unitReferenceParameter_nonzero
      unitReferenceParameter_unit degree degreeAtLeastTwo index).positive
  rw [unitRobustBoundaryClearance_bound_eq_scale] at positive
  exact positive

theorem unitRobustBoundaryClearance_uniform
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
        uniformRobustClearance degree degreeAtLeastTwo := by
  rw [unitRobustBoundaryClearance_bound_eq_scale]
  exact unitRobustClearanceScale_eq_of_normSq_eq parameterUnit
    unitReferenceParameter_unit
    (parameterUnit.trans unitReferenceParameter_unit.symm) degree
    degreeAtLeastTwo

/-- One explicit local owner at the common robust unit-circuit scale. -/
def unitRobustOwner
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    CCL.ProgressivePolynomialRoots.LocalOwner (polynomial parameter degree) :=
  { box := unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      index
    proper := unitRobustBox_proper parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
    clearance := unitRobustBoundaryClearance parameterNonzero parameterUnit
      degree degreeAtLeastTwo index
    rawWindingFour := unitRobustBox_rawWindingFour parameterNonzero
      parameterUnit degree degreeAtLeastTwo index }

/-- A small source box and a nearby proposed centre fit in the corresponding
centred square.  The proof checks the two displayed corners after a finite
quadrance estimate. -/
private theorem box_refines_centeredSquare_of_anchor_near
    {source : RFAP.Boxes.Box} {center : Gaussian} {q r : Coordinate}
    (qNonnegative : 0 ≤ q) (rNonnegative : 0 ≤ r)
    (sourceSmall : source.diagonalSq ≤ q ^ 2)
    (centerNear : normSq (center - source.anchor) ≤ q ^ 2)
    (twiceQLe : 2 * q ≤ r) :
    source.Refines (RFAP.AffineWinding.centeredSquare center r rNonnegative) := by
  have fourQSquareLe : 4 * q ^ 2 ≤ r ^ 2 := by
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) qNonnegative)
      twiceQLe 2
    calc
      4 * q ^ 2 = (2 * q) ^ 2 := by ring1
      _ ≤ r ^ 2 := powered
  have included : ∀ z : Gaussian, source.Contains z →
      (RFAP.AffineWinding.centeredSquare center r rNonnegative).Contains z := by
    intro z inside
    have pointNearAnchor := (source.normSq_sub_anchor_le inside).trans sourceSmall
    have reverseCenter : normSq (source.anchor - center) ≤ q ^ 2 := by
      calc
        normSq (source.anchor - center) = normSq (center - source.anchor) := by
          simp only [normSq, sub_re, sub_im]
          ring1
        _ ≤ q ^ 2 := centerNear
    have pointIdentity : z - center =
        (z - source.anchor) + (source.anchor - center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    have pointNearCenter : normSq (z - center) ≤ r ^ 2 := by
      rw [pointIdentity]
      calc
        normSq ((z - source.anchor) + (source.anchor - center)) ≤
            2 * (normSq (z - source.anchor) +
              normSq (source.anchor - center)) := normSq_add_le_two _ _
        _ ≤ 2 * (q ^ 2 + q ^ 2) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add pointNearAnchor reverseCenter) (by decide)
        _ = 4 * q ^ 2 := by ring1
        _ ≤ r ^ 2 := fourQSquareLe
    have bounds := RFAP.AffineWinding.coordinate_bounds_of_normSq_le
      rNonnegative pointNearCenter
    change center.re - r ≤ z.re ∧ z.re ≤ center.re + r ∧
      center.im - r ≤ z.im ∧ z.im ≤ center.im + r
    exact
      ⟨by
        calc
          center.re - r = -r + center.re := by ring1
          _ ≤ (z - center).re + center.re :=
            add_le_add bounds.1 (le_refl center.re)
          _ = z.re := by simp only [sub_re]; ring1,
       by
        calc
          z.re = (z - center).re + center.re := by
            simp only [sub_re]; ring1
          _ ≤ r + center.re := add_le_add bounds.2.1 (le_refl center.re)
          _ = center.re + r := by ring1,
       by
        calc
          center.im - r = -r + center.im := by ring1
          _ ≤ (z - center).im + center.im :=
            add_le_add bounds.2.2.1 (le_refl center.im)
          _ = z.im := by simp only [sub_im]; ring1,
       by
        calc
          z.im = (z - center).im + center.im := by
            simp only [sub_im]; ring1
          _ ≤ r + center.im := add_le_add bounds.2.2.2 (le_refl center.im)
          _ = center.im + r := by ring1⟩
  let upperRight : Gaussian := ⟨source.xUpper, source.yUpper⟩
  have anchorInside := included source.anchor source.contains_anchor
  have upperRightInside := included upperRight
    (show source.Contains upperRight from
      ⟨source.x_valid, le_rfl, source.y_valid, le_rfl⟩)
  exact ⟨anchorInside.1, upperRightInside.2.1,
    anchorInside.2.2.1, upperRightInside.2.2.2⟩

/-- The source state used to compute the Newton correction is retained inside
its resulting robust owner. -/
theorem unitRobustSourceState_refinesBox
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.Refines
        (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
          index) := by
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let q := r / 4
  have qNonnegative : (0 : Coordinate) ≤ q :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
      (by decide)
  have twiceQLe : 2 * q ≤ r := by
    have inverseFour : (4 : Coordinate)⁻¹ = 1 / 4 := by decide
    dsimp only [q]
    rw [RFAP.ExplicitField.div_eq_mul_inv, inverseFour]
    have coefficient : (2 : Coordinate) * (1 / 4) = 1 / 2 := by decide
    calc
      2 * (r * (1 / 4 : Coordinate)) =
          ((2 : Coordinate) * (1 / 4)) * r := by ring1
      _ = (1 / 2 : Coordinate) * r := by rw [coefficient]
      _ ≤ 1 * r :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) (unitRobustRadius_pos parameterUnit degree
            degreeAtLeastTwo).le
      _ = r := by ring1
  exact box_refines_centeredSquare_of_anchor_near qNonnegative
    (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
    (unitRobustSourceState_diagonalSq_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
    (unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
    twiceQLe

theorem unitRobustSourceState_refinesInitial
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.Refines
        (isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial.box :=
  (isolatedTrack parameterNonzero degree degreeAtLeastTwo index).nested
    (isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial
    (unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo)
    (unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)

/-- The two source states retain the original isolation family's positive
coordinate separation. -/
theorem unitRobustSourceState_pairwiseSeparated
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (left right : Fin degree.value) (different : left ≠ right) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo left).box.Separated
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right).box := by
  let castIndex : Fin degree.value →
      Fin (polynomial parameter degree).natDegree :=
    Fin.cast (polynomial_degree parameter degree).symm
  have castDifferent : castIndex left ≠ castIndex right := by
    intro equal
    apply different
    apply Fin.ext
    have values := congrArg (fun index => index.val) equal
    change left.val = right.val at values
    exact values
  have initialSeparated := CCL.BoxRFAPBridge.Result.trackAt_pairwiseSeparated
    (isolationResult parameterNonzero degree degreeAtLeastTwo)
    (castIndex left) (castIndex right) castDifferent
  exact RFAP.Boxes.Box.Separated.of_refines initialSeparated
    (unitRobustSourceState_refinesInitial parameterNonzero parameterUnit degree
      degreeAtLeastTwo left)
    (unitRobustSourceState_refinesInitial parameterNonzero parameterUnit degree
      degreeAtLeastTwo right)

/-- A radius-`r` square containing a displayed point lies in the radius-`2r`
square centred at that point. -/
private theorem centeredSquare_refines_double_at_member
    {center point : Gaussian} {r : Coordinate} (rNonnegative : 0 ≤ r)
    (inside :
      (RFAP.AffineWinding.centeredSquare center r rNonnegative).Contains point) :
    (RFAP.AffineWinding.centeredSquare center r rNonnegative).Refines
      (RFAP.AffineWinding.centeredSquare point (2 * r)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          rNonnegative)) := by
  change point.re - 2 * r ≤ center.re - r ∧
    center.re + r ≤ point.re + 2 * r ∧
    point.im - 2 * r ≤ center.im - r ∧
    center.im + r ≤ point.im + 2 * r
  exact
    ⟨by
      calc
        point.re - 2 * r ≤ center.re + r - 2 * r :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.1 (2 * r)
        _ = center.re - r := by ring1,
     by
      calc
        center.re + r = center.re - r + 2 * r := by ring1
        _ ≤ point.re + 2 * r := add_le_add inside.1 (le_refl (2 * r)),
     by
      calc
        point.im - 2 * r ≤ center.im + r - 2 * r :=
          RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.2.2 (2 * r)
        _ = center.im - r := by ring1,
     by
      calc
        center.im + r = center.im - r + 2 * r := by ring1
        _ ≤ point.im + 2 * r :=
          add_le_add inside.2.2.1 (le_refl (2 * r))⟩

/-- Distinct robust owners are positively separated.  If two closed squares
overlapped, their common displayed overlap point would put the two already
separated source tracks inside one radius-`2r` square, contradicting the
explicit derivative-separation threshold. -/
theorem unitRobustBox_pairwiseSeparated
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (left right : Fin degree.value) (different : left ≠ right) :
    (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      left).Separated
        (unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
          right) := by
  let p := polynomial parameter degree
  let ambient := RFAP.GlobalWinding.largeSquareBox p
  let separation := unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let leftBox := unitRobustBox parameterNonzero parameterUnit degree
    degreeAtLeastTwo left
  let rightBox := unitRobustBox parameterNonzero parameterUnit degree
    degreeAtLeastTwo right
  by_cases separated : leftBox.Separated rightBox
  · exact separated
  · let overlap := RFAP.Boxes.Box.overlapPoint leftBox rightBox
    have overlapInside :=
      RFAP.Boxes.Box.contains_overlapPoint_of_not_separated separated
    let common := RFAP.AffineWinding.centeredSquare overlap (2 * r)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le)
    have leftBoxCommon : leftBox.Refines common :=
      centeredSquare_refines_double_at_member
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
        overlapInside.1
    have rightBoxCommon : rightBox.Refines common :=
      centeredSquare_refines_double_at_member
        (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
        overlapInside.2
    have leftSourceCommon :
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo left).box.Refines common :=
      (unitRobustSourceState_refinesBox parameterNonzero parameterUnit degree
        degreeAtLeastTwo left).trans leftBoxCommon
    have rightSourceCommon :
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right).box.Refines common :=
      (unitRobustSourceState_refinesBox parameterNonzero parameterUnit degree
        degreeAtLeastTwo right).trans rightBoxCommon
    have commonSmall : common.diagonalSq <
        RFAP.TrackSeparation.separatedUniquenessDiagonalThreshold ambient
          separation := by
      calc
        common.diagonalSq = 8 * (2 * r) ^ 2 :=
          RFAP.AffineWinding.centeredSquare_diagonalSq overlap
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le)
        _ = 32 * r ^ 2 := by ring1
        _ < unitUniquenessDiagonalThreshold parameterUnit degree
            degreeAtLeastTwo :=
          thirtyTwo_mul_unitRobustRadius_sq_lt_uniqueness parameterUnit degree
            degreeAtLeastTwo
    exact False.elim
      (RFAP.TrackSeparation.separated_tracks_not_supported_in_small_common_box_of_separation
        (by rw [polynomial_degree]; exact degree.positive) separation
        (isolatedTrack parameterNonzero degree degreeAtLeastTwo left)
        (isolatedTrack parameterNonzero degree degreeAtLeastTwo right)
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo left)
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right)
        (unitRobustSourceState_pairwiseSeparated parameterNonzero parameterUnit
          degree degreeAtLeastTwo left right different)
        common leftSourceCommon rightSourceCommon commonSmall)

/-- The degree-many robust local owners at one exact unit parameter. -/
def unitRobustOwnerFamily
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial parameter degree) degree.value where
  owner := unitRobustOwner parameterNonzero parameterUnit degree degreeAtLeastTwo
  pairwiseSeparated := unitRobustBox_pairwiseSeparated parameterNonzero
    parameterUnit degree degreeAtLeastTwo

/-- The exact coefficient table equipped with the common-scale robust owner
family.  Maximality is unchanged because it is a statement about every
separated globally supported family for the same displayed polynomial. -/
def robustChamberFrame
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable parameter degree
  chamber := by
    let rawOwners := unitRobustOwnerFamily parameterNonzero parameterUnit degree
      degreeAtLeastTwo
    have countSame : degree.value =
        (coefficientTable parameter degree).degree := by
      rw [coefficientTable_degree]
    let owners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (coefficientTable parameter degree).polynomial
        (coefficientTable parameter degree).degree :=
      CCL.FiniteMonodromy.castOwnerFamilyFull
        (coefficientTable_polynomial parameter degree).symm countSame rawOwners
    let original := (chamberFrame parameterNonzero degree degreeAtLeastTwo).chamber
    exact
      { degreeAtLeastTwo := original.degreeAtLeastTwo
        squarefree := original.squarefree
        owners := owners
        referenceSmall := coefficientTable_allowances_lt parameter degree
          (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
            (coefficientTable parameter degree) original.squarefree owners)
        referenceMaximality := original.referenceMaximality }

@[simp] theorem robustChamberFrame_degree
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).degree = degree.value :=
  coefficientTable_degree parameter degree

@[simp] theorem robustChamberFrame_polynomial
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).polynomial = polynomial parameter degree :=
  coefficientTable_polynomial parameter degree

@[simp] theorem robustChamberFrame_owner_box
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).Index) :
    ((robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).owner index).box =
      unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        (Fin.cast
          (robustChamberFrame_degree parameterNonzero parameterUnit degree
            degreeAtLeastTwo)
          index) := by
  simp [robustChamberFrame, CCL.FiniteMonodromy.ChamberFrame.owner,
    unitRobustOwnerFamily, unitRobustOwner]

@[simp] theorem robustChamberFrame_owner_clearance_bound
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).Index) :
    ((robustChamberFrame parameterNonzero parameterUnit degree
      degreeAtLeastTwo).owner index).clearance.bound =
      (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
        degreeAtLeastTwo
        (Fin.cast
          (robustChamberFrame_degree parameterNonzero parameterUnit degree
            degreeAtLeastTwo)
          index)).bound := by
  simp [robustChamberFrame, CCL.FiniteMonodromy.ChamberFrame.owner,
    unitRobustOwnerFamily, unitRobustOwner]

/-! ## Canonical same-polynomial rebase to the robust frame -/

theorem isolationRobustCountEq
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (chamberFrame parameterNonzero degree degreeAtLeastTwo).degree =
      (robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo).degree := by
  rw [chamberFrame_degree, robustChamberFrame_degree]

def isolationRobustBridge
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    CCL.FiniteMonodromy.OwnerBridge
      (chamberFrame parameterNonzero degree degreeAtLeastTwo).polynomial
      (robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo).polynomial := by
  let degreeIndex : Fin degree.value := Fin.cast
    (chamberFrame_degree parameterNonzero degree degreeAtLeastTwo) index
  let state := unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo degreeIndex
  let owner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial parameter degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (CCL.FiniteMonodromy.OwnerBridge.reflexive owner).cast
    (chamberFrame_polynomial parameterNonzero degree degreeAtLeastTwo).symm
    (robustChamberFrame_polynomial parameterNonzero parameterUnit degree
      degreeAtLeastTwo).symm

@[simp] theorem isolationRobustBridge_box
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (chamberFrame parameterNonzero degree degreeAtLeastTwo).Index) :
    (isolationRobustBridge parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box =
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo
        (Fin.cast
          (chamberFrame_degree parameterNonzero degree degreeAtLeastTwo)
          index)).box := by
  unfold isolationRobustBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_box]
  rfl

/-- The independently isolated frame and the robust frame have a canonical
identity-labelled overlap through the source state used by the Newton step. -/
def isolationRobustOverlap
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.ChamberOverlap
      (chamberFrame parameterNonzero degree degreeAtLeastTwo)
      (robustChamberFrame parameterNonzero parameterUnit degree
        degreeAtLeastTwo) where
  matching := CCL.FiniteMonodromy.FiniteBijection.cast
    (isolationRobustCountEq parameterNonzero parameterUnit degree
      degreeAtLeastTwo)
  bridge := isolationRobustBridge parameterNonzero parameterUnit degree
    degreeAtLeastTwo
  bridge_refines_left := by
    intro index
    rw [isolationRobustBridge_box]
    let degreeIndex : Fin degree.value := Fin.cast
      (chamberFrame_degree parameterNonzero degree degreeAtLeastTwo) index
    calc
      (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo degreeIndex).box.Refines
          (isolatedTrack parameterNonzero degree degreeAtLeastTwo
            degreeIndex).initial.box :=
        unitRobustSourceState_refinesInitial parameterNonzero parameterUnit
          degree degreeAtLeastTwo degreeIndex
      _ = ((chamberFrame parameterNonzero degree degreeAtLeastTwo).owner
          index).box :=
        isolatedTrack_initial_box_eq_chamber_owner parameterNonzero degree
          degreeAtLeastTwo index
  bridge_refines_right := by
    intro index
    rw [isolationRobustBridge_box,
      CCL.FiniteMonodromy.FiniteBijection.cast_forward,
      robustChamberFrame_owner_box]
    exact unitRobustSourceState_refinesBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo _

/-! ## Uniform moves between robust unit-parameter frames -/

theorem nonzero_of_normSq_eq_one {parameter : Gaussian}
    (unit : normSq parameter = 1) : parameter ≠ 0 := by
  intro zero
  rw [zero, normSq_zero] at unit
  exact (by decide : (0 : Coordinate) ≠ 1) unit

/-- A single parameter-distance comparison suffices for every robust owner. -/
structure UnitMoveSmall
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Prop where
  distance : normSq (source - target) <
    uniformRobustClearance degree degreeAtLeastTwo
  liftMargin : normSq (source - target) ≤ (1 / 128 : Coordinate)

theorem UnitMoveSmall.reflexive
    {parameter : Gaussian} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitMoveSmall parameterUnit parameterUnit degree degreeAtLeastTwo where
  distance := by
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact uniformRobustClearance_pos degree degreeAtLeastTwo
  liftMargin := by
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
    exact RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 1) (by decide)).le
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 128) (by decide)).le

theorem UnitMoveSmall.owner
    {source target : Gaussian}
    {sourceUnit : normSq source = 1} {targetUnit : normSq target = 1}
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    normSq (source - target) <
      (unitRobustOwner (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
        degreeAtLeastTwo index).clearance.bound := by
  change normSq (source - target) <
    (unitRobustBoundaryClearance (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).bound
  rw [unitRobustBoundaryClearance_uniform]
  exact small.distance

theorem unitMoveCountEq
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo).degree = (coefficientTable target degree).degree := by
  rw [robustChamberFrame_degree, coefficientTable_degree]

def unitMoveSourceIndex
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (coefficientTable target degree).degree) :
    (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo).Index :=
  Fin.cast (unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo).symm
    index

/-- Target-parameter chamber which retains the robust source boxes after the
finite Rouché comparison. -/
def unitTransportedFrame
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable target degree
  chamber := by
    let sourceFrame := robustChamberFrame
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
    let sourceIndex : Fin (coefficientTable target degree).degree →
        sourceFrame.Index :=
      unitMoveSourceIndex sourceUnit targetUnit degree degreeAtLeastTwo
    let sourceOwner :
        (index : Fin (coefficientTable target degree).degree) →
          CCL.ProgressivePolynomialRoots.LocalOwner
            (polynomial source degree) := fun index =>
      CCL.FiniteMonodromy.castOwner
        (robustChamberFrame_polynomial
          (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo)
        (sourceFrame.owner (sourceIndex index))
    let rawOwners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (polynomial target degree)
        (coefficientTable target degree).degree :=
      { owner := fun index => transportedOwner degree (sourceOwner index) (by
          dsimp only [sourceOwner]
          rw [CCL.FiniteMonodromy.castOwner_clearance_bound]
          have sourceDegreeIndex : Fin degree.value := Fin.cast
            (robustChamberFrame_degree
              (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
              degreeAtLeastTwo) (sourceIndex index)
          rw [robustChamberFrame_owner_clearance_bound]
          exact small.owner sourceDegreeIndex)
        pairwiseSeparated := by
          intro left right different
          have sourceDifferent : sourceIndex left ≠ sourceIndex right := by
            intro equal
            apply different
            apply Fin.ext
            have values := congrArg (fun index => index.val) equal
            change left.val = right.val at values
            exact values
          have separated := sourceFrame.pairwiseSeparated
            (sourceIndex left) (sourceIndex right) sourceDifferent
          have leftBox : (sourceOwner left).box =
              (sourceFrame.owner (sourceIndex left)).box :=
            CCL.FiniteMonodromy.castOwner_box _ _
          have rightBox : (sourceOwner right).box =
              (sourceFrame.owner (sourceIndex right)).box :=
            CCL.FiniteMonodromy.castOwner_box _ _
          simpa only [transportedOwner,
            CCL.FiniteMonodromy.OwnerBridge.rightOwner,
            CCL.FiniteMonodromy.OwnerBridge.ofForward,
            leftBox, rightBox] using separated }
    let owners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (coefficientTable target degree).polynomial
        (coefficientTable target degree).degree :=
      CCL.FiniteMonodromy.castOwnerFamily
        (coefficientTable_polynomial target degree).symm rawOwners
    let targetOriginal :=
      (chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).chamber
    exact
      { degreeAtLeastTwo := targetOriginal.degreeAtLeastTwo
        squarefree := targetOriginal.squarefree
        owners := owners
        referenceSmall := coefficientTable_allowances_lt target degree
          (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
            (coefficientTable target degree) targetOriginal.squarefree owners)
        referenceMaximality := targetOriginal.referenceMaximality }

@[simp] theorem unitTransportedFrame_degree
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).degree = degree.value :=
  coefficientTable_degree target degree

@[simp] theorem unitTransportedFrame_polynomial
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).polynomial = polynomial target degree :=
  coefficientTable_polynomial target degree

@[simp] theorem unitTransportedFrame_owner_box
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    ((unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
      small).owner
        (Fin.cast (unitMoveCountEq sourceUnit targetUnit degree
          degreeAtLeastTwo) index)).box =
      ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  simp only [CCL.FiniteMonodromy.ChamberFrame.owner, unitTransportedFrame,
    unitMoveSourceIndex, CCL.FiniteMonodromy.castOwnerFamily_owner_box,
    CCL.FiniteMonodromy.castOwner_box, transportedOwner,
    CCL.FiniteMonodromy.OwnerBridge.rightOwner,
    CCL.FiniteMonodromy.OwnerBridge.ofForward]
  congr 1

def unitMoveBridge
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    CCL.FiniteMonodromy.OwnerBridge
      (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo).polynomial
      (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).polynomial := by
  let owner := CCL.FiniteMonodromy.castOwner
    (robustChamberFrame_polynomial (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo)
    ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo).owner index)
  let raw := CCL.FiniteMonodromy.OwnerBridge.ofForward owner
    (ownerMoveRouche degree owner (by
      dsimp only [owner]
      rw [CCL.FiniteMonodromy.castOwner_clearance_bound,
        robustChamberFrame_owner_clearance_bound]
      exact small.owner _))
  exact raw.cast
    (robustChamberFrame_polynomial (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).symm
    (unitTransportedFrame_polynomial sourceUnit targetUnit degree
      degreeAtLeastTwo small).symm

@[simp] theorem unitMoveBridge_box
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box =
      ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  rw [unitMoveBridge, CCL.FiniteMonodromy.OwnerBridge.cast_box]
  exact CCL.FiniteMonodromy.castOwner_box _ _

def unitMoveOverlap
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberOverlap
      (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo)
      (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small) where
  matching := CCL.FiniteMonodromy.FiniteBijection.cast
    (unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo)
  bridge := unitMoveBridge sourceUnit targetUnit degree degreeAtLeastTwo small
  bridge_refines_left := by
    intro index
    rw [unitMoveBridge_box]
    exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [unitMoveBridge_box,
      CCL.FiniteMonodromy.FiniteBijection.cast_forward,
      unitTransportedFrame_owner_box]
    exact RFAP.Boxes.Box.refines_refl _

/-- Source robust-frame index normalized to `Fin d` for the numerical
transport program. -/
def unitMoveSourceDegreeIndex
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (coefficientTable target degree).degree) : Fin degree.value :=
  Fin.cast
    (robustChamberFrame_degree (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
      degree degreeAtLeastTwo)
    (unitMoveSourceIndex sourceUnit targetUnit degree degreeAtLeastTwo index)

/-- The moved robust owner as a raw target-polynomial state in the common
unit-parameter global square. -/
def unitTransportedRawState
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.RawSubdivision.RawWindingState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  let sourceOwner := unitRobustOwner (nonzero_of_normSq_eq_one sourceUnit)
    sourceUnit degree degreeAtLeastTwo index
  let targetOwner := transportedOwner degree sourceOwner (small.owner index)
  exact
    { box := sourceOwner.box
      refinesAmbient := by
        rw [← largeSquareBox_polynomial_eq_of_normSq_eq
          (sourceUnit.trans targetUnit.symm) degree]
        exact unitRobustBox_refinesAmbient
          (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo index
      proper := targetOwner.proper
      clearance := targetOwner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← targetOwner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }

@[simp] theorem unitTransportedRawState_box
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (unitTransportedRawState sourceUnit targetUnit degree degreeAtLeastTwo
      small index).box =
      unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
        degreeAtLeastTwo index := rfl

def unitTransportedExtraction
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :=
  RFAP.NewtonBand.extract
    (by rw [polynomial_degree]; exact degreeAtLeastTwo)
    (squarefree (nonzero_of_normSq_eq_one targetUnit) degree)
    (isolationInput (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitTransportedRawState sourceUnit targetUnit degree degreeAtLeastTwo
      small index) (epsilon := (1 : Coordinate)) (by decide)

def unitTransportedIsolatedState
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  let extracted := unitTransportedExtraction sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }

theorem unitTransportedIsolatedState_refines
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (unitTransportedIsolatedState sourceUnit targetUnit degree degreeAtLeastTwo
      small index).box.Refines
        (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo index) := by
  change (unitTransportedExtraction sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.Refines _
  rw [← unitTransportedRawState_box sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact (unitTransportedExtraction sourceUnit targetUnit degree
    degreeAtLeastTwo small index).strictCurrent.refines

def unitTransportedIsolatedTrack
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  RFAP.ShrinkingTrack.ofInitial
    (by rw [polynomial_degree]; exact degreeAtLeastTwo)
    (squarefree (nonzero_of_normSq_eq_one targetUnit) degree)
    (isolationInput (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitTransportedIsolatedState sourceUnit targetUnit degree degreeAtLeastTwo
      small index)

/-- Globally supported transported track corresponding to one intermediate
frame index. -/
def unitTransportedFrameTrack
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  unitTransportedIsolatedTrack sourceUnit targetUnit degree degreeAtLeastTwo
    small (unitMoveSourceDegreeIndex sourceUnit targetUnit degree
      degreeAtLeastTwo index)

theorem unitTransportedFrameTrack_initial_refines
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small index).initial.box.Refines
      ((unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box := by
  let sourceIndex := unitMoveSourceIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  let degreeIndex := unitMoveSourceDegreeIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  have targetIndex :
      Fin.cast (unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo)
          sourceIndex = index := by
    apply Fin.ext
    rfl
  have transportedBox :
      ((unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box =
        ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
          degree degreeAtLeastTwo).owner sourceIndex).box := by
    rw [← targetIndex]
    exact unitTransportedFrame_owner_box sourceUnit targetUnit degree
      degreeAtLeastTwo small sourceIndex
  have sourceRobustBox :
      ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo).owner sourceIndex).box =
        unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
          degreeAtLeastTwo degreeIndex := by
    exact robustChamberFrame_owner_box (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo sourceIndex
  rw [transportedBox, sourceRobustBox]
  exact unitTransportedIsolatedState_refines sourceUnit targetUnit degree
    degreeAtLeastTwo small degreeIndex

theorem unitTransportedFrameTracks_pairwise
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (left right : Fin (coefficientTable target degree).degree)
    (different : left ≠ right) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small left).initial.box.Separated
      (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small right).initial.box :=
  RFAP.Boxes.Box.Separated.of_refines
    (CCL.FiniteMonodromy.ChamberFrame.pairwiseSeparated
      (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo small)
      left right different)
      (unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small left)
      (unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small right)

theorem unitTransportedFrameTrack_supported
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
      small index).initial.box.Refines
      (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.support := by
  change (unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).initial.box.Refines
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree))
  exact (unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).initial.refinesAmbient

def unitTransportedOwnerSelection
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.Maximality.OwnerSelection
      (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation
      (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small index) :=
  (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
    degreeAtLeastTwo).boxes.ownership
      (unitTransportedFrameTrack sourceUnit targetUnit degree degreeAtLeastTwo
        small index)
      (unitTransportedFrameTrack_supported sourceUnit targetUnit degree
        degreeAtLeastTwo small index)

theorem unitTargetTrackCountEq
    {target : Gaussian} (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
      (coefficientTable target degree).degree := by
  calc
    (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
        (polynomial target degree).natDegree :=
      (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks_length
    _ = degree.value := polynomial_degree target degree
    _ = (coefficientTable target degree).degree :=
      (coefficientTable_degree target degree).symm

def unitRebaseMap
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Fin (coefficientTable target degree).degree →
      Fin (coefficientTable target degree).degree := fun index =>
  Fin.cast (unitTargetTrackCountEq targetUnit degree degreeAtLeastTwo)
    (unitTransportedOwnerSelection sourceUnit targetUnit degree degreeAtLeastTwo
      small index).owner

theorem unitRebaseMap_injective
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    Function.Injective
      (unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small) := by
  let output :=
    (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).boxes.isolation
  let family : Fin (coefficientTable target degree).degree →
      RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
    fun index => unitTransportedFrameTrack sourceUnit targetUnit degree
      degreeAtLeastTwo small index
  have rawInjective : Function.Injective (fun index =>
      (unitTransportedOwnerSelection sourceUnit targetUnit degree
        degreeAtLeastTwo small index).owner) := by
    change Function.Injective (fun index =>
      (RFAP.Maximality.selectOutputOwner
        (by rw [polynomial_degree]; exact degreeAtLeastTwo)
        (squarefree (nonzero_of_normSq_eq_one targetUnit) degree)
        (isolationInput (nonzero_of_normSq_eq_one targetUnit) degree
          degreeAtLeastTwo).elimination output (family index)
        (unitTransportedFrameTrack_supported sourceUnit targetUnit degree
          degreeAtLeastTwo small index)).owner)
    exact RFAP.Maximality.selectedOwner_injective
      (by rw [polynomial_degree]; exact degreeAtLeastTwo)
      (squarefree (nonzero_of_normSq_eq_one targetUnit) degree)
      (isolationInput (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).elimination output family
      (unitTransportedFrameTrack_supported sourceUnit targetUnit degree
        degreeAtLeastTwo small)
      (unitTransportedFrameTracks_pairwise sourceUnit targetUnit degree
        degreeAtLeastTwo small)
  intro left right equal
  apply rawInjective
  apply Fin.ext
  simpa only [unitRebaseMap, Fin.val_cast] using
    congrArg (fun index => index.val) equal

def unitRebaseMatching
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.FiniteBijection
      (coefficientTable target degree).degree
      (coefficientTable target degree).degree :=
  CCL.FiniteMonodromy.FiniteBijection.ofInjectiveEndomap
    (unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small)
    (unitRebaseMap_injective sourceUnit targetUnit degree degreeAtLeastTwo small)

@[simp] theorem unitRebaseMatching_forward
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo small).forward
        index =
      unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small index :=
  rfl

@[simp] theorem unitTargetTrack_get_box_eq_chamber_owner
    {target : Gaussian} (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin
      (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.length) :
    ((isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.get index).initial.box =
      ((chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        (Fin.cast (unitTargetTrackCountEq targetUnit degree degreeAtLeastTwo)
          index)).box := by
  simp [chamberFrame, CCL.FiniteMonodromy.ChamberFrame.owner,
    CCL.ProgressivePolynomialRoots.OwnerFamily.ofResult,
    CCL.BoxRFAPBridge.Result.trackAt, RFAP.ExactIsolation.Output.trackAt,
    RFAP.ExactIsolation.Output.trackIndex]

def unitRebaseRefinedState
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  let output :=
    (isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).boxes.isolation
  let track := unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  track.refine track.initial
    (RFAP.Maximality.assignmentRadius (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) output)
    (RFAP.Maximality.assignmentRadius_pos (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) output)

def unitRebaseBridge
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    CCL.FiniteMonodromy.OwnerBridge
      (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).polynomial
      (chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).polynomial := by
  let state := unitRebaseRefinedState sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let owner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial target degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (CCL.FiniteMonodromy.OwnerBridge.reflexive owner).cast
    (unitTransportedFrame_polynomial sourceUnit targetUnit degree
      degreeAtLeastTwo small).symm
    (chamberFrame_polynomial (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).symm

@[simp] theorem unitRebaseBridge_box
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box =
      (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box := by
  unfold unitRebaseBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_box]
  rfl

theorem unitSelectedTargetBox_eq_rebaseMap_owner
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    ((isolationResult (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).boxes.isolation.tracks.get
      (unitTransportedOwnerSelection sourceUnit targetUnit degree
        degreeAtLeastTwo small index).owner).initial.box =
      ((chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        (unitRebaseMap sourceUnit targetUnit degree degreeAtLeastTwo small
          index)).box :=
  unitTargetTrack_get_box_eq_chamber_owner targetUnit degree degreeAtLeastTwo _

theorem unitRebaseBridge_refines_transported
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo
        small).owner index).box := by
  rw [unitRebaseBridge_box]
  exact ((unitTransportedFrameTrack sourceUnit targetUnit degree
    degreeAtLeastTwo small index).nested _ _ _).trans
      (unitTransportedFrameTrack_initial_refines sourceUnit targetUnit degree
        degreeAtLeastTwo small index)

theorem unitRebaseBridge_refines_target
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner
        ((unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
          small).forward index)).box := by
  have refined :=
    (unitTransportedOwnerSelection sourceUnit targetUnit degree degreeAtLeastTwo
      small index).strict.refines
  rw [unitRebaseBridge_box, unitRebaseMatching_forward]
  rw [← unitSelectedTargetBox_eq_rebaseMap_owner sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact refined

def unitRebaseOverlap
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberOverlap
      (unitTransportedFrame sourceUnit targetUnit degree degreeAtLeastTwo small)
      (chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo) where
  matching := unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo
    small
  bridge := unitRebaseBridge sourceUnit targetUnit degree degreeAtLeastTwo small
  bridge_refines_left := unitRebaseBridge_refines_transported sourceUnit
    targetUnit degree degreeAtLeastTwo small
  bridge_refines_right := unitRebaseBridge_refines_target sourceUnit targetUnit
    degree degreeAtLeastTwo small

/-- Two winding-one states carried by the same winding-one region cannot be
positively separated.  A further strict refinement of each state would split
the region into two contributions of raw winding at least four, contradicting
the region's displayed raw winding four. -/
private theorem windingOneStates_not_separated_in_region
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : RFAP.LocalExtraction.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (region left right : RFAP.ShrinkingTrack.WindingOneState p ambient)
    (leftRefines : left.box.Refines region.box)
    (rightRefines : right.box.Refines region.box) :
    ¬left.box.Separated right.box := by
  intro separated
  let leftTrack := RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree
    elimination left
  let rightTrack := RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo squarefree
    elimination right
  let leftSmall := leftTrack.refine left 1 (by decide)
  let rightSmall := rightTrack.refine right 1 (by decide)
  have leftNested : leftSmall.box.Refines left.box :=
    leftTrack.nested left 1 (by decide)
  have rightNested : rightSmall.box.Refines right.box :=
    rightTrack.nested right 1 (by decide)
  have smallSeparated : leftSmall.box.Separated rightSmall.box :=
    separated.of_refines leftNested rightNested
  have leftInside : leftSmall.box.StrictInterior region.box :=
    (leftTrack.strict left 1 (by decide)).trans_refines leftRefines
  have rightInside : rightSmall.box.StrictInterior region.box :=
    (rightTrack.strict right 1 (by decide)).trans_refines rightRefines
  let clearRegion : RFAP.ExactIsolation.ClearRegion p ambient :=
    { box := region.box
      refinesAmbient := region.refinesAmbient
      proper := region.proper
      clearance := region.clearance }
  have atLeastEight := RFAP.Maximality.region_rawWinding_ge_eight_of_separated
    degreeAtLeastTwo squarefree elimination clearRegion leftSmall rightSmall
      leftInside rightInside smallSeparated
  have exactlyFour := region.rawWindingFour
  dsimp only [clearRegion] at atLeastEight
  rw [exactlyFour] at atLeastEight
  omega

/-- Axis-aligned rational boxes contain every displayed affine point between
two of their members. -/
private theorem box_contains_line
    (box : RFAP.Boxes.Box) {start finish : Gaussian}
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    box.Contains (RFAP.PathPolynomial.line start (finish - start) time) := by
  have oneMinusNonnegative : (0 : Coordinate) ≤ 1 - time :=
    RFAP.ConstructiveFraction.sub_nonneg_direct timeInside.2
  have lineReal :
      (RFAP.PathPolynomial.line start (finish - start) time).re =
        (1 - time) * start.re + time * finish.re := by
    simp only [RFAP.PathPolynomial.line, add_re, mul_re, sub_re,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im]
    ring1
  have lineImag :
      (RFAP.PathPolynomial.line start (finish - start) time).im =
        (1 - time) * start.im + time * finish.im := by
    simp only [RFAP.PathPolynomial.line, add_im, mul_im, sub_im,
      RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im]
    ring1
  change box.xLower ≤
      (RFAP.PathPolynomial.line start (finish - start) time).re ∧
    (RFAP.PathPolynomial.line start (finish - start) time).re ≤ box.xUpper ∧
    box.yLower ≤
      (RFAP.PathPolynomial.line start (finish - start) time).im ∧
    (RFAP.PathPolynomial.line start (finish - start) time).im ≤ box.yUpper
  rw [lineReal, lineImag]
  exact
    ⟨by
      calc
        box.xLower = (1 - time) * box.xLower + time * box.xLower := by ring1
        _ ≤ (1 - time) * start.re + time * finish.re :=
          add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              startInside.1 oneMinusNonnegative)
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              finishInside.1 timeInside.1),
     by
      calc
        (1 - time) * start.re + time * finish.re ≤
            (1 - time) * box.xUpper + time * box.xUpper :=
          add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              startInside.2.1 oneMinusNonnegative)
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              finishInside.2.1 timeInside.1)
        _ = box.xUpper := by ring1,
     by
      calc
        box.yLower = (1 - time) * box.yLower + time * box.yLower := by ring1
        _ ≤ (1 - time) * start.im + time * finish.im :=
          add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              startInside.2.2.1 oneMinusNonnegative)
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              finishInside.2.2.1 timeInside.1),
     by
      calc
        (1 - time) * start.im + time * finish.im ≤
            (1 - time) * box.yUpper + time * box.yUpper :=
          add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              startInside.2.2.2 oneMinusNonnegative)
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              finishInside.2.2.2 timeInside.1)
        _ = box.yUpper := by ring1⟩

/-- A point on the displayed parameter segment is no farther from its source
than the displayed endpoint displacement. -/
private theorem normSq_source_sub_line_le
    (source target : Gaussian) {time : Coordinate}
    (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    normSq (source -
        RFAP.PathPolynomial.line source (target - source) time) ≤
      normSq (source - target) := by
  have identity :
      source - RFAP.PathPolynomial.line source (target - source) time =
        RFAP.PathPolynomial.ofCoordinate time * (source - target) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.PathPolynomial.line, RFAP.PathPolynomial.ofCoordinate_re,
        RFAP.PathPolynomial.ofCoordinate_im, add_re, add_im, mul_re, mul_im,
        sub_re, sub_im] <;>
      ring1
  have timeSquareLeOne : time ^ 2 ≤ (1 : Coordinate) := by
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct timeInside.1
      timeInside.2 2
    simpa only [one_pow] using powered
  rw [identity, normSq_mul]
  have scalarNorm :
      normSq (RFAP.PathPolynomial.ofCoordinate time) = time ^ 2 := by
    simp only [normSq, RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im]
    ring1
  rw [scalarNorm]
  calc
    time ^ 2 * normSq (source - target) ≤
        1 * normSq (source - target) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        timeSquareLeOne (normSq_nonneg _)
    _ = normSq (source - target) := by ring1

private theorem one_over_one_twenty_eight_le_one_over_thirty_two :
    (1 / 128 : Coordinate) ≤ 1 / 32 := by
  have denominatorPositive : (0 : Coordinate) < 128 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 128) (by decide)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  have thirtyTwoNonzero : (32 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 32) (by decide)).ne'
  have inverseThirtyTwo : (1 / 32 : Coordinate) * 32 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 32 thirtyTwoNonzero
  calc
    (1 : Coordinate) ≤ 4 := by decide
    _ = 1 * 4 := by ring1
    _ = ((1 / 32 : Coordinate) * 32) * 4 := by rw [inverseThirtyTwo]
    _ = (1 / 32 : Coordinate) * 128 := by ring1

private theorem one_over_thirty_two_le_one_over_four :
    (1 / 32 : Coordinate) ≤ 1 / 4 := by
  have denominatorPositive : (0 : Coordinate) < 32 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 32) (by decide)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
  have fourNonzero : (4 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 4) (by decide)).ne'
  have inverseFour : (1 / 4 : Coordinate) * 4 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 4 fourNonzero
  calc
    (1 : Coordinate) ≤ 8 := by decide
    _ = 1 * 8 := by ring1
    _ = ((1 / 4 : Coordinate) * 4) * 8 := by rw [inverseFour]
    _ = (1 / 4 : Coordinate) * 32 := by ring1

private theorem twice_two_thirty_seconds_eq_eighth :
    2 * ((1 / 32 : Coordinate) + 1 / 32) = 1 / 8 := by
  have eightNonzero : (8 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 8) (by decide)).ne'
  have inverseEighth : (8 : Coordinate) * (1 / 8) = 1 := by
    calc
      (8 : Coordinate) * (1 / 8) = (1 / 8) * 8 := by ring1
      _ = 1 := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        1 8 eightNonzero
  have thirtyTwoNonzero : (32 : Coordinate) ≠ 0 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 32) (by decide)).ne'
  have inverseThirtyTwo : (1 / 32 : Coordinate) * 32 = 1 :=
    RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 32 thirtyTwoNonzero
  have thirtySecond : (1 / 32 : Coordinate) =
      2 * (1 / 8 : Coordinate) ^ 2 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne thirtyTwoNonzero
    calc
      (1 / 32 : Coordinate) * 32 = 1 := inverseThirtyTwo
      _ = (8 * (1 / 8 : Coordinate)) *
          (8 * (1 / 8 : Coordinate)) := by rw [inverseEighth]; ring1
      _ = (2 * (1 / 8 : Coordinate) ^ 2) * 32 := by ring1
  rw [thirtySecond]
  calc
    2 * (2 * (1 / 8 : Coordinate) ^ 2 +
        2 * (1 / 8 : Coordinate) ^ 2) =
      (8 * (1 / 8 : Coordinate)) * (1 / 8 : Coordinate) := by ring1
    _ = 1 * (1 / 8 : Coordinate) := by rw [inverseEighth]
    _ = 1 / 8 := by ring1

theorem unitRobustSegment_residual_le
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    normSq ((RFAP.PathPolynomial.line start (finish - start) time) ^
        degree.value - parameter) ≤ (1 / 32 : Coordinate) := by
  let point := RFAP.PathPolynomial.line start (finish - start) time
  have pointInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains point :=
    box_contains_line _ startInside finishInside timeInside
  have residual := unitRobustBox_residual_le parameterNonzero parameterUnit
    degree degreeAtLeastTwo index pointInside
  rw [polynomial_eval] at residual
  exact residual

theorem unitRobustSegment_power_lower
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    (1 / 4 : Coordinate) ≤
      normSq (RFAP.PathPolynomial.line start (finish - start) time) ^
        degree.value := by
  apply one_fourth_le_normSq_power_of_residual_le_quarter parameterUnit
  exact (unitRobustSegment_residual_le parameterNonzero parameterUnit degree
    degreeAtLeastTwo index startInside finishInside timeInside).trans
      one_over_thirty_two_le_one_over_four

private theorem pow_le_self_of_nonnegative_le_one
    {value : Coordinate} (nonnegative : 0 ≤ value) (atMostOne : value ≤ 1)
    {exponent : Nat} (positive : 0 < exponent) : value ^ exponent ≤ value := by
  obtain ⟨preceding, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  rw [pow_succ]
  have precedingPower := RFAP.ConstructiveFraction.pow_le_pow_direct
    nonnegative atMostOne preceding
  calc
    value ^ preceding * value ≤ 1 * value :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (by simpa only [one_pow] using precedingPower) nonnegative
    _ = value := by ring1

theorem unitRobustSegment_coordinate_lower
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    (1 / 4 : Coordinate) ≤
      normSq (RFAP.PathPolynomial.line start (finish - start) time) := by
  let value := normSq (RFAP.PathPolynomial.line start (finish - start) time)
  have powerLower := unitRobustSegment_power_lower parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside
    timeInside
  by_cases oneLe : (1 : Coordinate) ≤ value
  · exact (show (1 / 4 : Coordinate) ≤ 1 by decide).trans oneLe
  · have valueLeOne : value ≤ 1 := (lt_of_not_ge oneLe).le
    exact powerLower.trans
      (pow_le_self_of_nonnegative_le_one (normSq_nonneg _) valueLeOne
        degree.positive)

/-- Every positive coordinate power has a displayed clearance along a robust
lift segment. -/
def unitRobustSegmentCoordinatePowerCertificate
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    (exponent : Nat) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal
        (RFAP.GlobalWinding.coordinatePositivePower exponent)
        start (finish - start))
      (RFAP.PathPolynomial.pathImag
        (RFAP.GlobalWinding.coordinatePositivePower exponent)
        start (finish - start))
      { lower := 0, upper := 1, valid := by decide } :=
  { bound := (1 / 4 : Coordinate) ^ (exponent + 1)
    positive := RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide))) _
    lower := by
      intro time timeInside
      have coordinateLower := unitRobustSegment_coordinate_lower
        parameterNonzero parameterUnit degree degreeAtLeastTwo index startInside
        finishInside timeInside
      have powered := RFAP.ConstructiveFraction.pow_le_pow_direct (by decide)
        coordinateLower (exponent + 1)
      rw [← normSq_pow] at powered
      simpa only [RFAP.PathPolynomial.eval_pathReal,
        RFAP.PathPolynomial.eval_pathImag,
        RFAP.GlobalWinding.coordinatePositivePower_eval, normSq] using powered }

private theorem path_value_ne_zero_of_certificate
    (p : GaussianPolynomial) (origin direction : Gaussian)
    {interval : RFAP.PathClearance.Interval}
    (certificate : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal p origin direction)
      (RFAP.PathPolynomial.pathImag p origin direction) interval)
    {time : Coordinate} (inside : interval.Contains time) :
    p.eval (RFAP.PathPolynomial.line origin direction time) ≠ 0 := by
  intro zero
  have pair := certificate.eval_ne_zero inside
  rw [RFAP.PathPolynomial.eval_pathReal,
    RFAP.PathPolynomial.eval_pathImag, zero] at pair
  simp only [zero_re, zero_im] at pair
  exact pair.elim (fun impossible => impossible rfl)
    (fun impossible => impossible rfl)

/-- Product formula for two successive positive coordinate powers along one
robust lift segment. -/
theorem unitRobustSegmentProductFormula
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish)
    (exponent : Nat) :
    RFAP.WindingProduct.LineProductFormula
      (RFAP.GlobalWinding.coordinatePositivePower exponent)
      RFAP.GlobalWinding.coordinatePolynomial start (finish - start) 0 1 := by
  let left := unitRobustSegmentCoordinatePowerCertificate parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside exponent
  let right := unitRobustSegmentCoordinatePowerCertificate parameterNonzero
    parameterUnit degree degreeAtLeastTwo index startInside finishInside 0
  apply RFAP.WindingProduct.lineProductFormula_of_clearances
    (RFAP.GlobalWinding.coordinatePositivePower exponent)
    RFAP.GlobalWinding.coordinatePolynomial start (finish - start)
    (by decide) left right
  · exact path_value_ne_zero_of_certificate _ _ _ left
      (show ({ lower := 0, upper := 1, valid := by decide } :
        RFAP.PathClearance.Interval).Contains 0 from ⟨le_rfl, by decide⟩)
  · simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      path_value_ne_zero_of_certificate
        (RFAP.GlobalWinding.coordinatePositivePower 0) start (finish - start)
        right
        (show ({ lower := 0, upper := 1, valid := by decide } :
          RFAP.PathClearance.Interval).Contains 0 from ⟨le_rfl, by decide⟩)
  · exact path_value_ne_zero_of_certificate _ _ _ left
      (show ({ lower := 0, upper := 1, valid := by decide } :
        RFAP.PathClearance.Interval).Contains 1 from ⟨by decide, le_rfl⟩)
  · simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      path_value_ne_zero_of_certificate
        (RFAP.GlobalWinding.coordinatePositivePower 0) start (finish - start)
        right
        (show ({ lower := 0, upper := 1, valid := by decide } :
          RFAP.PathClearance.Interval).Contains 1 from ⟨by decide, le_rfl⟩)

theorem unitRobustSegment_parameter_residual_le_eighth
    {source target start finish : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    normSq
        ((RFAP.PathPolynomial.line start (finish - start) time) ^ degree.value -
          RFAP.PathPolynomial.line source (target - source) time) ≤
      (1 / 8 : Coordinate) := by
  let liftPoint := RFAP.PathPolynomial.line start (finish - start) time
  let parameterPoint := RFAP.PathPolynomial.line source (target - source) time
  have liftResidual : normSq (liftPoint ^ degree.value - source) ≤
      (1 / 32 : Coordinate) :=
    unitRobustSegment_residual_le (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index startInside finishInside timeInside
  have parameterDistance : normSq (source - parameterPoint) ≤
      (1 / 128 : Coordinate) :=
    (normSq_source_sub_line_le source target timeInside).trans small.liftMargin
  have residualIdentity :
      liftPoint ^ degree.value - parameterPoint =
        (liftPoint ^ degree.value - source) + (source - parameterPoint) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring1
  rw [residualIdentity]
  calc
    normSq ((liftPoint ^ degree.value - source) +
        (source - parameterPoint)) ≤
      2 * (normSq (liftPoint ^ degree.value - source) +
        normSq (source - parameterPoint)) := normSq_add_le_two _ _
    _ ≤ 2 * ((1 / 32 : Coordinate) + 1 / 128) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add liftResidual parameterDistance) (by decide)
    _ ≤ 2 * ((1 / 32 : Coordinate) + 1 / 32) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_refl _) one_over_one_twenty_eight_le_one_over_thirty_two)
        (by decide)
    _ = 1 / 8 := twice_two_thirty_seconds_eq_eighth

theorem unitRobustSegment_constantTarget_residual_le_eighth
    {source target start finish : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    normSq
        ((RFAP.PathPolynomial.line start (finish - start) time) ^ degree.value -
          target) ≤ (1 / 8 : Coordinate) := by
  let liftPoint := RFAP.PathPolynomial.line start (finish - start) time
  have liftResidual : normSq (liftPoint ^ degree.value - source) ≤
      (1 / 32 : Coordinate) :=
    unitRobustSegment_residual_le (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index startInside finishInside timeInside
  have residualIdentity :
      liftPoint ^ degree.value - target =
        (liftPoint ^ degree.value - source) + (source - target) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring1
  rw [residualIdentity]
  calc
    normSq ((liftPoint ^ degree.value - source) + (source - target)) ≤
      2 * (normSq (liftPoint ^ degree.value - source) +
        normSq (source - target)) := normSq_add_le_two _ _
    _ ≤ 2 * ((1 / 32 : Coordinate) + 1 / 128) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add liftResidual small.liftMargin) (by decide)
    _ ≤ 2 * ((1 / 32 : Coordinate) + 1 / 32) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_refl _) one_over_one_twenty_eight_le_one_over_thirty_two)
        (by decide)
    _ = 1 / 8 := twice_two_thirty_seconds_eq_eighth

/-- Quantitative nonvanishing certificate for the positive power of any
segment retained in one robust owner. -/
def unitRobustSegmentPowerCertificate
    {parameter start finish : Gaussian}
    (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).Contains finish) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal
        (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
        start (finish - start))
      (RFAP.PathPolynomial.pathImag
        (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
        start (finish - start))
      { lower := 0, upper := 1, valid := by decide } := by
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.sub_add_cancel degree.positive
  exact
    { bound := 1 / 4
      positive := RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
        (RFAP.ConstructiveFraction.natCast_pos_direct (n := 4) (by decide))
      lower := by
        intro time timeInside
        have lower := unitRobustSegment_power_lower parameterNonzero
          parameterUnit degree degreeAtLeastTwo index startInside finishInside
          timeInside
        rw [← exponent] at lower
        rw [← normSq_pow] at lower
        simpa only [RFAP.PathPolynomial.eval_pathReal,
          RFAP.PathPolynomial.eval_pathImag,
          RFAP.GlobalWinding.coordinatePositivePower_eval, normSq] using lower }

/-- Edgewise finite Rouché formula from a displayed residual estimate. -/
private theorem unitRobustSegmentHomotopy_of_residual
    {source parameterStart parameterFinish start finish : Gaussian}
    (sourceUnit : normSq source = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    (residual : ∀ {time : Coordinate},
      (0 : Coordinate) ≤ time ∧ time ≤ 1 →
      normSq
          ((RFAP.PathPolynomial.line start (finish - start) time) ^ degree.value -
            RFAP.PathPolynomial.line parameterStart
              (parameterFinish - parameterStart) time) ≤
        (1 / 8 : Coordinate)) :
    RFAP.PolygonWinding.SegmentHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial start finish parameterStart
        parameterFinish := by
  let power := RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1)
  let coordinate := RFAP.GlobalWinding.coordinatePolynomial
  let A := RFAP.PathPolynomial.pathReal power start (finish - start)
  let B := RFAP.PathPolynomial.pathImag power start (finish - start)
  let U := RFAP.PathPolynomial.pathReal coordinate parameterStart
    (parameterFinish - parameterStart)
  let V := RFAP.PathPolynomial.pathImag coordinate parameterStart
    (parameterFinish - parameterStart)
  let C := U - A
  let D := V - B
  let interval : RFAP.PathClearance.Interval :=
    { lower := 0, upper := 1, valid := by decide }
  let clearance : RFAP.PathClearance.Certificate A B interval :=
    unitRobustSegmentPowerCertificate
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      index startInside finishInside
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.sub_add_cancel degree.positive
  have startNonzero : power.eval start ≠ 0 := by
    intro zero
    have pair := clearance.eval_ne_zero
      (x := (0 : Coordinate)) (show interval.Contains 0 from ⟨le_rfl, by decide⟩)
    simp only [A, B, RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag, RFAP.PolygonWinding.line_segment_zero,
      zero, zero_re, zero_im] at pair
    exact pair.elim (fun impossible => impossible rfl)
      (fun impossible => impossible rfl)
  have finishNonzero : power.eval finish ≠ 0 := by
    intro zero
    have pair := clearance.eval_ne_zero
      (x := (1 : Coordinate)) (show interval.Contains 1 from ⟨by decide, le_rfl⟩)
    simp only [A, B, RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag, RFAP.PolygonWinding.line_segment_one,
      zero, zero_re, zero_im] at pair
    exact pair.elim (fun impossible => impossible rfl)
      (fun impossible => impossible rfl)
  refine
    { sourceStartNonzero := startNonzero
      sourceFinishNonzero := finishNonzero
      data := ?_ }
  apply RFAP.WindingHomotopy.lineData_of_normDominance
    (A := A) (B := B) (C := C) (D := D) (U := U) (V := V)
    (root := interval) (by decide) clearance (1 / 8) (by decide)
  · intro time timeInside
    have powerLower := unitRobustSegment_power_lower
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      index startInside finishInside timeInside
    have errorUpper := residual timeInside
    have powerCoordinates : (1 / 4 : Coordinate) ≤
        A.eval time ^ 2 + B.eval time ^ 2 := by
      rw [← normSq_pow] at powerLower
      rw [← exponent] at powerLower
      simpa only [A, B, power, RFAP.PathPolynomial.eval_pathReal,
        RFAP.PathPolynomial.eval_pathImag,
        RFAP.GlobalWinding.coordinatePositivePower_eval, normSq] using powerLower
    have errorCoordinates : C.eval time ^ 2 + D.eval time ^ 2 ≤
        (1 / 8 : Coordinate) := by
      calc
        C.eval time ^ 2 + D.eval time ^ 2 =
            normSq
              (RFAP.PathPolynomial.line parameterStart
                  (parameterFinish - parameterStart) time -
                (RFAP.PathPolynomial.line start (finish - start) time) ^
                  degree.value) := by
          simp only [C, D, U, V, A, B, power, coordinate, eval_sub,
            RFAP.PathPolynomial.eval_pathReal,
            RFAP.PathPolynomial.eval_pathImag,
            RFAP.GlobalWinding.coordinatePositivePower_eval,
            RFAP.GlobalWinding.coordinatePolynomial_eval, exponent, normSq,
            sub_re, sub_im]
        _ = normSq
              ((RFAP.PathPolynomial.line start (finish - start) time) ^
                  degree.value -
                RFAP.PathPolynomial.line parameterStart
                  (parameterFinish - parameterStart) time) := by
          simp only [normSq, sub_re, sub_im]
          ring1
        _ ≤ 1 / 8 := errorUpper
    calc
      (1 / 8 : Coordinate) = 1 / 4 - 1 / 8 := by decide
      _ ≤ (A.eval time ^ 2 + B.eval time ^ 2) -
          (C.eval time ^ 2 + D.eval time ^ 2) :=
        RFAP.ConstructiveFraction.sub_le_sub_direct powerCoordinates
          errorCoordinates
  · intro time
    simp only [C, U, A, eval_sub]
    ring1
  · intro time
    simp only [D, V, B, eval_sub]
    ring1

/-- Edgewise finite Rouché formula comparing a robust lifted segment with
the synchronized parameter segment. -/
theorem unitRobustSegmentHomotopy
    {source target start finish : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish) :
    RFAP.PolygonWinding.SegmentHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial start finish source target := by
  apply unitRobustSegmentHomotopy_of_residual sourceUnit degree degreeAtLeastTwo
    index startInside finishInside
  intro time timeInside
  exact unitRobustSegment_parameter_residual_le_eighth sourceUnit targetUnit
    degree degreeAtLeastTwo small index startInside finishInside timeInside

private theorem line_same_endpoint (point : Gaussian) (time : Coordinate) :
    RFAP.PathPolynomial.line point (point - point) time = point := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.PathPolynomial.line, RFAP.PathPolynomial.ofCoordinate_re,
      RFAP.PathPolynomial.ofCoordinate_im, add_re, add_im, mul_re, mul_im,
      sub_re, sub_im] <;>
    ring1

/-- The two connector edges after a parameter move are compared with the
constant target parameter. -/
theorem unitRobustSegmentConstantTargetHomotopy
    {source target start finish : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish) :
    RFAP.PolygonWinding.SegmentHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial start finish target target := by
  apply unitRobustSegmentHomotopy_of_residual sourceUnit degree degreeAtLeastTwo
    index startInside finishInside
  intro time timeInside
  rw [line_same_endpoint]
  exact unitRobustSegment_constantTarget_residual_le_eighth sourceUnit
    targetUnit degree degreeAtLeastTwo small index startInside finishInside
    timeInside

/-- Degree-normalized target owner reached by the same-polynomial rebase in
one small unit move. -/
def unitMoveTargetDegreeIndex
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) : Fin degree.value :=
  Fin.cast
    (chamberFrame_degree (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo)
    ((unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo small).forward
      index)

/-- Independently isolated target state containing both halves of the robust
rebase. -/
def unitRebaseTargetRegion
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  (isolatedTrack (nonzero_of_normSq_eq_one targetUnit) degree degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)).initial

/-- Source state from which the target robust Newton square was constructed. -/
def unitRebaseTargetSource
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  unitRobustSourceState (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
    degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)

theorem unitRebaseRefinedState_refines_targetRegion
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box := by
  let targetIndex :=
    (unitRebaseMatching sourceUnit targetUnit degree degreeAtLeastTwo small).forward
      index
  have regionBox :
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box =
      ((chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree
        degreeAtLeastTwo).owner targetIndex).box := by
    exact isolatedTrack_initial_box_eq_chamber_owner
      (nonzero_of_normSq_eq_one targetUnit) degree degreeAtLeastTwo targetIndex
  rw [regionBox]
  have refined := unitRebaseBridge_refines_target sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  rw [unitRebaseBridge_box] at refined
  exact refined

theorem unitRebaseTargetSource_refines_targetRegion
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo
        small index).box :=
  unitRobustSourceState_refinesInitial
    (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small index)

/-- The two explicitly computed rebase states overlap inside their common
independently isolated target owner. -/
theorem unitRebaseStates_not_separated
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    ¬(unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Separated
      (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box := by
  exact windingOneStates_not_separated_in_region
    (by rw [polynomial_degree]; exact degreeAtLeastTwo)
    (squarefree (nonzero_of_normSq_eq_one targetUnit) degree)
    (isolationInput (nonzero_of_normSq_eq_one targetUnit) degree
      degreeAtLeastTwo).elimination
    (unitRebaseTargetRegion sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index)
    (unitRebaseRefinedState_refines_targetRegion sourceUnit targetUnit degree
      degreeAtLeastTwo small index)
    (unitRebaseTargetSource_refines_targetRegion sourceUnit targetUnit degree
      degreeAtLeastTwo small index)

/-- Explicit rational point shared by the rebase bridge and the source state
of its target robust owner. -/
def unitRebaseRobustOverlapPoint
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) : Gaussian :=
  RFAP.Boxes.Box.overlapPoint
    (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box
    (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box

theorem unitRebaseRobustOverlapPoint_inside
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Contains
        (unitRebaseRobustOverlapPoint sourceUnit targetUnit degree
          degreeAtLeastTwo small index) ∧
      (unitRebaseTargetSource sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.Contains
        (unitRebaseRobustOverlapPoint sourceUnit targetUnit degree
          degreeAtLeastTwo small index) :=
  RFAP.Boxes.Box.contains_overlapPoint_of_not_separated
    (unitRebaseStates_not_separated sourceUnit targetUnit degree
      degreeAtLeastTwo small index)

/-- Index of a source robust owner in the intermediate target-parameter
frame of one small move. -/
def unitMoveTransportedIndex
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Fin (coefficientTable target degree).degree :=
  Fin.cast (unitMoveCountEq sourceUnit targetUnit degree degreeAtLeastTwo) index

def unitMoveSourceDegreeIndexFromFrame
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Fin degree.value :=
  Fin.cast (robustChamberFrame_degree (nonzero_of_normSq_eq_one sourceUnit)
    sourceUnit degree degreeAtLeastTwo) index

def unitMoveTargetDegreeIndexFromSource
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Fin degree.value :=
  unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)

def unitMoveBridgeState
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :=
  unitRebaseRefinedState sourceUnit targetUnit degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)

def unitMoveOverlapPoint
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Gaussian :=
  unitRebaseRobustOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo
    small (unitMoveTransportedIndex sourceUnit targetUnit degree
      degreeAtLeastTwo index)

theorem unitMoveBridgeState_refines_sourceOwner
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.Refines
      ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
        degree degreeAtLeastTwo).owner index).box := by
  have refined := unitRebaseBridge_refines_transported sourceUnit targetUnit
    degree degreeAtLeastTwo small
    (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
      index)
  rw [unitRebaseBridge_box] at refined
  rw [← unitTransportedFrame_owner_box sourceUnit targetUnit degree
    degreeAtLeastTwo small index]
  exact refined

theorem unitMoveOverlapPoint_inside_sourceOwner
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit
      degree degreeAtLeastTwo).owner index).box.Contains
      (unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  exact (unitMoveBridgeState_refines_sourceOwner sourceUnit targetUnit degree
    degreeAtLeastTwo small index).contains
      (unitRebaseRobustOverlapPoint_inside sourceUnit targetUnit degree
        degreeAtLeastTwo small
        (unitMoveTransportedIndex sourceUnit targetUnit degree degreeAtLeastTwo
          index)).1

theorem unitMoveOverlapPoint_inside_targetRobustBox
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).Contains
      (unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let transported := unitMoveTransportedIndex sourceUnit targetUnit degree
    degreeAtLeastTwo index
  have overlapInside := (unitRebaseRobustOverlapPoint_inside sourceUnit
    targetUnit degree degreeAtLeastTwo small transported).2
  exact (unitRobustSourceState_refinesBox
    (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
    (unitMoveTargetDegreeIndex sourceUnit targetUnit degree degreeAtLeastTwo
      small transported)).contains overlapInside

def unitMoveLiftBase
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (_targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : Gaussian :=
  ((robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
    degreeAtLeastTwo).owner index).box.anchor

def unitMoveLiftVertices
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) : List Gaussian :=
  [(unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
      index).box.anchor,
    unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
      index,
    (unitRobustBox (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).anchor]

def unitMoveParameterVertices (target : Gaussian) : List Gaussian :=
  [target, target, target]

theorem unitMoveLiftBase_inside_sourceRobustBox
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index) := by
  unfold unitMoveLiftBase unitMoveSourceDegreeIndexFromFrame
  rw [robustChamberFrame_owner_box]
  exact RFAP.Boxes.Box.contains_anchor _

theorem unitMoveBridgeAnchor_inside_sourceRobustBox
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.anchor := by
  have inside := (unitMoveBridgeState_refines_sourceOwner sourceUnit targetUnit
    degree degreeAtLeastTwo small index).contains
      (unitMoveBridgeState sourceUnit targetUnit degree degreeAtLeastTwo small
        index).box.contains_anchor
  rw [robustChamberFrame_owner_box] at inside
  exact inside

theorem unitMoveOverlapPoint_inside_sourceRobustBox
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
      degreeAtLeastTwo
      (unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit degree
        degreeAtLeastTwo index)).Contains
      (unitMoveOverlapPoint sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  have inside := unitMoveOverlapPoint_inside_sourceOwner sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  rw [robustChamberFrame_owner_box] at inside
  exact inside

theorem unitMoveTargetAnchor_inside_targetRobustBox
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).Contains
      (unitRobustBox (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
        degreeAtLeastTwo
        (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
          degreeAtLeastTwo small index)).anchor :=
  RFAP.Boxes.Box.contains_anchor _

/-- The three rational lift edges of one small move, synchronized with one
parameter edge followed by two stationary target edges. -/
theorem unitMoveLiftHomotopy
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    RFAP.PolygonWinding.ChainHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial
      (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index)
      source (unitMoveParameterVertices target) := by
  let sourceIndex := unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (unitRobustBox (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  change RFAP.PolygonWinding.ChainHomotopyFormula _ _
    (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor] source [target, target, target]
  exact .cons
    (unitRobustSegmentHomotopy sourceUnit targetUnit degree degreeAtLeastTwo
      small sourceIndex
      (unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo index)
      (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo small index))
    (.cons
      (unitRobustSegmentConstantTargetHomotopy sourceUnit targetUnit degree
        degreeAtLeastTwo small sourceIndex
        (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index))
      (.cons
        (unitRobustSegmentConstantTargetHomotopy targetUnit targetUnit degree
          degreeAtLeastTwo (UnitMoveSmall.reflexive targetUnit degree
            degreeAtLeastTwo) targetIndex
          (unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index)
          (unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index))
        (.nil targetAnchor target)))

theorem unitMoveLiftProductFormula
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index)
    (exponent : Nat) :
    RFAP.PolygonWinding.ChainProductFormula
      (RFAP.GlobalWinding.coordinatePositivePower exponent)
      RFAP.GlobalWinding.coordinatePolynomial
      (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let sourceIndex := unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (unitRobustBox (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  change RFAP.PolygonWinding.ChainProductFormula _ _
    (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor]
  exact .cons
    (unitRobustSegmentProductFormula
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      sourceIndex
      (unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo index)
      (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
        degreeAtLeastTwo small index) exponent)
    (.cons
      (unitRobustSegmentProductFormula
        (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) exponent)
      (.cons
        (unitRobustSegmentProductFormula
          (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
          targetIndex
          (unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index)
          (unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit
            degree degreeAtLeastTwo small index) exponent)
        (.nil targetAnchor)))

/-- The same three robust connector edges carry constructive modulo-four
phase formulas for the coordinate path itself. -/
def unitMoveLiftPhaseFormula
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    RFAP.PolygonWinding.ChainPhaseFormula
      RFAP.GlobalWinding.coordinatePolynomial
      (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
      (unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
        index) := by
  let sourceIndex := unitMoveSourceDegreeIndexFromFrame sourceUnit targetUnit
    degree degreeAtLeastTwo index
  let targetIndex := unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit
    degree degreeAtLeastTwo small index
  let bridgeAnchor := (unitMoveBridgeState sourceUnit targetUnit degree
    degreeAtLeastTwo small index).box.anchor
  let overlap := unitMoveOverlapPoint sourceUnit targetUnit degree
    degreeAtLeastTwo small index
  let targetAnchor := (unitRobustBox (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeAtLeastTwo targetIndex).anchor
  have firstCertificate : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal RFAP.GlobalWinding.coordinatePolynomial
        (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (bridgeAnchor -
          unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index))
      (RFAP.PathPolynomial.pathImag RFAP.GlobalWinding.coordinatePolynomial
        (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (bridgeAnchor -
          unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      unitRobustSegmentCoordinatePowerCertificate
        (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (unitMoveLiftBase_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo index)
        (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  have secondCertificate : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal RFAP.GlobalWinding.coordinatePolynomial
        bridgeAnchor (overlap - bridgeAnchor))
      (RFAP.PathPolynomial.pathImag RFAP.GlobalWinding.coordinatePolynomial
        bridgeAnchor (overlap - bridgeAnchor))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      unitRobustSegmentCoordinatePowerCertificate
        (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
        sourceIndex
        (unitMoveBridgeAnchor_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (unitMoveOverlapPoint_inside_sourceRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  have thirdCertificate : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal RFAP.GlobalWinding.coordinatePolynomial
        overlap (targetAnchor - overlap))
      (RFAP.PathPolynomial.pathImag RFAP.GlobalWinding.coordinatePolynomial
        overlap (targetAnchor - overlap))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      unitRobustSegmentCoordinatePowerCertificate
        (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeAtLeastTwo
        targetIndex
        (unitMoveOverlapPoint_inside_targetRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index)
        (unitMoveTargetAnchor_inside_targetRobustBox sourceUnit targetUnit degree
          degreeAtLeastTwo small index) 0
  change RFAP.PolygonWinding.ChainPhaseFormula
    RFAP.GlobalWinding.coordinatePolynomial
    (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
    [bridgeAnchor, overlap, targetAnchor]
  exact RFAP.PolygonWinding.ChainPhaseFormula.consOfClearance firstCertificate
    (RFAP.PolygonWinding.ChainPhaseFormula.consOfClearance secondCertificate
      (RFAP.PolygonWinding.ChainPhaseFormula.consOfClearance thirdCertificate
        (RFAP.PolygonWinding.ChainPhaseFormula.nil
          RFAP.GlobalWinding.coordinatePolynomial targetAnchor)))

/-- One complete robust move: Rouché transport, finite target ownership, and
the canonical same-polynomial rebase to the target robust frame. -/
def unitSmallMovePath
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberPath
      (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree
        degreeAtLeastTwo)
      (robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
        degreeAtLeastTwo) :=
  .cons (unitMoveOverlap sourceUnit targetUnit degree degreeAtLeastTwo small)
    (.cons (unitRebaseOverlap sourceUnit targetUnit degree degreeAtLeastTwo
      small)
      (.cons (isolationRobustOverlap (nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree degreeAtLeastTwo)
        (.nil (robustChamberFrame (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeAtLeastTwo))))

theorem unitSmallMovePath_finalIndex_degree
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    Fin.cast
        (robustChamberFrame_degree (nonzero_of_normSq_eq_one targetUnit)
          targetUnit degree degreeAtLeastTwo)
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index) =
      unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index := by
  unfold unitSmallMovePath
  simp only [CCL.FiniteMonodromy.ChamberPath.finalIndex_cons,
    CCL.FiniteMonodromy.ChamberPath.finalIndex_nil,
    unitMoveOverlap, unitRebaseOverlap, isolationRobustOverlap,
    CCL.FiniteMonodromy.FiniteBijection.cast_forward]
  apply Fin.ext
  rfl

theorem unitMoveTargetAnchor_eq_finalOwnerAnchor
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    (unitRobustBox (nonzero_of_normSq_eq_one targetUnit) targetUnit degree
      degreeAtLeastTwo
      (unitMoveTargetDegreeIndexFromSource sourceUnit targetUnit degree
        degreeAtLeastTwo small index)).anchor =
      ((robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit
        degree degreeAtLeastTwo).owner
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index)).box.anchor := by
  rw [robustChamberFrame_owner_box]
  rw [unitSmallMovePath_finalIndex_degree]

theorem unitMoveLift_terminal_eq_finalOwnerAnchor
    {source target : Gaussian}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : (robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo).Index) :
    RFAP.PolygonWinding.terminal
        (unitMoveLiftBase sourceUnit targetUnit degree degreeAtLeastTwo index)
        (unitMoveLiftVertices sourceUnit targetUnit degree degreeAtLeastTwo small
          index) =
      ((robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit
        degree degreeAtLeastTwo).owner
        ((unitSmallMovePath sourceUnit targetUnit degree degreeAtLeastTwo small)
          |>.finalIndex index)).box.anchor := by
  simp only [unitMoveLiftVertices, RFAP.PolygonWinding.terminal]
  exact unitMoveTargetAnchor_eq_finalOwnerAnchor sourceUnit targetUnit degree
    degreeAtLeastTwo small index

/-! ## An explicit rational unit-circle circuit -/

def unitCircleDirection (parameter : Coordinate) : Gaussian :=
  ⟨1 - parameter ^ 2, 2 * parameter⟩

def unitCircleDenominator (parameter : Coordinate) : Gaussian :=
  ⟨parameter ^ 2 + 1, 0⟩

/-- Primary rational stereographic quarter-circle chart, from `1` at
parameter zero to `i` at parameter one. -/
def unitQuarterPoint (parameter : Coordinate) : Gaussian :=
  unitCircleDirection parameter *
    RFAP.ConstructiveGaussian.Gaussian.inv (unitCircleDenominator parameter)

private theorem unitCircleScalar_pos (parameter : Coordinate) :
    0 < parameter ^ 2 + 1 := by
  exact lt_of_le_of_lt
    (RFAP.ConstructiveFraction.sq_nonneg_direct parameter)
    (by
      have shifted := RFAP.ConstructiveFraction.add_lt_add_left_direct
        (show (0 : Coordinate) < 1 by decide) (parameter ^ 2)
      calc
        parameter ^ 2 = parameter ^ 2 + 0 := by ring1
        _ < parameter ^ 2 + 1 := shifted)

private theorem unitCircleDenominator_nonzero (parameter : Coordinate) :
    unitCircleDenominator parameter ≠ 0 := by
  intro zero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
  change parameter ^ 2 + 1 = 0 at realZero
  have positive := unitCircleScalar_pos parameter
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim

private theorem unitQuarterPoint_mul_denominator
    (parameter : Coordinate) :
    unitQuarterPoint parameter * unitCircleDenominator parameter =
      unitCircleDirection parameter := by
  unfold unitQuarterPoint
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    RFAP.ConstructiveGaussian.Gaussian.inv_mul
      (unitCircleDenominator parameter)
      (unitCircleDenominator_nonzero parameter),
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

@[simp] theorem unitQuarterPoint_re (parameter : Coordinate) :
    (unitQuarterPoint parameter).re =
      (1 - parameter ^ 2) * (parameter ^ 2 + 1)⁻¹ := by
  let scalar := parameter ^ 2 + 1
  have scalarNonzero : scalar ≠ 0 := (unitCircleScalar_pos parameter).ne'
  have realProduct := congrArg RFAP.ConstructiveGaussian.Gaussian.re
    (unitQuarterPoint_mul_denominator parameter)
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re] at realProduct
  change (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) -
      (unitQuarterPoint parameter).im * 0 = 1 - parameter ^ 2 at realProduct
  have realProduct' : (unitQuarterPoint parameter).re * scalar =
      1 - parameter ^ 2 := by
    dsimp only [scalar]
    calc
      (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) =
          (unitQuarterPoint parameter).re * (parameter ^ 2 + 1) -
            (unitQuarterPoint parameter).im * 0 := by ring1
      _ = 1 - parameter ^ 2 := realProduct
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne scalarNonzero
  calc
    (unitQuarterPoint parameter).re * scalar =
        1 - parameter ^ 2 := realProduct'
    _ = ((1 - parameter ^ 2) * scalar⁻¹) * scalar := by
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.inv_mul_cancel scalar scalarNonzero]
      ring1

@[simp] theorem unitQuarterPoint_im (parameter : Coordinate) :
    (unitQuarterPoint parameter).im =
      (2 * parameter) * (parameter ^ 2 + 1)⁻¹ := by
  let scalar := parameter ^ 2 + 1
  have scalarNonzero : scalar ≠ 0 := (unitCircleScalar_pos parameter).ne'
  have imaginaryProduct := congrArg RFAP.ConstructiveGaussian.Gaussian.im
    (unitQuarterPoint_mul_denominator parameter)
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_im] at imaginaryProduct
  change (unitQuarterPoint parameter).re * 0 +
      (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) =
        2 * parameter at imaginaryProduct
  have imaginaryProduct' : (unitQuarterPoint parameter).im * scalar =
      2 * parameter := by
    dsimp only [scalar]
    calc
      (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) =
          (unitQuarterPoint parameter).re * 0 +
            (unitQuarterPoint parameter).im * (parameter ^ 2 + 1) := by ring1
      _ = 2 * parameter := imaginaryProduct
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne scalarNonzero
  calc
    (unitQuarterPoint parameter).im * scalar =
        2 * parameter := imaginaryProduct'
    _ = ((2 * parameter) * scalar⁻¹) * scalar := by
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.inv_mul_cancel scalar scalarNonzero]
      ring1

/-- The fixed diagonal coordinate of the primary stereographic quarter is
at least one throughout its displayed parameter interval. -/
theorem unitQuarterPoint_re_add_im_ge_one
    {parameter : Coordinate} (nonnegative : 0 ≤ parameter)
    (atMostOne : parameter ≤ 1) :
    1 ≤ (unitQuarterPoint parameter).re +
      (unitQuarterPoint parameter).im := by
  let scalar := parameter ^ 2 + 1
  have scalarPositive : 0 < scalar := unitCircleScalar_pos parameter
  have oneMinusNonnegative : 0 ≤ 1 - parameter :=
    RFAP.ConstructiveFraction.sub_nonneg_direct atMostOne
  have extraNonnegative : 0 ≤ 2 * parameter * (1 - parameter) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) nonnegative)
      oneMinusNonnegative
  have numeratorBound : scalar ≤
      1 - parameter ^ 2 + 2 * parameter := by
    calc
      scalar = 0 + scalar := by ring1
      _ ≤ 2 * parameter * (1 - parameter) + scalar :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          extraNonnegative scalar
      _ = scalar + 2 * parameter * (1 - parameter) := by ring1
      _ = 1 - parameter ^ 2 + 2 * parameter := by
        dsimp only [scalar]
        ring1
  rw [unitQuarterPoint_re, unitQuarterPoint_im]
  have combined :
      (1 - parameter ^ 2) * scalar⁻¹ +
          (2 * parameter) * scalar⁻¹ =
        (1 - parameter ^ 2 + 2 * parameter) / scalar := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  rw [combined]
  apply (RFAP.ConstructiveFraction.le_div_iff_pos scalarPositive).2
  simpa only [RFAP.ConstructiveFraction.one_mul] using numeratorBound

private theorem unitCircleDirection_normSq (parameter : Coordinate) :
    normSq (unitCircleDirection parameter) =
      (parameter ^ 2 + 1) ^ 2 := by
  dsimp only [unitCircleDirection, normSq]
  ring1

private theorem unitCircleDenominator_normSq (parameter : Coordinate) :
    normSq (unitCircleDenominator parameter) =
      (parameter ^ 2 + 1) ^ 2 := by
  dsimp only [unitCircleDenominator, normSq]
  ring1

theorem unitQuarterPoint_unit (parameter : Coordinate) :
    normSq (unitQuarterPoint parameter) = 1 := by
  unfold unitQuarterPoint
  rw [normSq_mul,
    normSq_inv _ (unitCircleDenominator_nonzero parameter),
    unitCircleDirection_normSq, unitCircleDenominator_normSq]
  exact RFAP.ConstructiveFraction.mul_inv_cancel _
    (RFAP.ConstructiveFraction.pow_pos_direct
      (unitCircleScalar_pos parameter) 2).ne'

private theorem unitQuarterPoint_cross_difference
    (source target : Coordinate) :
    (unitQuarterPoint source - unitQuarterPoint target) *
        (unitCircleDenominator source * unitCircleDenominator target) =
      unitCircleDirection source * unitCircleDenominator target -
        unitCircleDirection target * unitCircleDenominator source := by
  unfold unitQuarterPoint
  rw [_root_.sub_mul]
  congr 1
  · calc
      (unitCircleDirection source *
            RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator source)) *
          (unitCircleDenominator source * unitCircleDenominator target) =
        unitCircleDirection source *
          (RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator source) *
            (unitCircleDenominator source * unitCircleDenominator target)) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
      _ = unitCircleDirection source *
          ((RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator source) *
            unitCircleDenominator source) * unitCircleDenominator target) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
      _ =
        unitCircleDirection source *
          (RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator source) *
            unitCircleDenominator source) * unitCircleDenominator target := by
          exact (RFAP.ConstructiveGaussian.Gaussian.mul_assoc
            (unitCircleDirection source)
            (RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator source) * unitCircleDenominator source)
            (unitCircleDenominator target)).symm
      _ = unitCircleDirection source * unitCircleDenominator target := by
        rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul
            (unitCircleDenominator source)
            (unitCircleDenominator_nonzero source),
          RFAP.ConstructiveGaussian.Gaussian.mul_one]
  · calc
      (unitCircleDirection target *
            RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator target)) *
          (unitCircleDenominator source * unitCircleDenominator target) =
        unitCircleDirection target *
          (RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator target) *
            (unitCircleDenominator target * unitCircleDenominator source)) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm
              (unitCircleDenominator source) (unitCircleDenominator target),
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
      _ = unitCircleDirection target *
          ((RFAP.ConstructiveGaussian.Gaussian.inv
              (unitCircleDenominator target) *
            unitCircleDenominator target) * unitCircleDenominator source) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
      _ = unitCircleDirection target * unitCircleDenominator source := by
        rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul
            (unitCircleDenominator target)
            (unitCircleDenominator_nonzero target),
          RFAP.ConstructiveGaussian.Gaussian.one_mul]

private theorem unitCircleCrossDifference_normSq
    (source target : Coordinate) :
    normSq (unitCircleDirection source * unitCircleDenominator target -
      unitCircleDirection target * unitCircleDenominator source) =
      4 * (source - target) ^ 2 *
        ((source ^ 2 + 1) * (target ^ 2 + 1)) := by
  dsimp only [unitCircleDirection, unitCircleDenominator, normSq, mul_re,
    mul_im, sub_re, sub_im]
  ring1

/-- Coarse rational Lipschitz estimate for the stereographic chart.  It is
obtained by an exact cross-product identity and cancellation of the positive
displayed denominator product. -/
theorem unitQuarterPoint_distance_le (source target : Coordinate) :
    normSq (unitQuarterPoint source - unitQuarterPoint target) ≤
      4 * (source - target) ^ 2 := by
  let sourceScalar := source ^ 2 + 1
  let targetScalar := target ^ 2 + 1
  let product := sourceScalar * targetScalar
  have productPositive : 0 < product :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (unitCircleScalar_pos source) (unitCircleScalar_pos target)
  have cross := congrArg normSq
    (unitQuarterPoint_cross_difference source target)
  have productEquation :
      normSq (unitQuarterPoint source - unitQuarterPoint target) * product ^ 2 =
        (4 * (source - target) ^ 2) * product := by
    rw [normSq_mul, normSq_mul,
      unitCircleDenominator_normSq source,
      unitCircleDenominator_normSq target,
      unitCircleCrossDifference_normSq source target] at cross
    simpa only [sourceScalar, targetScalar, product] using (by
      calc
        normSq (unitQuarterPoint source - unitQuarterPoint target) *
            product ^ 2 =
          normSq (unitQuarterPoint source - unitQuarterPoint target) *
            (sourceScalar ^ 2 * targetScalar ^ 2) := by ring1
        _ = 4 * (source - target) ^ 2 * product := cross)
  have canceled :
      normSq (unitQuarterPoint source - unitQuarterPoint target) * product =
        4 * (source - target) ^ 2 := by
    apply RFAP.CanonicalFraction.mul_left_cancel_of_nonzero
      productPositive.ne'
    calc
      product *
          (normSq (unitQuarterPoint source - unitQuarterPoint target) *
            product) =
        normSq (unitQuarterPoint source - unitQuarterPoint target) *
          product ^ 2 := by ring1
      _ = (4 * (source - target) ^ 2) * product := productEquation
      _ = product * (4 * (source - target) ^ 2) := by ring1
  have oneLeProduct : (1 : Coordinate) ≤ product := by
    have sourceOne : (1 : Coordinate) ≤ sourceScalar := by
      dsimp only [sourceScalar]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct source)
    have targetOne : (1 : Coordinate) ≤ targetScalar := by
      dsimp only [targetScalar]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct target)
    exact (show (1 : Coordinate) = 1 * 1 by ring1) ▸
      RFAP.ConstructiveFraction.mul_le_mul_direct sourceOne targetOne
        (by decide) (unitCircleScalar_pos source).le
  calc
    normSq (unitQuarterPoint source - unitQuarterPoint target) =
        normSq (unitQuarterPoint source - unitQuarterPoint target) * 1 := by
      ring1
    _ ≤ normSq (unitQuarterPoint source - unitQuarterPoint target) * product :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct oneLeProduct
        (normSq_nonneg _)
    _ = 4 * (source - target) ^ 2 := canceled

/-- The common move budget also reserves a fixed margin for the later
power-lift homotopy. -/
def unitCircuitMoveBudget (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Coordinate :=
  min (uniformRobustClearance degree degreeAtLeastTwo) (1 / 128)

theorem unitCircuitMoveBudget_pos (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitCircuitMoveBudget degree degreeAtLeastTwo := by
  exact lt_min (uniformRobustClearance_pos degree degreeAtLeastTwo)
    (RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide))
      (RFAP.ConstructiveFraction.natCast_pos_direct (n := 128) (by decide)))

theorem unitCircuitMoveBudget_le_clearance (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitMoveBudget degree degreeAtLeastTwo ≤
      uniformRobustClearance degree degreeAtLeastTwo :=
  min_le_left _ _

theorem unitCircuitMoveBudget_le_liftMargin (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitMoveBudget degree degreeAtLeastTwo ≤ (1 / 128 : Coordinate) :=
  min_le_right _ _

/-- The number of rational subedges used on each quarter of the unit circuit.
It is computed directly from the common move budget. -/
def unitCircuitStepCount (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Nat :=
  RFAP.ConstructiveFraction.ceilNat
      (4 / unitCircuitMoveBudget degree degreeAtLeastTwo) + 1

theorem unitCircuitStepCount_pos (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitCircuitStepCount degree degreeAtLeastTwo := by
  unfold unitCircuitStepCount
  exact Nat.zero_lt_succ _

theorem unitCircuitStepCount_one_le (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    1 ≤ unitCircuitStepCount degree degreeAtLeastTwo := by
  unfold unitCircuitStepCount
  exact Nat.succ_le_succ (Nat.zero_le _)

theorem four_lt_unitCircuitStepCount_mul_budget (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (4 : Coordinate) <
      (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) *
        unitCircuitMoveBudget degree degreeAtLeastTwo := by
  let budget := unitCircuitMoveBudget degree degreeAtLeastTwo
  let ceiling := RFAP.ConstructiveFraction.ceilNat (4 / budget)
  have budgetPositive : 0 < budget :=
    unitCircuitMoveBudget_pos degree degreeAtLeastTwo
  have ratioNonnegative : (0 : Coordinate) ≤ 4 / budget :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide)
      budgetPositive).le
  have ratioLeCeiling :
      4 / budget ≤ (ceiling : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg ratioNonnegative
  have ceilingLtStepsNat :
      ceiling < unitCircuitStepCount degree degreeAtLeastTwo := by
    dsimp only [ceiling, budget]
    unfold unitCircuitStepCount
    exact Nat.lt_succ_self _
  have ceilingLtSteps :
      (ceiling : Coordinate) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct ceilingLtStepsNat
  have ratioLtSteps :
      4 / budget <
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) :=
    ratioLeCeiling.trans_lt ceilingLtSteps
  exact (RFAP.ConstructiveFraction.div_lt_iff_pos budgetPositive).1
    ratioLtSteps

theorem four_div_unitCircuitStepCount_lt_budget (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (4 : Coordinate) /
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) <
      unitCircuitMoveBudget degree degreeAtLeastTwo := by
  have stepsPositive :
      (0 : Coordinate) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos stepsPositive).2
  calc
    (4 : Coordinate) <
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) *
          unitCircuitMoveBudget degree degreeAtLeastTwo :=
      four_lt_unitCircuitStepCount_mul_budget degree degreeAtLeastTwo
    _ = unitCircuitMoveBudget degree degreeAtLeastTwo *
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) := by ring1

/-- The rational subdivision parameter `index/N` on one stereographic
quarter. -/
def unitCircuitParameter (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : Coordinate :=
  (index : Coordinate) /
    (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate)

theorem unitCircuitParameter_nonnegative (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    0 ≤ unitCircuitParameter degree degreeAtLeastTwo index := by
  unfold unitCircuitParameter
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_le_direct
      (m := 0) (n := index) (Nat.zero_le index))
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)).le

theorem unitCircuitParameter_le_one (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index ≤ unitCircuitStepCount degree degreeAtLeastTwo) :
    unitCircuitParameter degree degreeAtLeastTwo index ≤ 1 := by
  let steps := unitCircuitStepCount degree degreeAtLeastTwo
  have stepsPositive : (0 : Coordinate) < (steps : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  unfold unitCircuitParameter
  apply (RFAP.ConstructiveFraction.div_le_iff_pos stepsPositive).2
  have castBound : (index : Coordinate) ≤ (steps : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct indexBound
  simpa only [RFAP.ConstructiveFraction.one_mul] using castBound

private theorem unitCircuitParameter_step_bound
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    4 * (unitCircuitParameter degree degreeAtLeastTwo index -
        unitCircuitParameter degree degreeAtLeastTwo (index + 1)) ^ 2 <
      unitCircuitMoveBudget degree degreeAtLeastTwo := by
  let steps : Coordinate :=
    (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate)
  have stepsPositive : 0 < steps := by
    exact RFAP.ConstructiveFraction.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)
  have oneLeStepsCast : (1 : Coordinate) ≤
      (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct
      (m := 1) (n := unitCircuitStepCount degree degreeAtLeastTwo)
      (unitCircuitStepCount_one_le degree degreeAtLeastTwo)
  have oneLeSteps : (1 : Coordinate) ≤ steps := by
    exact oneLeStepsCast
  have inversePositive : 0 < steps⁻¹ :=
    RFAP.ConstructiveFraction.inv_pos_direct stepsPositive
  have inverseLeOne : steps⁻¹ ≤ (1 : Coordinate)⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct (by decide) oneLeSteps
  have inverseOne : (1 : Coordinate)⁻¹ = 1 := by decide
  rw [inverseOne] at inverseLeOne
  have inverseSquareLeInverse : steps⁻¹ ^ 2 ≤ steps⁻¹ := by
    rw [pow_two]
    have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
      inverseLeOne (le_refl steps⁻¹) inversePositive.le (by decide)
    simpa only [RFAP.ConstructiveFraction.one_mul] using multiplied
  have scaled : 4 * steps⁻¹ ^ 2 ≤ 4 * steps⁻¹ :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      inverseSquareLeInverse (by decide)
  have parameterDifference :
      unitCircuitParameter degree degreeAtLeastTwo index -
          unitCircuitParameter degree degreeAtLeastTwo (index + 1) =
        -steps⁻¹ := by
    dsimp only [unitCircuitParameter, steps]
    rw [Nat.cast_add, Nat.cast_one]
    change (index : Coordinate) * steps⁻¹ -
        ((index : Coordinate) + 1) * steps⁻¹ = -steps⁻¹
    ring1
  rw [parameterDifference]
  have negativeSquare : (-steps⁻¹) ^ 2 = steps⁻¹ ^ 2 := by ring1
  rw [negativeSquare]
  exact scaled.trans_lt (by
    change (4 : Coordinate) / steps <
      unitCircuitMoveBudget degree degreeAtLeastTwo
    exact four_div_unitCircuitStepCount_lt_budget degree degreeAtLeastTwo)

theorem unitQuarterSubdivision_budget
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (unitQuarterPoint (unitCircuitParameter degree degreeAtLeastTwo index) -
          unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      unitCircuitMoveBudget degree degreeAtLeastTwo :=
  (unitQuarterPoint_distance_le _ _).trans_lt
    (unitCircuitParameter_step_bound degree degreeAtLeastTwo index)

theorem unitQuarterSubdivision_small
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (unitQuarterPoint (unitCircuitParameter degree degreeAtLeastTwo index) -
          unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      uniformRobustClearance degree degreeAtLeastTwo :=
  (unitQuarterSubdivision_budget degree degreeAtLeastTwo index).trans_le
    (unitCircuitMoveBudget_le_clearance degree degreeAtLeastTwo)

theorem unitQuarterSubdivision_liftMargin
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq
        (unitQuarterPoint (unitCircuitParameter degree degreeAtLeastTwo index) -
          unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) <
      (1 / 128 : Coordinate) :=
  (unitQuarterSubdivision_budget degree degreeAtLeastTwo index).trans_le
    (unitCircuitMoveBudget_le_liftMargin degree degreeAtLeastTwo)

/-- Four successive rotations of the primary rational quarter chart. -/
inductive UnitCircuitQuarter
  | first
  | second
  | third
  | fourth
deriving DecidableEq, Repr

def unitCircuitMultiplier : UnitCircuitQuarter → Gaussian
  | .first => ⟨1, 0⟩
  | .second => ⟨0, 1⟩
  | .third => ⟨-1, 0⟩
  | .fourth => ⟨0, -1⟩

/-- Quarter-dependent Gaussian unit which rotates every point of that
quarter into the same explicit open right half-plane. -/
def unitCircuitRotation : UnitCircuitQuarter → Gaussian
  | .first => ⟨1, -1⟩
  | .second => ⟨-1, -1⟩
  | .third => ⟨-1, 1⟩
  | .fourth => ⟨1, 1⟩

theorem unitCircuitRotation_mul_multiplier
    (quarter : UnitCircuitQuarter) :
    unitCircuitRotation quarter * unitCircuitMultiplier quarter =
      ⟨1, -1⟩ := by
  cases quarter <;> decide

theorem unitCircuitRotation_normSq (quarter : UnitCircuitQuarter) :
    normSq (unitCircuitRotation quarter) = 2 := by
  cases quarter <;> decide

theorem unitCircuitRotation_ne_zero (quarter : UnitCircuitQuarter) :
    unitCircuitRotation quarter ≠ 0 := by
  intro zero
  have normZero := congrArg normSq zero
  rw [unitCircuitRotation_normSq, normSq_zero] at normZero
  exact (by decide : (2 : Coordinate) ≠ 0) normZero

theorem unitCircuitMultiplier_unit (quarter : UnitCircuitQuarter) :
    normSq (unitCircuitMultiplier quarter) = 1 := by
  cases quarter <;> decide

/-- The `index`th rational parameter vertex on a selected quarter. -/
def unitCircuitPoint (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : Gaussian :=
  unitCircuitMultiplier quarter *
    unitQuarterPoint (unitCircuitParameter degree degreeAtLeastTwo index)

theorem unitCircuitRotation_mul_point
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    unitCircuitRotation quarter *
        unitCircuitPoint quarter degree degreeAtLeastTwo index =
      ⟨1, -1⟩ *
        unitQuarterPoint
          (unitCircuitParameter degree degreeAtLeastTwo index) := by
  unfold unitCircuitPoint
  rw [← RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    unitCircuitRotation_mul_multiplier]

private theorem diagonalRotation_real (point : Gaussian) :
    (⟨1, -1⟩ * point : Gaussian).re = point.re + point.im := by
  change (1 : Coordinate) * point.re - (-1) * point.im =
    point.re + point.im
  ring1

theorem unitCircuitRotatedPoint_real_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index ≤ unitCircuitStepCount degree degreeAtLeastTwo) :
    1 ≤ (unitCircuitRotation quarter *
      unitCircuitPoint quarter degree degreeAtLeastTwo index).re := by
  rw [unitCircuitRotation_mul_point]
  rw [diagonalRotation_real]
  exact unitQuarterPoint_re_add_im_ge_one
    (unitCircuitParameter_nonnegative degree degreeAtLeastTwo index)
    (unitCircuitParameter_le_one degree degreeAtLeastTwo indexBound)

def unitCircuitRotatedCoordinate
    (quarter : UnitCircuitQuarter) : GaussianPolynomial :=
  RFAP.GlobalWinding.coordinatePolynomial *
    RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter)

@[simp] theorem unitCircuitRotatedCoordinate_eval
    (quarter : UnitCircuitQuarter) (point : Gaussian) :
    (unitCircuitRotatedCoordinate quarter).eval point =
      unitCircuitRotation quarter * point := by
  rw [unitCircuitRotatedCoordinate,
    RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
    RFAP.GlobalWinding.coordinatePolynomial_eval,
    RFAP.GlobalWinding.gaussianConstant_eval,
    RFAP.ConstructiveGaussian.Gaussian.mul_comm]

private theorem rotated_line_real_eq_convex
    (rotation source target : Gaussian) (time : Coordinate) :
    (rotation * RFAP.PathPolynomial.line source (target - source) time).re =
      (1 - time) * (rotation * source).re +
        time * (rotation * target).re := by
  simp only [RFAP.PathPolynomial.line,
    RFAP.PathPolynomial.ofCoordinate_re,
    RFAP.PathPolynomial.ofCoordinate_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im]
  ring1

theorem unitCircuitRotatedLine_real_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    1 ≤ ((unitCircuitRotatedCoordinate quarter).eval
      (RFAP.PathPolynomial.line
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index) time)).re := by
  let source := unitCircuitPoint quarter degree degreeAtLeastTwo index
  let target := unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)
  have sourceBound : 1 ≤ (unitCircuitRotation quarter * source).re :=
    unitCircuitRotatedPoint_real_ge_one quarter degree degreeAtLeastTwo
      (Nat.le_of_lt indexBound)
  have targetBound : 1 ≤ (unitCircuitRotation quarter * target).re :=
    unitCircuitRotatedPoint_real_ge_one quarter degree degreeAtLeastTwo
      (by omega)
  have oneMinusNonnegative : 0 ≤ 1 - time :=
    RFAP.ConstructiveFraction.sub_nonneg_direct timeInside.2
  rw [unitCircuitRotatedCoordinate_eval,
    rotated_line_real_eq_convex]
  change 1 ≤ (1 - time) * (unitCircuitRotation quarter * source).re +
    time * (unitCircuitRotation quarter * target).re
  calc
    1 = (1 - time) * 1 + time * 1 := by ring1
    _ ≤ (1 - time) * (unitCircuitRotation quarter * source).re +
        time * (unitCircuitRotation quarter * target).re :=
      add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sourceBound oneMinusNonnegative)
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          targetBound timeInside.1)

theorem unitCircuitRotatedLine_normSq_ge_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    1 ≤ normSq ((unitCircuitRotatedCoordinate quarter).eval
      (RFAP.PathPolynomial.line
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index) time)) := by
  let value := (unitCircuitRotatedCoordinate quarter).eval
    (RFAP.PathPolynomial.line
      (unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        unitCircuitPoint quarter degree degreeAtLeastTwo index) time)
  have realLower : (1 : Coordinate) ≤ value.re :=
    unitCircuitRotatedLine_real_ge_one quarter degree degreeAtLeastTwo
      indexBound timeInside
  have realSquare : (1 : Coordinate) ≤ value.re ^ 2 := by
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1) realLower 2
    simpa only [one_pow] using powered
  exact realSquare.trans (le_add_of_nonneg_right
    (RFAP.ConstructiveFraction.sq_nonneg_direct value.im))

/-- Quantitative nonvanishing of one rotated stereographic chord. -/
def unitCircuitRotatedEdgeCertificate
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal (unitCircuitRotatedCoordinate quarter)
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (RFAP.PathPolynomial.pathImag (unitCircuitRotatedCoordinate quarter)
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } where
  bound := 1
  positive := by decide
  lower := by
    intro time timeInside
    simpa only [RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag, normSq] using
      unitCircuitRotatedLine_normSq_ge_one quarter degree degreeAtLeastTwo
        indexBound timeInside

/-- The finite right-half-plane formula for one rotated rational quarter
edge. -/
theorem unitCircuitRotatedEdgeHalfPlaneFormula
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo) :
    RFAP.HalfPlane.Formula
      (RFAP.PathPolynomial.pathReal (unitCircuitRotatedCoordinate quarter)
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (RFAP.PathPolynomial.pathImag (unitCircuitRotatedCoordinate quarter)
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index)) 0 1 := by
  let source := unitCircuitPoint quarter degree degreeAtLeastTwo index
  let direction :=
    unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) - source
  let A := RFAP.PathPolynomial.pathReal
    (unitCircuitRotatedCoordinate quarter) source direction
  let B := RFAP.PathPolynomial.pathImag
    (unitCircuitRotatedCoordinate quarter) source direction
  let interval : RFAP.PathClearance.Interval :=
    { lower := 0, upper := 1, valid := by decide }
  let certificate : RFAP.PathClearance.Certificate A B interval := by
    simpa only [A, B, interval, source, direction] using
      unitCircuitRotatedEdgeCertificate quarter degree degreeAtLeastTwo
        indexBound
  have positive : ∀ time : Coordinate, interval.Contains time →
      0 < A.eval time := by
    intro time timeInside
    have inside : (0 : Coordinate) ≤ time ∧ time ≤ 1 := by
      simpa only [interval, RFAP.PathClearance.Interval.Contains] using
        timeInside
    have lower := unitCircuitRotatedLine_real_ge_one quarter degree
      degreeAtLeastTwo indexBound inside
    have strict := (show (0 : Coordinate) < 1 by decide).trans_le lower
    simpa only [A, source, direction, RFAP.PathPolynomial.eval_pathReal] using
      strict
  have formula := RFAP.HalfPlane.formula_of_positive_real certificate
    (show interval.lower < interval.upper by
      simpa only [interval] using (show (0 : Coordinate) < 1 by decide))
    positive
  simpa only [A, B, source, direction, interval] using formula

theorem unitCircuitCoordinateLine_normSq_ge_half
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo)
    {time : Coordinate} (timeInside : (0 : Coordinate) ≤ time ∧ time ≤ 1) :
    (1 / 2 : Coordinate) ≤ normSq (RFAP.PathPolynomial.line
      (unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        unitCircuitPoint quarter degree degreeAtLeastTwo index) time) := by
  let point := RFAP.PathPolynomial.line
    (unitCircuitPoint quarter degree degreeAtLeastTwo index)
    (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
      unitCircuitPoint quarter degree degreeAtLeastTwo index) time
  have rotatedLower := unitCircuitRotatedLine_normSq_ge_one quarter degree
    degreeAtLeastTwo indexBound timeInside
  rw [unitCircuitRotatedCoordinate_eval, normSq_mul,
    unitCircuitRotation_normSq] at rotatedLower
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (show (0 : Coordinate) < 2 by decide)).2
  calc
    (1 : Coordinate) ≤ 2 * normSq point := rotatedLower
    _ = normSq point * 2 := by ring1

/-- The same chord carries a coordinate clearance; it follows from the
rotated real-coordinate bound and the exact norm two of the rotation. -/
def unitCircuitCoordinateEdgeCertificate
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal
        RFAP.GlobalWinding.coordinatePolynomial
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index))
      (RFAP.PathPolynomial.pathImag
        RFAP.GlobalWinding.coordinatePolynomial
        (unitCircuitPoint quarter degree degreeAtLeastTwo index)
        (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
          unitCircuitPoint quarter degree degreeAtLeastTwo index))
      { lower := 0, upper := 1, valid := by decide } where
  bound := 1 / 2
  positive := by decide
  lower := by
    intro time timeInside
    simpa only [RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag,
      RFAP.GlobalWinding.coordinatePolynomial_eval, normSq] using
      unitCircuitCoordinateLine_normSq_ge_half quarter degree degreeAtLeastTwo
        indexBound timeInside

/-- A quarter rotation is a fixed nonzero constant path with exact norm-two
clearance. -/
def unitCircuitRotationConstantCertificate
    (quarter : UnitCircuitQuarter) (origin direction : Gaussian) :
    RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal
        (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
        origin direction)
      (RFAP.PathPolynomial.pathImag
        (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
        origin direction)
      { lower := 0, upper := 1, valid := by decide } where
  bound := 2
  positive := by decide
  lower := by
    intro time _timeInside
    have lower : (2 : Coordinate) ≤ normSq (unitCircuitRotation quarter) :=
      (unitCircuitRotation_normSq quarter).ge
    simpa only [RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag,
      RFAP.GlobalWinding.gaussianConstant_eval, normSq] using lower

/-- Multiplication by the quarter rotation relates the coordinate edge to
its right-half-plane edge by the finite product formula. -/
theorem unitCircuitEdgeProductFormula
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) {index : Nat}
    (indexBound : index < unitCircuitStepCount degree degreeAtLeastTwo) :
    RFAP.WindingProduct.LineProductFormula
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
      (unitCircuitPoint quarter degree degreeAtLeastTwo index)
      (unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) -
        unitCircuitPoint quarter degree degreeAtLeastTwo index) 0 1 := by
  let source := unitCircuitPoint quarter degree degreeAtLeastTwo index
  let target := unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)
  have sourceUnit : normSq source = 1 := by
    dsimp only [source, unitCircuitPoint]
    rw [normSq_mul, unitCircuitMultiplier_unit, unitQuarterPoint_unit,
      RFAP.ConstructiveFraction.one_mul]
  have targetUnit : normSq target = 1 := by
    dsimp only [target, unitCircuitPoint]
    rw [normSq_mul, unitCircuitMultiplier_unit, unitQuarterPoint_unit,
      RFAP.ConstructiveFraction.one_mul]
  have sourceNonzero : source ≠ 0 := nonzero_of_normSq_eq_one sourceUnit
  have targetNonzero : target ≠ 0 := nonzero_of_normSq_eq_one targetUnit
  have rotationNonzero : unitCircuitRotation quarter ≠ 0 := by
    intro zero
    have normZero := congrArg normSq zero
    rw [unitCircuitRotation_normSq, normSq_zero] at normZero
    exact (by decide : (2 : Coordinate) ≠ 0) normZero
  apply RFAP.WindingProduct.lineProductFormula_of_clearances
    RFAP.GlobalWinding.coordinatePolynomial
    (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
    source (target - source) (by decide)
    (unitCircuitCoordinateEdgeCertificate quarter degree degreeAtLeastTwo
      indexBound)
    (unitCircuitRotationConstantCertificate quarter source (target - source))
  · simpa only [RFAP.GlobalWinding.coordinatePolynomial_eval,
      RFAP.PolygonWinding.line_segment_zero] using sourceNonzero
  · simpa only [RFAP.GlobalWinding.gaussianConstant_eval] using rotationNonzero
  · simpa only [RFAP.GlobalWinding.coordinatePolynomial_eval,
      RFAP.PolygonWinding.line_segment_one] using targetNonzero
  · simpa only [RFAP.GlobalWinding.gaussianConstant_eval] using rotationNonzero

theorem unitCircuitPoint_unit (quarter : UnitCircuitQuarter)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index) = 1 := by
  rw [unitCircuitPoint, normSq_mul, unitCircuitMultiplier_unit,
    unitQuarterPoint_unit, RFAP.ConstructiveFraction.one_mul]

private theorem unitCircuitPoint_difference
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1) =
      unitCircuitMultiplier quarter *
        (unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo index) -
          unitQuarterPoint
            (unitCircuitParameter degree degreeAtLeastTwo (index + 1))) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [unitCircuitPoint, mul_re, mul_im, sub_re, sub_im] <;> ring1

theorem unitCircuitSubdivision_small
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)) <
      uniformRobustClearance degree degreeAtLeastTwo := by
  rw [unitCircuitPoint_difference, normSq_mul,
    unitCircuitMultiplier_unit, RFAP.ConstructiveFraction.one_mul]
  exact unitQuarterSubdivision_small degree degreeAtLeastTwo index

theorem unitCircuitSubdivision_liftMargin
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) :
    normSq (unitCircuitPoint quarter degree degreeAtLeastTwo index -
        unitCircuitPoint quarter degree degreeAtLeastTwo (index + 1)) <
      (1 / 128 : Coordinate) := by
  rw [unitCircuitPoint_difference, normSq_mul,
    unitCircuitMultiplier_unit, RFAP.ConstructiveFraction.one_mul]
  exact unitQuarterSubdivision_liftMargin degree degreeAtLeastTwo index

theorem unitCircuitParameter_zero (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitParameter degree degreeAtLeastTwo 0 = 0 := by
  unfold unitCircuitParameter
  exact RFAP.ConstructiveFraction.zero_div_direct _

theorem unitCircuitParameter_last (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitParameter degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo) = 1 := by
  unfold unitCircuitParameter
  change
    (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate) *
        (unitCircuitStepCount degree degreeAtLeastTwo : Coordinate)⁻¹ = 1
  exact RFAP.ConstructiveFraction.mul_inv_cancel _
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (unitCircuitStepCount_pos degree degreeAtLeastTwo)).ne'

theorem unitQuarterPoint_zero : unitQuarterPoint 0 = 1 := by
  decide

theorem unitQuarterPoint_one : unitQuarterPoint 1 = ⟨0, 1⟩ := by
  decide

/-- The four subdivided quarters join without a geometric gap and the last
quarter returns to the first vertex. -/
theorem unitCircuitQuarters_join (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitCircuitPoint .first degree degreeAtLeastTwo
          (unitCircuitStepCount degree degreeAtLeastTwo) =
        unitCircuitPoint .second degree degreeAtLeastTwo 0 ∧
      unitCircuitPoint .second degree degreeAtLeastTwo
          (unitCircuitStepCount degree degreeAtLeastTwo) =
        unitCircuitPoint .third degree degreeAtLeastTwo 0 ∧
      unitCircuitPoint .third degree degreeAtLeastTwo
          (unitCircuitStepCount degree degreeAtLeastTwo) =
        unitCircuitPoint .fourth degree degreeAtLeastTwo 0 ∧
      unitCircuitPoint .fourth degree degreeAtLeastTwo
          (unitCircuitStepCount degree degreeAtLeastTwo) =
        unitCircuitPoint .first degree degreeAtLeastTwo 0 := by
  simp only [unitCircuitPoint, unitCircuitParameter_last,
    unitCircuitParameter_zero, unitQuarterPoint_one, unitQuarterPoint_zero,
    unitCircuitMultiplier]
  decide

/-! ### The certified finite chamber loop -/

/-- A displayed rational parameter together with its exact unit-norm
certificate. -/
structure UnitVertex where
  value : Gaussian
  unit : normSq value = 1

namespace UnitVertex

def frame (vertex : UnitVertex) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.ChamberFrame :=
  robustChamberFrame (nonzero_of_normSq_eq_one vertex.unit) vertex.unit degree
    degreeAtLeastTwo

def ownerAnchor (vertex : UnitVertex) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : (vertex.frame degree degreeAtLeastTwo).Index) : Gaussian :=
  ((vertex.frame degree degreeAtLeastTwo).owner index).box.anchor

theorem eq_of_value_eq {left right : UnitVertex}
    (same : left.value = right.value) : left = right := by
  cases left with
  | mk leftValue leftUnit =>
      cases right with
      | mk rightValue rightUnit =>
          dsimp only at same
          subst rightValue
          rfl

end UnitVertex

def unitCircuitVertex (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (index : Nat) : UnitVertex where
  value := unitCircuitPoint quarter degree degreeAtLeastTwo index
  unit := unitCircuitPoint_unit quarter degree degreeAtLeastTwo index

/-- A finite chain of uniformly small unit-parameter moves.  Its dependent
endpoints guarantee that the chamber paths assembled from it really join. -/
inductive UnitChain (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : UnitVertex → UnitVertex → Type 1
  | nil (vertex : UnitVertex) : UnitChain degree degreeAtLeastTwo vertex vertex
  | cons {source middle target : UnitVertex}
      (small : UnitMoveSmall source.unit middle.unit degree degreeAtLeastTwo)
      (remaining : UnitChain degree degreeAtLeastTwo middle target) :
      UnitChain degree degreeAtLeastTwo source target

namespace UnitChain

def append {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : UnitVertex}
    (first : UnitChain degree degreeAtLeastTwo start middle)
    (second : UnitChain degree degreeAtLeastTwo middle finish) :
    UnitChain degree degreeAtLeastTwo start finish :=
  match first with
  | .nil _ => second
  | .cons small remaining => .cons small (remaining.append second)

def castStart {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right finish : UnitVertex} (same : left = right)
    (chain : UnitChain degree degreeAtLeastTwo right finish) :
    UnitChain degree degreeAtLeastTwo left finish := by
  subst right
  exact chain

def castFinish {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start left right : UnitVertex} (same : left = right)
    (chain : UnitChain degree degreeAtLeastTwo start left) :
    UnitChain degree degreeAtLeastTwo start right := by
  subst right
  exact chain

/-- Join two differently packaged unit vertices whose displayed Gaussian
values are equal.  The inserted move has exact squared distance zero. -/
def equalValue {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right : UnitVertex} (same : left.value = right.value) :
    UnitChain degree degreeAtLeastTwo left right :=
  .cons
    { distance := by
        rw [same, RFAP.ConstructiveGaussian.Gaussian.sub_self,
          normSq_zero]
        exact uniformRobustClearance_pos degree degreeAtLeastTwo
      liftMargin := by
        rw [same, RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
        exact RFAP.ConstructiveFraction.div_nonneg_direct
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 1) (by decide)).le
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 128) (by decide)).le }
    (.nil right)

/-- Forget the unit-vertex packaging and execute every certified edge as the
three finite chamber overlaps supplied by `unitSmallMovePath`. -/
def toPath {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : UnitVertex} →
      UnitChain degree degreeAtLeastTwo start finish →
      CCL.FiniteMonodromy.ChamberPath
        (start.frame degree degreeAtLeastTwo)
        (finish.frame degree degreeAtLeastTwo)
  | _, _, .nil vertex => .nil (vertex.frame degree degreeAtLeastTwo)
  | _, _, .cons small remaining =>
      (unitSmallMovePath _ _ degree degreeAtLeastTwo small).append
        remaining.toPath

theorem toPath_append
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : UnitVertex}
    (first : UnitChain degree degreeAtLeastTwo start middle)
    (second : UnitChain degree degreeAtLeastTwo middle finish) :
    (first.append second).toPath = first.toPath.append second.toPath := by
  induction first with
  | nil => rfl
  | cons small remaining inductionHypothesis =>
      simp only [append, toPath, inductionHypothesis]
      exact (CCL.FiniteMonodromy.ChamberPath.append_assoc
        (unitSmallMovePath _ _ degree degreeAtLeastTwo small)
        remaining.toPath second.toPath).symm

def repeatClosed
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex) : Nat →
      UnitChain degree degreeAtLeastTwo vertex vertex
  | 0 => .nil vertex
  | circuits + 1 => (repeatClosed chain circuits).append chain

theorem repeatClosed_finalIndex
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index) :
    ∀ circuits : Nat,
      (chain.repeatClosed circuits).toPath.finalIndex index =
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
          chain.toPath.monodromy circuits index
  | 0 => rfl
  | circuits + 1 => by
      rw [repeatClosed, toPath_append,
        CCL.FiniteMonodromy.ChamberPath.finalIndex_append]
      rw [repeatClosed_finalIndex chain index circuits]
      rfl

/-- Parameter vertices reached after each finite move, including the final
vertex but excluding the initial one. -/
def vertices {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : UnitVertex} →
      UnitChain degree degreeAtLeastTwo start finish → List Gaussian
  | _, _, .nil _ => []
  | _, _, .cons (middle := middle) _ remaining =>
      middle.value :: remaining.vertices

theorem vertices_terminal
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish),
      RFAP.PolygonWinding.terminal start.value chain.vertices = finish.value
  | _, _, .nil _ => rfl
  | _, _, .cons _ remaining => vertices_terminal remaining

theorem vertices_append
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : UnitVertex}
    (first : UnitChain degree degreeAtLeastTwo start middle)
    (second : UnitChain degree degreeAtLeastTwo middle finish) :
    (first.append second).vertices = first.vertices ++ second.vertices := by
  induction first with
  | nil => rfl
  | cons small remaining inductionHypothesis =>
      simp only [append, vertices, List.cons_append, inductionHypothesis]

def parameterRaw
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start finish : UnitVertex} (p : GaussianPolynomial)
    (chain : UnitChain degree degreeAtLeastTwo start finish) : Int :=
  RFAP.PolygonWinding.chainRaw p start.value chain.vertices

@[simp] theorem parameterRaw_nil
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (p : GaussianPolynomial) (vertex : UnitVertex) :
    parameterRaw (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo)
      p (UnitChain.nil vertex) = 0 := rfl

theorem parameterRaw_append
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : UnitVertex} (p : GaussianPolynomial)
    (first : UnitChain degree degreeAtLeastTwo start middle)
    (second : UnitChain degree degreeAtLeastTwo middle finish) :
    parameterRaw p (first.append second) =
      parameterRaw p first + parameterRaw p second := by
  unfold parameterRaw
  rw [vertices_append, RFAP.PolygonWinding.chainRaw_append,
    first.vertices_terminal]

theorem parameterRaw_castFinish
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start left right : UnitVertex} (p : GaussianPolynomial)
    (same : left = right)
    (chain : UnitChain degree degreeAtLeastTwo start left) :
    parameterRaw p (UnitChain.castFinish same chain) = parameterRaw p chain := by
  subst right
  rfl

theorem parameterRaw_equalValue
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right : UnitVertex} (same : left.value = right.value) :
    parameterRaw RFAP.GlobalWinding.coordinatePolynomial
      (UnitChain.equalValue
        (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo) same) = 0 := by
  unfold parameterRaw UnitChain.equalValue
  simp only [vertices, RFAP.PolygonWinding.chainRaw]
  rw [same]
  rw [RFAP.PolygonWinding.coordinate_segment_self_doubledWinding]
  exact Int.zero_add 0

theorem parameterRaw_repeatClosed
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex} (p : GaussianPolynomial)
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex) :
    ∀ circuits : Nat,
      parameterRaw p (chain.repeatClosed circuits) =
        (circuits : Int) * parameterRaw p chain
  | 0 => by
      simp only [repeatClosed, parameterRaw_nil]
      ring1
  | circuits + 1 => by
      rw [repeatClosed, parameterRaw_append,
        parameterRaw_repeatClosed p chain circuits]
      simp only [Nat.cast_add, Nat.cast_one]
      ring1

/-- The two finite edgewise formulas used to compare one subdivided unit
quarter with its fixed right-half-plane rotation. -/
structure RotationFormulas
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter) {start finish : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo start finish) : Prop where
  halfPlane : RFAP.PolygonWinding.ChainHalfPlaneFormula
    (unitCircuitRotatedCoordinate quarter) start.value chain.vertices
  product : RFAP.PolygonWinding.ChainProductFormula
    RFAP.GlobalWinding.coordinatePolynomial
    (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
    start.value chain.vertices

def rotationEndpointCorrection
    (quarter : UnitCircuitQuarter) (point : Gaussian) : Int :=
  (RFAP.PolygonWinding.vertexHalfPlaneCorrection2
      (unitCircuitRotatedCoordinate quarter) point : Int) +
    RFAP.WindingProduct.vertexProductCorrection2
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter)) point

theorem RotationFormulas.nil
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter) (vertex : UnitVertex) :
    RotationFormulas (degree := degree)
      (degreeAtLeastTwo := degreeAtLeastTwo) quarter
      (UnitChain.nil vertex) :=
  { halfPlane := RFAP.PolygonWinding.ChainHalfPlaneFormula.nil vertex.value
    product := RFAP.PolygonWinding.ChainProductFormula.nil vertex.value }

theorem RotationFormulas.cons
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter)
    {source middle finish : UnitVertex}
    {small : UnitMoveSmall source.unit middle.unit degree degreeAtLeastTwo}
    {remaining : UnitChain degree degreeAtLeastTwo middle finish}
    (edgeHalfPlane : RFAP.HalfPlane.Formula
      (RFAP.PathPolynomial.pathReal (unitCircuitRotatedCoordinate quarter)
        source.value (middle.value - source.value))
      (RFAP.PathPolynomial.pathImag (unitCircuitRotatedCoordinate quarter)
        source.value (middle.value - source.value)) 0 1)
    (edgeProduct : RFAP.WindingProduct.LineProductFormula
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
      source.value (middle.value - source.value) 0 1)
    (tail : RotationFormulas quarter remaining) :
    RotationFormulas quarter (UnitChain.cons small remaining) :=
  { halfPlane := .cons edgeHalfPlane tail.halfPlane
    product := .cons edgeProduct tail.product }

theorem RotationFormulas.castFinish
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (quarter : UnitCircuitQuarter)
    {start left right : UnitVertex} (same : left = right)
    {chain : UnitChain degree degreeAtLeastTwo start left}
    (formulas : RotationFormulas quarter chain) :
    RotationFormulas quarter (UnitChain.castFinish same chain) := by
  subst right
  exact formulas

/-- The open raw winding of one rotated quarter chain is reduced entirely
to its two displayed endpoints. -/
theorem RotationFormulas.coordinateRaw_eq_endpoint
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {quarter : UnitCircuitQuarter} {start finish : UnitVertex}
    {chain : UnitChain degree degreeAtLeastTwo start finish}
    (formulas : RotationFormulas quarter chain) :
    RFAP.PolygonWinding.chainRaw
        RFAP.GlobalWinding.coordinatePolynomial start.value chain.vertices =
      rotationEndpointCorrection quarter start.value -
        rotationEndpointCorrection quarter finish.value := by
  have halfPlane :=
    RFAP.PolygonWinding.chainRaw_eq_endpoint_corrections_of_halfPlane
      (unitCircuitRotatedCoordinate quarter) start.value chain.vertices
        formulas.halfPlane
  rw [chain.vertices_terminal] at halfPlane
  have product := RFAP.PolygonWinding.chainRaw_mul_of_formula
    RFAP.GlobalWinding.coordinatePolynomial
    (RFAP.GlobalWinding.gaussianConstant (unitCircuitRotation quarter))
    start.value chain.vertices formulas.product
  have constantZero := RFAP.PolygonWinding.chainRaw_gaussianConstant_zero
    (unitCircuitRotation_ne_zero quarter) start.value chain.vertices
  unfold rotationEndpointCorrection
  unfold unitCircuitRotatedCoordinate at halfPlane ⊢
  rw [halfPlane, constantZero] at product
  rw [chain.vertices_terminal] at product
  omega

/-- Rational lift vertices obtained by expanding every chamber move into its
three explicit connector edges. -/
def liftVertices {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : UnitVertex} →
      (chain : UnitChain degree degreeAtLeastTwo start finish) →
      (start.frame degree degreeAtLeastTwo).Index → List Gaussian
  | _, _, .nil _, _ => []
  | source, _, .cons (middle := middle) small remaining, index =>
      unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo small
          index ++
        remaining.liftVertices
          ((unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
            small).finalIndex index)

/-- Parameter vertices synchronized with `liftVertices`; stationary repeats
record the two connector edges after each genuine parameter move. -/
def liftParameterVertices
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : UnitVertex} →
      UnitChain degree degreeAtLeastTwo start finish → List Gaussian
  | _, _, .nil _ => []
  | _, _, .cons (middle := middle) _ remaining =>
      unitMoveParameterVertices middle.value ++
        remaining.liftParameterVertices

/-- The two stationary connector copies attached to every genuine parameter
move do not alter its coordinate winding. -/
theorem liftParameterRaw_eq_parameterRaw
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish),
      RFAP.PolygonWinding.chainRaw
          RFAP.GlobalWinding.coordinatePolynomial start.value
          chain.liftParameterVertices =
        parameterRaw RFAP.GlobalWinding.coordinatePolynomial chain
  | _, _, .nil _ => rfl
  | source, finish, .cons (middle := middle) _ remaining => by
      simp only [liftParameterVertices, unitMoveParameterVertices,
        List.cons_append, List.nil_append, RFAP.PolygonWinding.chainRaw,
        RFAP.PolygonWinding.coordinate_segment_self_doubledWinding,
        Int.zero_add, parameterRaw, vertices]
      rw [liftParameterRaw_eq_parameterRaw remaining]
      rfl

/-- The edgewise finite Rouché formulas telescope along an arbitrary finite
unit chain. -/
theorem liftHomotopy
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index),
      RFAP.PolygonWinding.ChainHomotopyFormula
        (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
        RFAP.GlobalWinding.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index) start.value chain.liftParameterVertices
  | _, _, .nil vertex, index => .nil (vertex.ownerAnchor degree
      degreeAtLeastTwo index) vertex.value
  | source, finish, .cons (middle := middle) small remaining, index => by
      let move := unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := unitMoveLiftHomotopy source.unit middle.unit degree
        degreeAtLeastTwo small index
      have tail := liftHomotopy remaining nextIndex
      have liftEndpoint := unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : RFAP.PolygonWinding.terminal
          (unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [UnitVertex.ownerAnchor, UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [liftVertices, liftParameterVertices, UnitVertex.ownerAnchor,
        UnitVertex.frame, unitMoveLiftBase, move, nextIndex] using combined

theorem liftProductFormula
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index)
      (exponent : Nat),
      RFAP.PolygonWinding.ChainProductFormula
        (RFAP.GlobalWinding.coordinatePositivePower exponent)
        RFAP.GlobalWinding.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index)
  | _, _, .nil vertex, index, _ =>
      .nil (vertex.ownerAnchor degree degreeAtLeastTwo index)
  | source, finish, .cons (middle := middle) small remaining, index,
      exponent => by
      let move := unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := unitMoveLiftProductFormula source.unit middle.unit degree
        degreeAtLeastTwo small index exponent
      have tail := liftProductFormula remaining nextIndex exponent
      have liftEndpoint := unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : RFAP.PolygonWinding.terminal
          (unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [UnitVertex.ownerAnchor, UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [liftVertices, UnitVertex.ownerAnchor, UnitVertex.frame,
        unitMoveLiftBase, move, nextIndex] using combined

/-- Constructive modulo-four phase data for every rational connector edge of
an arbitrary finite owner lift. -/
def liftPhaseFormula
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : UnitVertex} →
      (chain : UnitChain degree degreeAtLeastTwo start finish) →
      (index : (start.frame degree degreeAtLeastTwo).Index) →
      RFAP.PolygonWinding.ChainPhaseFormula
        RFAP.GlobalWinding.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index)
  | _, _, .nil vertex, index =>
      RFAP.PolygonWinding.ChainPhaseFormula.nil
        RFAP.GlobalWinding.coordinatePolynomial
        (vertex.ownerAnchor degree degreeAtLeastTwo index)
  | source, finish, .cons (middle := middle) small remaining, index => by
      let move := unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := unitMoveLiftPhaseFormula source.unit middle.unit degree
        degreeAtLeastTwo small index
      have tail := liftPhaseFormula remaining nextIndex
      have liftEndpoint := unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : RFAP.PolygonWinding.terminal
          (unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [UnitVertex.ownerAnchor, UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [liftVertices, UnitVertex.ownerAnchor, UnitVertex.frame,
        unitMoveLiftBase, move, nextIndex] using combined

theorem liftVertices_terminal
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index),
      RFAP.PolygonWinding.terminal
          (start.ownerAnchor degree degreeAtLeastTwo index)
          (chain.liftVertices index) =
        finish.ownerAnchor degree degreeAtLeastTwo
          (chain.toPath.finalIndex index)
  | _, _, .nil _, _ => rfl
  | source, finish, .cons (middle := middle) small remaining, index => by
      rw [liftVertices, RFAP.PolygonWinding.terminal_append]
      rw [show source.ownerAnchor degree degreeAtLeastTwo index =
          unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo
            index by rfl]
      have moveEndpoint := unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have moveEndpoint' : RFAP.PolygonWinding.terminal
          (unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo
            ((unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
              small).finalIndex index) := by
        simpa only [UnitVertex.ownerAnchor, UnitVertex.frame] using moveEndpoint
      rw [moveEndpoint']
      rw [liftVertices_terminal remaining
        ((unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
          small).finalIndex index)]
      apply congrArg (finish.ownerAnchor degree degreeAtLeastTwo)
      exact (CCL.FiniteMonodromy.ChamberPath.finalIndex_append
        (unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo small)
        remaining.toPath index).symm

theorem liftParameterVertices_terminal
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : UnitVertex}
      (chain : UnitChain degree degreeAtLeastTwo start finish),
      RFAP.PolygonWinding.terminal start.value
          chain.liftParameterVertices = finish.value
  | _, _, .nil _ => rfl
  | source, finish, .cons (middle := middle) _ remaining => by
      rw [liftParameterVertices, RFAP.PolygonWinding.terminal_append]
      change RFAP.PolygonWinding.terminal middle.value
        remaining.liftParameterVertices = finish.value
      exact liftParameterVertices_terminal remaining

/-- For a closed unit chain, the synchronized parameter polygon has the
same raw winding as the underlying genuine parameter moves. -/
theorem closedLiftParameterRaw_eq_parameterRaw
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex) :
    RFAP.PolygonWinding.closedRaw RFAP.GlobalWinding.coordinatePolynomial
        vertex.value chain.liftParameterVertices =
      parameterRaw RFAP.GlobalWinding.coordinatePolynomial chain := by
  unfold RFAP.PolygonWinding.closedRaw
  rw [RFAP.PolygonWinding.chainRaw_append,
    liftParameterVertices_terminal]
  rw [liftParameterRaw_eq_parameterRaw]
  simp only [RFAP.PolygonWinding.chainRaw,
    RFAP.PolygonWinding.coordinate_segment_self_doubledWinding,
    Int.add_zero]

/-- A returned owner lift has a fully constructed modulo-four phase
telescope, including its final rational segment back to the initial anchor. -/
def closedPhaseFormula_of_return
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    RFAP.PolygonWinding.ClosedPhaseFormula
      RFAP.GlobalWinding.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (robustChamberFrame_degree (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (unitRobustBox (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex UnitVertex.ownerAnchor UnitVertex.frame
    rw [robustChamberFrame_owner_box]
    exact RFAP.Boxes.Box.contains_anchor _
  have openFormula := chain.liftPhaseFormula index
  have endpoint := chain.liftVertices_terminal index
  rw [returned] at endpoint
  have finalCertificate : RFAP.PathClearance.Certificate
      (RFAP.PathPolynomial.pathReal RFAP.GlobalWinding.coordinatePolynomial
        base (base - base))
      (RFAP.PathPolynomial.pathImag RFAP.GlobalWinding.coordinatePolynomial
        base (base - base))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [show RFAP.GlobalWinding.coordinatePolynomial =
        RFAP.GlobalWinding.coordinatePositivePower 0 from rfl] using
      unitRobustSegmentCoordinatePowerCertificate
        (nonzero_of_normSq_eq_one vertex.unit) vertex.unit degree
        degreeAtLeastTwo degreeIndex baseInside baseInside 0
  have tail : RFAP.PolygonWinding.ChainPhaseFormula
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.PolygonWinding.terminal base (chain.liftVertices index)) [base] := by
    rw [endpoint]
    exact RFAP.PolygonWinding.ChainPhaseFormula.consOfClearance finalCertificate
      (RFAP.PolygonWinding.ChainPhaseFormula.nil
        RFAP.GlobalWinding.coordinatePolynomial base)
  exact openFormula.append tail

/-- Constructive normalization of a returned rational owner polygon. -/
def normalizedLiftOfReturn
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    RFAP.PolygonWinding.Normalized
      RFAP.GlobalWinding.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) :=
  RFAP.PolygonWinding.Normalized.ofPhaseFormula _ _ _
    (closedPhaseFormula_of_return chain index returned)

theorem closedProductFormula_of_return
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index)
    (exponent : Nat) :
    RFAP.PolygonWinding.ClosedProductFormula
      (RFAP.GlobalWinding.coordinatePositivePower exponent)
      RFAP.GlobalWinding.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (robustChamberFrame_degree (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (unitRobustBox (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex UnitVertex.ownerAnchor UnitVertex.frame
    rw [robustChamberFrame_owner_box]
    exact RFAP.Boxes.Box.contains_anchor _
  have openFormula := chain.liftProductFormula index exponent
  have endpoint := chain.liftVertices_terminal index
  rw [returned] at endpoint
  have finalEdge := unitRobustSegmentProductFormula
    (nonzero_of_normSq_eq_one vertex.unit) vertex.unit degree degreeAtLeastTwo
    degreeIndex baseInside baseInside exponent
  have tail : RFAP.PolygonWinding.ChainProductFormula
      (RFAP.GlobalWinding.coordinatePositivePower exponent)
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.PolygonWinding.terminal base (chain.liftVertices index)) [base] := by
    rw [endpoint]
    exact .cons finalEdge (.nil base)
  exact openFormula.append tail

theorem closedHomotopyFormula_of_return
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    RFAP.PolygonWinding.ClosedHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) vertex.value chain.liftParameterVertices := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (robustChamberFrame_degree (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (unitRobustBox (nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex UnitVertex.ownerAnchor UnitVertex.frame
    rw [robustChamberFrame_owner_box]
    exact RFAP.Boxes.Box.contains_anchor _
  have openFormula := chain.liftHomotopy index
  have liftEndpoint := chain.liftVertices_terminal index
  rw [returned] at liftEndpoint
  have parameterEndpoint := chain.liftParameterVertices_terminal
  have finalEdge := unitRobustSegmentHomotopy vertex.unit vertex.unit degree
    degreeAtLeastTwo (UnitMoveSmall.reflexive vertex.unit degree degreeAtLeastTwo)
    degreeIndex baseInside baseInside
  have tail : RFAP.PolygonWinding.ChainHomotopyFormula
      (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
      RFAP.GlobalWinding.coordinatePolynomial
      (RFAP.PolygonWinding.terminal base (chain.liftVertices index)) [base]
      (RFAP.PolygonWinding.terminal vertex.value chain.liftParameterVertices)
      [vertex.value] := by
    rw [liftEndpoint, parameterEndpoint]
    exact .cons finalEdge (.nil base vertex.value)
  exact openFormula.append tail

theorem closedPositivePowerFormula_of_return
    {degree : RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : UnitVertex}
    (chain : UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    (exponent : Nat) → RFAP.PolygonWinding.ClosedPositivePowerFormula
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) exponent
  | 0 => .zero
  | exponent + 1 => .succ
      (closedPositivePowerFormula_of_return chain index returned exponent)
      (closedProductFormula_of_return chain index returned exponent)

end UnitChain

private def unitQuarterChainFrom (quarter : UnitCircuitQuarter)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (start : Nat) : (count : Nat) →
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex quarter degree degreeAtLeastTwo start)
      (unitCircuitVertex quarter degree degreeAtLeastTwo (start + count))
  | 0 => by
      simpa only [Nat.add_zero] using
        (UnitChain.nil
          (unitCircuitVertex quarter degree degreeAtLeastTwo start))
  | count + 1 => by
      let step : UnitMoveSmall
          (unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : UnitChain degree degreeAtLeastTwo
          (unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1) count
      let raw : UnitChain degree degreeAtLeastTwo
          (unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        UnitChain.cons step tail
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      exact UnitChain.castFinish
        (congrArg
          (unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint) raw

private theorem unitQuarterChainFrom_rotationFormulas
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (start : Nat) :
    ∀ (count : Nat),
      start + count ≤ unitCircuitStepCount degree degreeAtLeastTwo →
      UnitChain.RotationFormulas quarter
        (unitQuarterChainFrom quarter degree degreeAtLeastTwo start count)
  | 0, _ => by
      have chainEq :
          unitQuarterChainFrom quarter degree degreeAtLeastTwo start 0 =
            UnitChain.nil
              (unitCircuitVertex quarter degree degreeAtLeastTwo start) := by
        rfl
      rw [chainEq]
      exact UnitChain.RotationFormulas.nil
        (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo) quarter
        (unitCircuitVertex quarter degree degreeAtLeastTwo start)
  | count + 1, bound => by
      have edgeBound : start <
          unitCircuitStepCount degree degreeAtLeastTwo := by omega
      have tailBound : start + 1 + count ≤
          unitCircuitStepCount degree degreeAtLeastTwo := by omega
      let step : UnitMoveSmall
          (unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : UnitChain degree degreeAtLeastTwo
          (unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1) count
      have tailFormulas : UnitChain.RotationFormulas quarter tail := by
        exact unitQuarterChainFrom_rotationFormulas quarter degree
          degreeAtLeastTwo (start + 1) count tailBound
      have edgeHalfPlane := unitCircuitRotatedEdgeHalfPlaneFormula quarter
        degree degreeAtLeastTwo edgeBound
      have edgeProduct := unitCircuitEdgeProductFormula quarter degree
        degreeAtLeastTwo edgeBound
      let raw : UnitChain degree degreeAtLeastTwo
          (unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        UnitChain.cons step tail
      have rawFormulas : UnitChain.RotationFormulas quarter raw := by
        exact UnitChain.RotationFormulas.cons quarter edgeHalfPlane edgeProduct
          tailFormulas
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      have castFormulas := UnitChain.RotationFormulas.castFinish quarter
        (congrArg (unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint)
        rawFormulas
      simpa only [unitQuarterChainFrom, step, tail, raw] using castFormulas

def unitQuarterChain (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex quarter degree degreeAtLeastTwo 0)
      (unitCircuitVertex quarter degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo)) :=
  UnitChain.castFinish
    (congrArg (unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (unitCircuitStepCount degree degreeAtLeastTwo)))
    (unitQuarterChainFrom quarter degree degreeAtLeastTwo 0
      (unitCircuitStepCount degree degreeAtLeastTwo))

theorem unitQuarterChain_rotationFormulas
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain.RotationFormulas quarter
      (unitQuarterChain quarter degree degreeAtLeastTwo) := by
  exact UnitChain.RotationFormulas.castFinish quarter
    (congrArg (unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (unitCircuitStepCount degree degreeAtLeastTwo)))
    (unitQuarterChainFrom_rotationFormulas quarter degree degreeAtLeastTwo 0
      (unitCircuitStepCount degree degreeAtLeastTwo) (by omega))

theorem unitCircuitVertex_zero_value
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (unitCircuitVertex quarter degree degreeAtLeastTwo 0).value =
      unitCircuitMultiplier quarter := by
  simp only [unitCircuitVertex, unitCircuitPoint,
    unitCircuitParameter_zero, unitQuarterPoint_zero,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem unitCircuitVertex_last_value
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (unitCircuitVertex quarter degree degreeAtLeastTwo
      (unitCircuitStepCount degree degreeAtLeastTwo)).value =
      unitCircuitMultiplier quarter * ⟨0, 1⟩ := by
  simp only [unitCircuitVertex, unitCircuitPoint,
    unitCircuitParameter_last, unitQuarterPoint_one]

theorem unitQuarter_rotationCorrection_difference
    (quarter : UnitCircuitQuarter) :
    UnitChain.rotationEndpointCorrection quarter
        (unitCircuitMultiplier quarter) -
      UnitChain.rotationEndpointCorrection quarter
        (unitCircuitMultiplier quarter * ⟨0, 1⟩) = 1 := by
  cases quarter <;> decide

/-- Every explicitly subdivided stereographic quarter contributes one unit
of the repository's raw winding. -/
theorem unitQuarterChain_raw_eq_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    RFAP.PolygonWinding.chainRaw RFAP.GlobalWinding.coordinatePolynomial
        (unitCircuitVertex quarter degree degreeAtLeastTwo 0).value
        (unitQuarterChain quarter degree degreeAtLeastTwo).vertices = 1 := by
  have identity :
      RFAP.PolygonWinding.chainRaw RFAP.GlobalWinding.coordinatePolynomial
          (unitCircuitVertex quarter degree degreeAtLeastTwo 0).value
          (unitQuarterChain quarter degree degreeAtLeastTwo).vertices =
        UnitChain.rotationEndpointCorrection quarter
            (unitCircuitVertex quarter degree degreeAtLeastTwo 0).value -
          UnitChain.rotationEndpointCorrection quarter
            (unitCircuitVertex quarter degree degreeAtLeastTwo
              (unitCircuitStepCount degree degreeAtLeastTwo)).value :=
    UnitChain.RotationFormulas.coordinateRaw_eq_endpoint
      (unitQuarterChain_rotationFormulas quarter degree degreeAtLeastTwo)
  rw [unitCircuitVertex_zero_value,
    unitCircuitVertex_last_value] at identity
  rw [unitQuarter_rotationCorrection_difference] at identity
  rw [unitCircuitVertex_zero_value]
  rw [identity]

theorem unitQuarterChain_parameterRaw_eq_one
    (quarter : UnitCircuitQuarter) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain.parameterRaw RFAP.GlobalWinding.coordinatePolynomial
      (unitQuarterChain quarter degree degreeAtLeastTwo) = 1 :=
  unitQuarterChain_raw_eq_one quarter degree degreeAtLeastTwo

def unitCircuitFirstSecondJoin (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex .first degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo))
      (unitCircuitVertex .second degree degreeAtLeastTwo 0) :=
  UnitChain.equalValue (unitCircuitQuarters_join degree degreeAtLeastTwo).1

def unitCircuitSecondThirdJoin (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex .second degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo))
      (unitCircuitVertex .third degree degreeAtLeastTwo 0) :=
  UnitChain.equalValue (unitCircuitQuarters_join degree degreeAtLeastTwo).2.1

def unitCircuitThirdFourthJoin (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex .third degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo))
      (unitCircuitVertex .fourth degree degreeAtLeastTwo 0) :=
  UnitChain.equalValue (unitCircuitQuarters_join degree degreeAtLeastTwo).2.2.1

def unitCircuitFourthFirstJoin (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex .fourth degree degreeAtLeastTwo
        (unitCircuitStepCount degree degreeAtLeastTwo))
      (unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  UnitChain.equalValue (unitCircuitQuarters_join degree degreeAtLeastTwo).2.2.2

/-- Four explicitly subdivided rational quarter-arcs, joined into one closed
positive unit-parameter circuit. -/
def unitCircuitChain (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain degree degreeAtLeastTwo
      (unitCircuitVertex .first degree degreeAtLeastTwo 0)
      (unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  (((((((unitQuarterChain .first degree degreeAtLeastTwo).append
      (unitCircuitFirstSecondJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .second degree degreeAtLeastTwo)).append
      (unitCircuitSecondThirdJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .third degree degreeAtLeastTwo)).append
      (unitCircuitThirdFourthJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .fourth degree degreeAtLeastTwo)).append
      (unitCircuitFourthFirstJoin degree degreeAtLeastTwo)

theorem unitCircuitChain_parameterRaw_eq_four
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    UnitChain.parameterRaw RFAP.GlobalWinding.coordinatePolynomial
      (unitCircuitChain degree degreeAtLeastTwo) = 4 := by
  unfold unitCircuitChain
  simp only [UnitChain.parameterRaw_append,
    unitQuarterChain_parameterRaw_eq_one,
    unitCircuitFirstSecondJoin, unitCircuitSecondThirdJoin,
    unitCircuitThirdFourthJoin, unitCircuitFourthFirstJoin,
    UnitChain.parameterRaw_equalValue]
  decide

/-- Repeating the explicit unit circuit gives the corresponding exact raw
winding on the synchronized parameter polygon, including its stationary
connector copies. -/
theorem repeatedUnitCircuitParameterPolygon_windingFour
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (circuits : Nat) :
    RFAP.PolygonWinding.closedRaw RFAP.GlobalWinding.coordinatePolynomial
        (unitCircuitVertex .first degree degreeAtLeastTwo 0).value
        (UnitChain.liftParameterVertices
          ((unitCircuitChain degree degreeAtLeastTwo).repeatClosed circuits)) =
      (4 : Int) * circuits := by
  rw [UnitChain.closedLiftParameterRaw_eq_parameterRaw,
    UnitChain.parameterRaw_repeatClosed,
    unitCircuitChain_parameterRaw_eq_four]
  ring1

/-- The concrete closed finite chamber path for the family `Z^d-w`. -/
def unitCircuitLoop (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.ChamberPath
      ((unitCircuitVertex .first degree degreeAtLeastTwo 0).frame degree
        degreeAtLeastTwo)
      ((unitCircuitVertex .first degree degreeAtLeastTwo 0).frame degree
        degreeAtLeastTwo) :=
  (unitCircuitChain degree degreeAtLeastTwo).toPath

/-- A finite move is small on every currently displayed owner boundary. -/
def MoveSmall
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (target : Gaussian) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Prop :=
  ∀ index : (chamberFrame sourceNonzero degree degreeAtLeastTwo).Index,
    normSq (source - target) <
      ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
        index).clearance.bound

/-- The single finite clearance needed to move each isolated owner boundary.
Fresh target-polynomial ambient-line clearances are computed after the
Rouché move by the eliminant-driven Newton-band extractor. -/
structure GlobalMoveSmall
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (target : Gaussian) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Prop where
  boundary : ∀ index : Fin degree.value,
    normSq (source - target) <
      (isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.clearance.bound

/-- The degree-normalized boundary budget is the local Rouché half-move. -/
theorem GlobalMoveSmall.toMoveSmall
    {source : Gaussian} {sourceNonzero : source ≠ 0}
    {target : Gaussian} {degree : RootDegree}
    {degreeAtLeastTwo : 2 ≤ degree.value}
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    MoveSmall sourceNonzero target degree degreeAtLeastTwo := by
  intro index
  have bound := small.boundary
    (Fin.cast
      (chamberFrame_degree sourceNonzero degree degreeAtLeastTwo) index)
  rw [isolatedTrack_initial_clearance_bound_eq_chamber_owner] at bound
  exact bound

/-- The Rouché-moved local owner, regarded as a raw target-polynomial state
inside the common equal-norm global square. -/
def transportedRawState
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.RawSubdivision.RawWindingState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  let sourceState :=
    (isolatedTrack sourceNonzero degree degreeAtLeastTwo index).initial
  let sourceOwner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial source degree) :=
    { box := sourceState.box
      proper := sourceState.proper
      clearance := sourceState.clearance
      rawWindingFour := sourceState.rawWindingFour }
  let targetOwner := transportedOwner degree sourceOwner (small.boundary index)
  exact
    { box := sourceState.box
      refinesAmbient := by
        rw [← largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
        exact sourceState.refinesAmbient
      proper := targetOwner.proper
      clearance := targetOwner.clearance
      rawWinding_ne := by
        intro zero
        have fourZero : (4 : Int) = 0 := by
          rw [← targetOwner.rawWindingFour]
          exact zero
        exact (by decide : (4 : Int) ≠ 0) fourZero }

@[simp] theorem transportedRawState_box
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedRawState sourceNonzero equalNorm degree degreeAtLeastTwo small
      index).box =
      (isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box := rfl

/-- One target-polynomial Newton-band extraction inside the moved owner. -/
def transportedExtraction
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :=
  RFAP.NewtonBand.extract
    (by rw [polynomial_degree]; exact degreeAtLeastTwo)
    (squarefree targetNonzero degree)
    (isolationInput targetNonzero degree degreeAtLeastTwo).elimination
    (transportedRawState sourceNonzero equalNorm degree degreeAtLeastTwo small
      index) (epsilon := (1 : Coordinate)) (by decide)

/-- Move one source owner by Rouché, then run one target-polynomial
Newton-band extraction inside it.  The extraction computes four fresh safe
full lines in the common equal-norm ambient square, so no ambient-line
clearance has to survive the coefficient move. -/
def transportedIsolatedState
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) := by
  let extracted := transportedExtraction sourceNonzero targetNonzero equalNorm
    degree degreeAtLeastTwo small index
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }

theorem transportedIsolatedState_refines
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedIsolatedState sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).box.Refines
      (isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box := by
  change (transportedExtraction sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).box.Refines _
  rw [← transportedRawState_box sourceNonzero equalNorm degree
    degreeAtLeastTwo small index]
  exact (transportedExtraction sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).strictCurrent.refines

/-- The target squarefree extraction program started from a transported
global state. -/
def transportedIsolatedTrack
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  RFAP.ShrinkingTrack.ofInitial
    (by rw [polynomial_degree]; exact degreeAtLeastTwo)
    (squarefree targetNonzero degree)
    (isolationInput targetNonzero degree degreeAtLeastTwo).elimination
    (transportedIsolatedState sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index)

theorem transportedIsolatedTrack_initial_refines
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin degree.value) :
    (transportedIsolatedTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      (isolatedTrack sourceNonzero degree degreeAtLeastTwo
        index).initial.box :=
  transportedIsolatedState_refines sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index

theorem moveCountEq
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (target : Gaussian) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (chamberFrame sourceNonzero degree degreeAtLeastTwo).degree =
      (coefficientTable target degree).degree := by
  rw [chamberFrame_degree, coefficientTable_degree]

def moveSourceIndex
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (target : Gaussian) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (coefficientTable target degree).degree) :
    (chamberFrame sourceNonzero degree degreeAtLeastTwo).Index :=
  Fin.cast
    (moveCountEq sourceNonzero target degree degreeAtLeastTwo).symm index

/-- Intermediate chamber at the target parameter which deliberately keeps
the preceding owner boxes.  It is used only for the Rouché half of a move;
a subsequent same-polynomial overlap rebases to the independently isolated
target frame. -/
def transportedFrame
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable target degree
  chamber := by
    let sourceFrame := chamberFrame sourceNonzero degree degreeAtLeastTwo
    let sourceIndex : Fin (coefficientTable target degree).degree →
        sourceFrame.Index :=
      moveSourceIndex sourceNonzero target degree degreeAtLeastTwo
    let sourceOwner :
        (index : Fin (coefficientTable target degree).degree) →
          CCL.ProgressivePolynomialRoots.LocalOwner
            (polynomial source degree) := fun index =>
      CCL.FiniteMonodromy.castOwner
        (chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
        (sourceFrame.owner (sourceIndex index))
    let rawOwners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (polynomial target degree)
        (coefficientTable target degree).degree :=
      { owner := fun index => transportedOwner degree
          (sourceOwner index) (by
            dsimp only [sourceOwner]
            rw [CCL.FiniteMonodromy.castOwner_clearance_bound]
            exact small (sourceIndex index))
        pairwiseSeparated := by
          intro left right different
          have sourceDifferent : sourceIndex left ≠ sourceIndex right := by
            intro equal
            have valueEqual : left.val = right.val := by
              simpa only [sourceIndex, moveSourceIndex,
                Fin.val_cast] using
                congrArg (fun index => index.val) equal
            exact different (Fin.ext valueEqual)
          have separated := sourceFrame.pairwiseSeparated
            (sourceIndex left) (sourceIndex right) sourceDifferent
          have leftBox : (sourceOwner left).box =
              (sourceFrame.owner (sourceIndex left)).box := by
            exact CCL.FiniteMonodromy.castOwner_box _ _
          have rightBox : (sourceOwner right).box =
              (sourceFrame.owner (sourceIndex right)).box := by
            exact CCL.FiniteMonodromy.castOwner_box _ _
          simpa only [transportedOwner,
            CCL.FiniteMonodromy.OwnerBridge.rightOwner,
            CCL.FiniteMonodromy.OwnerBridge.ofForward,
            leftBox, rightBox] using separated }
    let owners : CCL.ProgressivePolynomialRoots.OwnerFamily
        (coefficientTable target degree).polynomial
        (coefficientTable target degree).degree :=
      CCL.FiniteMonodromy.castOwnerFamily
        (coefficientTable_polynomial target degree).symm rawOwners
    let squarefreeCertificate :=
      coefficientTableSquarefree targetNonzero degree
    exact
      { degreeAtLeastTwo := by
          rw [coefficientTable_degree]
          exact degreeAtLeastTwo
        squarefree := squarefreeCertificate
        owners := owners
        referenceSmall := coefficientTable_allowances_lt target degree
          (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
            (coefficientTable target degree) squarefreeCertificate owners)
        referenceMaximality := by
          intro familyCount family pairwise
          let result : CCL.BoxRFAPBridge.Result
              (coefficientTable target degree).polynomial := by
            rw [coefficientTable_polynomial]
            exact isolationResult targetNonzero degree degreeAtLeastTwo
          have bound := result.boxes.maximality family pairwise
          have tablePolynomialDegree :
              (coefficientTable target degree).polynomial.natDegree =
                (polynomial target degree).natDegree :=
            congrArg RFAP.ComputablePolynomial.DensePolynomial.natDegree
              (coefficientTable_polynomial target degree)
          calc
            familyCount ≤
                (coefficientTable target degree).polynomial.natDegree := bound
            _ = (polynomial target degree).natDegree := tablePolynomialDegree
            _ = degree.value := polynomial_degree target degree
            _ = (coefficientTable target degree).degree :=
              (coefficientTable_degree target degree).symm }

@[simp] theorem transportedFrame_degree
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).degree = degree.value := by
  exact coefficientTable_degree target degree

@[simp] theorem transportedFrame_polynomial
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).polynomial = polynomial target degree := by
  exact coefficientTable_polynomial target degree

@[simp] theorem transportedFrame_owner_box
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : MoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
      small).owner
        (Fin.cast
          (moveCountEq sourceNonzero target degree degreeAtLeastTwo) index)).box =
      ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box := by
  simp only [CCL.FiniteMonodromy.ChamberFrame.owner,
    transportedFrame, moveSourceIndex,
    CCL.FiniteMonodromy.castOwnerFamily_owner_box,
    CCL.FiniteMonodromy.castOwner_box, transportedOwner,
    CCL.FiniteMonodromy.OwnerBridge.rightOwner,
    CCL.FiniteMonodromy.OwnerBridge.ofForward]
  congr 1

/-! ## Same-polynomial rebasing at the target vertex -/

/-- The source owner index represented by one index of the intermediate
target frame, normalized to `Fin d`. -/
def transportedSourceDegreeIndex
    {source : Gaussian} (sourceNonzero : source ≠ 0)
    (target : Gaussian) (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin (coefficientTable target degree).degree) :
    Fin degree.value :=
  Fin.cast (chamberFrame_degree sourceNonzero degree degreeAtLeastTwo)
    (moveSourceIndex sourceNonzero target degree degreeAtLeastTwo index)

/-- The globally supported transported track corresponding to an owner of
the intermediate target frame. -/
def transportedFrameTrack
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  transportedIsolatedTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
      (transportedSourceDegreeIndex sourceNonzero target degree
        degreeAtLeastTwo index)

theorem transportedFrameTrack_initial_refines
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box := by
  let sourceIndex :=
    moveSourceIndex sourceNonzero target degree degreeAtLeastTwo index
  have sourceBox := isolatedTrack_initial_box_eq_chamber_owner
    sourceNonzero degree degreeAtLeastTwo sourceIndex
  have transportedBox := transportedFrame_owner_box sourceNonzero
    targetNonzero degree degreeAtLeastTwo small.toMoveSmall sourceIndex
  have targetIndex :
      Fin.cast (moveCountEq sourceNonzero target degree degreeAtLeastTwo)
          sourceIndex = index := by
    apply Fin.ext
    rfl
  have transportedBoxAtIndex :
      ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box =
        ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
          sourceIndex).box := by
    rw [← targetIndex]
    exact transportedBox
  calc
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).initial.box.Refines
        (isolatedTrack sourceNonzero degree degreeAtLeastTwo
          (Fin.cast
            (chamberFrame_degree sourceNonzero degree degreeAtLeastTwo)
            sourceIndex)).initial.box := by
      exact transportedIsolatedTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small _
    _ = ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner
          sourceIndex).box := sourceBox
    _ = ((transportedFrame sourceNonzero targetNonzero degree
          degreeAtLeastTwo small.toMoveSmall).owner index).box :=
      transportedBoxAtIndex.symm

theorem isolationResult_support
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (isolationResult parameterNonzero degree degreeAtLeastTwo).boxes.isolation.support =
      RFAP.GlobalWinding.largeSquareBox (polynomial parameter degree) := rfl

theorem transportedFrameTrack_supported
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).initial.box.Refines
      (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.support := by
  rw [isolationResult_support]
  exact (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).initial.refinesAmbient

theorem transportedFrameTracks_pairwise
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (left right : Fin (coefficientTable target degree).degree)
    (different : left ≠ right) :
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small left).initial.box.Separated
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small right).initial.box := by
  exact ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
    small.toMoveSmall).pairwiseSeparated left right different).of_refines
      (transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small left)
      (transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small right)

/-- Deterministic target-isolation ownership of a transported source track. -/
def transportedOwnerSelection
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.Maximality.OwnerSelection
      (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation
      (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index) :=
  (isolationResult targetNonzero degree degreeAtLeastTwo).boxes.ownership
    (transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index)
    (transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
      degree degreeAtLeastTwo small index)

/-- The target isolation's raw list length equals the displayed chamber
degree. -/
theorem targetTrackCountEq
    {target : Gaussian} (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
      (coefficientTable target degree).degree := by
  calc
    (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length =
        (polynomial target degree).natDegree :=
      (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks_length
    _ = degree.value := polynomial_degree target degree
    _ = (coefficientTable target degree).degree :=
      (coefficientTable_degree target degree).symm

/-- The finite owner map from transported-frame indices to independently
isolated target-frame indices. -/
def rebaseMap
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Fin (coefficientTable target degree).degree →
      Fin (coefficientTable target degree).degree := fun index =>
  Fin.cast (targetTrackCountEq targetNonzero degree degreeAtLeastTwo)
    (transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).owner

theorem rebaseMap_injective
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    Function.Injective (rebaseMap sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small) := by
  let output :=
    (isolationResult targetNonzero degree degreeAtLeastTwo).boxes.isolation
  let family : Fin (coefficientTable target degree).degree →
      RFAP.ShrinkingTrack.WindingOneTrack (polynomial target degree)
        (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
    fun index => transportedFrameTrack sourceNonzero targetNonzero equalNorm
      degree degreeAtLeastTwo small index
  have rawInjective : Function.Injective (fun index =>
      (transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).owner) := by
    change Function.Injective (fun index =>
      (RFAP.Maximality.selectOutputOwner
        (by rw [polynomial_degree]; exact degreeAtLeastTwo)
        (squarefree targetNonzero degree)
        (isolationInput targetNonzero degree degreeAtLeastTwo).elimination
        output (family index)
        (transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
          degree degreeAtLeastTwo small index)).owner)
    exact RFAP.Maximality.selectedOwner_injective
      (by rw [polynomial_degree]; exact degreeAtLeastTwo)
      (squarefree targetNonzero degree)
      (isolationInput targetNonzero degree degreeAtLeastTwo).elimination
      output family
      (transportedFrameTrack_supported sourceNonzero targetNonzero equalNorm
        degree degreeAtLeastTwo small)
      (transportedFrameTracks_pairwise sourceNonzero targetNonzero equalNorm
        degree degreeAtLeastTwo small)
  intro left right equal
  apply rawInjective
  apply Fin.ext
  simpa only [rebaseMap, Fin.val_cast] using
    congrArg (fun index => index.val) equal

def rebaseMatching
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.FiniteBijection
      (coefficientTable target degree).degree
      (coefficientTable target degree).degree :=
  CCL.FiniteMonodromy.FiniteBijection.ofInjectiveEndomap
    (rebaseMap sourceNonzero targetNonzero equalNorm degree degreeAtLeastTwo
      small)
    (rebaseMap_injective sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small)

@[simp] theorem rebaseMatching_forward
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (rebaseMatching sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small).forward index =
      rebaseMap sourceNonzero targetNonzero equalNorm degree degreeAtLeastTwo
        small index := rfl

@[simp] theorem targetTrack_get_box_eq_chamber_owner
    {target : Gaussian} (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin
      (isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.length) :
    ((isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.get index).initial.box =
      ((chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        (Fin.cast (targetTrackCountEq targetNonzero degree degreeAtLeastTwo)
          index)).box := by
  simp [chamberFrame,
    CCL.FiniteMonodromy.ChamberFrame.owner,
    CCL.ProgressivePolynomialRoots.OwnerFamily.ofResult,
    CCL.BoxRFAPBridge.Result.trackAt,
    RFAP.ExactIsolation.Output.trackAt,
    RFAP.ExactIsolation.Output.trackIndex]

/-- The common refined target-polynomial state used as the actual bridge
box between the transported frame and the independent target isolation. -/
def rebaseRefinedState
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    RFAP.ShrinkingTrack.WindingOneState (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) :=
  let output :=
    (isolationResult targetNonzero degree degreeAtLeastTwo).boxes.isolation
  let track := transportedFrameTrack sourceNonzero targetNonzero equalNorm
    degree degreeAtLeastTwo small index
  track.refine track.initial
    (RFAP.Maximality.assignmentRadius (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) output)
    (RFAP.Maximality.assignmentRadius_pos
      (polynomial target degree)
      (RFAP.GlobalWinding.largeSquareBox (polynomial target degree)) output)

/-- Same-polynomial bridge on the common refined owner box. -/
def rebaseBridge
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    CCL.FiniteMonodromy.OwnerBridge
      (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).polynomial
      (chamberFrame targetNonzero degree degreeAtLeastTwo).polynomial := by
  let state := rebaseRefinedState sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index
  let owner : CCL.ProgressivePolynomialRoots.LocalOwner
      (polynomial target degree) :=
    { box := state.box
      proper := state.proper
      clearance := state.clearance
      rawWindingFour := state.rawWindingFour }
  exact (CCL.FiniteMonodromy.OwnerBridge.reflexive owner).cast
    (transportedFrame_polynomial sourceNonzero targetNonzero degree
      degreeAtLeastTwo small.toMoveSmall).symm
    (chamberFrame_polynomial targetNonzero degree degreeAtLeastTwo).symm

@[simp] theorem rebaseBridge_box
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).box =
      (rebaseRefinedState sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).box := by
  rw [rebaseBridge]
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_box]
  rfl

theorem selectedTargetBox_eq_rebaseMap_owner
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    ((isolationResult targetNonzero degree
        degreeAtLeastTwo).boxes.isolation.tracks.get
      (transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
        degreeAtLeastTwo small index).owner).initial.box =
      ((chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        (rebaseMap sourceNonzero targetNonzero equalNorm degree
          degreeAtLeastTwo small index)).box := by
  exact targetTrack_get_box_eq_chamber_owner targetNonzero degree
    degreeAtLeastTwo _

theorem rebaseBridge_refines_transported
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree degreeAtLeastTwo
      small index).box.Refines
      ((transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).owner index).box := by
  rw [rebaseBridge_box]
  exact ((transportedFrameTrack sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small index).nested _ _ _).trans
      (transportedFrameTrack_initial_refines sourceNonzero targetNonzero
        equalNorm degree degreeAtLeastTwo small index)

theorem rebaseBridge_refines_target
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : Fin (coefficientTable target degree).degree) :
    (rebaseBridge sourceNonzero targetNonzero equalNorm degree degreeAtLeastTwo
      small index).box.Refines
      ((chamberFrame targetNonzero degree degreeAtLeastTwo).owner
        ((rebaseMatching sourceNonzero targetNonzero equalNorm degree
          degreeAtLeastTwo small).forward index)).box := by
  have strict :=
    (transportedOwnerSelection sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small index).strict
  have refined := strict.refines
  rw [rebaseBridge_box, rebaseMatching_forward]
  rw [← selectedTargetBox_eq_rebaseMap_owner sourceNonzero targetNonzero
    equalNorm degree degreeAtLeastTwo small index]
  exact refined

/-- Complete same-polynomial overlap which rebases the moved owners to the
independently computed target frame. -/
def rebaseOverlap
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberOverlap
      (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall)
      (chamberFrame targetNonzero degree degreeAtLeastTwo) where
  matching := rebaseMatching sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
  bridge := rebaseBridge sourceNonzero targetNonzero equalNorm degree
    degreeAtLeastTwo small
  bridge_refines_left := rebaseBridge_refines_transported sourceNonzero
    targetNonzero equalNorm degree degreeAtLeastTwo small
  bridge_refines_right := rebaseBridge_refines_target sourceNonzero
    targetNonzero equalNorm degree degreeAtLeastTwo small

/-! ## One complete small chamber move -/

def moveBridge
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    CCL.FiniteMonodromy.OwnerBridge
      (chamberFrame sourceNonzero degree degreeAtLeastTwo).polynomial
      (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall).polynomial := by
  let owner := CCL.FiniteMonodromy.castOwner
    (chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
    ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index)
  let raw := CCL.FiniteMonodromy.OwnerBridge.ofForward owner
    (ownerMoveRouche degree owner (by
      dsimp only [owner]
      rw [CCL.FiniteMonodromy.castOwner_clearance_bound]
      exact small.toMoveSmall index))
  exact raw.cast
    (chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo).symm
    (transportedFrame_polynomial sourceNonzero targetNonzero degree
      degreeAtLeastTwo small.toMoveSmall).symm

@[simp] theorem moveBridge_box
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo)
    (index : (chamberFrame sourceNonzero degree degreeAtLeastTwo).Index) :
    (moveBridge sourceNonzero targetNonzero degree degreeAtLeastTwo small
      index).box =
      ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box := by
  rw [moveBridge, CCL.FiniteMonodromy.OwnerBridge.cast_box]
  change
    (CCL.FiniteMonodromy.castOwner
      (chamberFrame_polynomial sourceNonzero degree degreeAtLeastTwo)
      ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index)).box =
    ((chamberFrame sourceNonzero degree degreeAtLeastTwo).owner index).box
  exact CCL.FiniteMonodromy.castOwner_box _ _

def moveOverlap
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberOverlap
      (chamberFrame sourceNonzero degree degreeAtLeastTwo)
      (transportedFrame sourceNonzero targetNonzero degree degreeAtLeastTwo
        small.toMoveSmall) where
  matching := CCL.FiniteMonodromy.FiniteBijection.cast
    (moveCountEq sourceNonzero target degree degreeAtLeastTwo)
  bridge := moveBridge sourceNonzero targetNonzero degree degreeAtLeastTwo small
  bridge_refines_left := by
    intro index
    rw [moveBridge_box]
    exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [moveBridge_box,
      CCL.FiniteMonodromy.FiniteBijection.cast_forward]
    rw [transportedFrame_owner_box]
    exact RFAP.Boxes.Box.refines_refl _

/-- A complete finite chamber step: first carry the old boxes by Rouché,
then rebase through a refined common target-polynomial box. -/
def smallMovePath
    {source target : Gaussian}
    (sourceNonzero : source ≠ 0) (targetNonzero : target ≠ 0)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : GlobalMoveSmall sourceNonzero target degree degreeAtLeastTwo) :
    CCL.FiniteMonodromy.ChamberPath
      (chamberFrame sourceNonzero degree degreeAtLeastTwo)
      (chamberFrame targetNonzero degree degreeAtLeastTwo) :=
  .cons (moveOverlap sourceNonzero targetNonzero degree degreeAtLeastTwo small)
    (.cons (rebaseOverlap sourceNonzero targetNonzero equalNorm degree
      degreeAtLeastTwo small)
      (.nil (chamberFrame targetNonzero degree degreeAtLeastTwo)))

/-! ## The explicit rational parameter circuit -/

/-- Four oriented sides of the positively oriented unit square. -/
inductive CircuitSide
  | bottom
  | right
  | top
  | left
deriving DecidableEq, Repr

/-- A rational parameter on one oriented side, with the common parameter
running from `-1` to `1`. -/
def circuitValue : CircuitSide → Coordinate → Gaussian
  | .bottom, position => ⟨position, -1⟩
  | .right, position => ⟨1, position⟩
  | .top, position => ⟨-position, 1⟩
  | .left, position => ⟨-1, -position⟩

/-- No point of any displayed circuit side is the excluded parameter zero.
The certificate is coordinatewise and does not quantify over a completed
curve. -/
theorem circuitValue_ne_zero (side : CircuitSide) (position : Coordinate) :
    circuitValue side position ≠ 0 := by
  intro zero
  cases side with
  | bottom =>
      have imaginary := congrArg RFAP.ConstructiveGaussian.Gaussian.im zero
      change (-1 : Coordinate) = 0 at imaginary
      exact (by decide : (-1 : Coordinate) ≠ 0) imaginary
  | right =>
      have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
      change (1 : Coordinate) = 0 at real
      exact (by decide : (1 : Coordinate) ≠ 0) real
  | top =>
      have imaginary := congrArg RFAP.ConstructiveGaussian.Gaussian.im zero
      change (1 : Coordinate) = 0 at imaginary
      exact (by decide : (1 : Coordinate) ≠ 0) imaginary
  | left =>
      have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
      change (-1 : Coordinate) = 0 at real
      exact (by decide : (-1 : Coordinate) ≠ 0) real

def parameterBox : RFAP.Boxes.Box :=
  RFAP.Boxes.Box.symmetric 1 (by decide)

theorem parameterBox_proper : parameterBox.Proper := by
  constructor <;> decide

/-- The four rational affine sides join in cyclic order. -/
theorem circuit_sides_join :
    circuitValue .bottom 1 = circuitValue .right (-1) ∧
      circuitValue .right 1 = circuitValue .top (-1) ∧
      circuitValue .top 1 = circuitValue .left (-1) ∧
      circuitValue .left 1 = circuitValue .bottom (-1) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The displayed parameter square makes exactly one positive circuit of
zero in the repository's integer-valued raw convention. -/
theorem parameterCircuit_windingFour :
    RFAP.Winding.quadrupledBoxWinding
      RFAP.GlobalWinding.coordinatePolynomial parameterBox = 4 := by
  exact (RFAP.GlobalWinding.coordinate_symmetric_normalization
    (R := (1 : Coordinate)) (by decide)).1

theorem parameterCircuit_winding :
    RFAP.Winding.boxWinding
      RFAP.GlobalWinding.coordinatePolynomial parameterBox = 1 := by
  exact (RFAP.GlobalWinding.coordinate_symmetric_normalization
    (R := (1 : Coordinate)) (by decide)).2.2

/-- Raising the circuit coordinate to the `d`th power multiplies its finite
raw winding by exactly `d`.  This is the arithmetic equality later applied
to a closed owner lift. -/
theorem parameterCircuit_power_windingFour (degree : RootDegree) :
    RFAP.Winding.quadrupledBoxWinding
        (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
        parameterBox =
      (4 : Int) * degree.value := by
  have power :=
    RFAP.GlobalWinding.quadrupledBoxWinding_coordinatePositivePower
      (R := (1 : Coordinate)) (by decide) (degree.value - 1)
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 : Nat) : Int) + 1 =
      (degree.value : Int) := by
    rw [← Int.natCast_one, ← Int.natCast_add, exponent]
  rw [castExponent] at power
  simpa only [parameterBox] using power

/-! ### The same circuit as an explicit finite polygon -/

def parameterBase : Gaussian := ⟨-1, -1⟩

def parameterVertices : List Gaussian :=
  [⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩]

/-- Direct kernel calculation of the four affine coordinate edges.  This is
the polygonal form used by a synchronized returned owner lift. -/
theorem parameterPolygon_windingFour :
    RFAP.PolygonWinding.closedRaw
        RFAP.GlobalWinding.coordinatePolynomial
        parameterBase parameterVertices = 4 := by
  decide

/-- Repeating the displayed square `additional+1` times has exactly the
corresponding raw winding. -/
theorem repeatedParameterPolygon_windingFour (additional : Nat) :
    RFAP.PolygonWinding.closedRaw
        RFAP.GlobalWinding.coordinatePolynomial parameterBase
        (RFAP.PolygonWinding.repeatClosedVertices
          parameterBase parameterVertices additional) =
      (4 : Int) * (additional + 1) := by
  rw [RFAP.PolygonWinding.closedRaw_repeatClosedVertices,
    parameterPolygon_windingFour]
  simp only [Nat.cast_add, Nat.cast_one]
  ring1

/-! ## The final finite orbit deduction -/

/-- The exact arithmetic extracted from a closed finite lift.  Its natural
`liftWinding` is the normalized winding of the returned owner polygon, and
`power_identity` is the finite equality `d Wind(lift) = circuits` obtained
by raising that polygon to the `d`th power and comparing it with the
parameter-square traversal. -/
structure ReturnWindingCertificate (degree : RootDegree) (circuits : Nat)
    where
  liftWinding : Nat
  power_identity : degree.value * liftWinding = circuits

/-- Any computed return of the explicit unit-circuit lift yields the exact
natural divisibility identity `d * k = circuits`.  The integer `k` is first
constructed by the finite phase scanner; positivity of `d` and the
nonnegative circuit count then shows that it is a natural number. -/
def unitCircuitReturnWindingCertificate
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : ((unitCircuitVertex .first degree degreeAtLeastTwo 0).frame
      degree degreeAtLeastTwo).Index)
    (circuits : Nat)
    (returned : CCL.FiniteMonodromy.FiniteBijection.iterateForward
      (unitCircuitLoop degree degreeAtLeastTwo).monodromy circuits index =
        index) :
    ReturnWindingCertificate degree circuits := by
  let vertex := unitCircuitVertex .first degree degreeAtLeastTwo 0
  let circuit := unitCircuitChain degree degreeAtLeastTwo
  let repeated := circuit.repeatClosed circuits
  have repeatedReturned : repeated.toPath.finalIndex index = index := by
    rw [UnitChain.repeatClosed_finalIndex]
    simpa only [unitCircuitLoop, circuit, repeated, vertex] using returned
  let normalized := repeated.normalizedLiftOfReturn index repeatedReturned
  have powerWinding := RFAP.PolygonWinding.closedRaw_coordinatePositivePower
    (vertex.ownerAnchor degree degreeAtLeastTwo index)
    (repeated.liftVertices index) (degree.value - 1)
    (repeated.closedPositivePowerFormula_of_return index repeatedReturned
      (degree.value - 1))
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 + 1 : Nat) : Int) =
      (degree.value : Int) := by
    rw [exponent]
  rw [castExponent] at powerWinding
  have compared := RFAP.PolygonWinding.closedRaw_eq_of_homotopy
    (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
    RFAP.GlobalWinding.coordinatePolynomial
    (vertex.ownerAnchor degree degreeAtLeastTwo index)
    (repeated.liftVertices index) vertex.value
    repeated.liftParameterVertices
    (repeated.closedHomotopyFormula_of_return index repeatedReturned)
  have parameterWinding := repeatedUnitCircuitParameterPolygon_windingFour
    degree degreeAtLeastTwo circuits
  have fourIdentity :
      (4 : Int) * ((degree.value : Int) * normalized.winding) =
        4 * (circuits : Int) := by
    calc
      (4 : Int) * ((degree.value : Int) * normalized.winding) =
          (degree.value : Int) * (4 * normalized.winding) := by ring1
      _ = (degree.value : Int) *
          RFAP.PolygonWinding.closedRaw
            RFAP.GlobalWinding.coordinatePolynomial
            (vertex.ownerAnchor degree degreeAtLeastTwo index)
            (repeated.liftVertices index) := by
        rw [normalized.raw_eq]
      _ = RFAP.PolygonWinding.closedRaw
          (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
          (vertex.ownerAnchor degree degreeAtLeastTwo index)
          (repeated.liftVertices index) := powerWinding.symm
      _ = RFAP.PolygonWinding.closedRaw
          RFAP.GlobalWinding.coordinatePolynomial vertex.value
          repeated.liftParameterVertices := compared.symm
      _ = 4 * (circuits : Int) := parameterWinding
  have intIdentity :
      (degree.value : Int) * normalized.winding = (circuits : Int) :=
    mul_left_cancel₀ (by decide : (4 : Int) ≠ 0) fourIdentity
  cases windingShape : normalized.winding with
  | ofNat liftWinding =>
      refine
        { liftWinding := liftWinding
          power_identity := ?_ }
      apply Int.ofNat_inj.mp
      rw [Nat.cast_mul]
      simpa only [windingShape, Int.ofNat_eq_natCast] using intIdentity
  | negSucc magnitude =>
      rw [windingShape, Int.ofNat_mul_negSucc] at intIdentity
      have productNonzero : degree.value * Nat.succ magnitude ≠ 0 :=
        Nat.mul_ne_zero (Nat.ne_of_gt degree.positive) (Nat.succ_ne_zero _)
      cases productShape : degree.value * Nat.succ magnitude with
      | zero => exact (productNonzero productShape).elim
      | succ preceding =>
          rw [productShape] at intIdentity
          exact Int.noConfusion intIdentity

/-! ### Returned rational power lifts -/

/-- Fully finite evidence attached to one returned owner after
`additional+1` positive parameter circuits.  The source is a rational
polygonal sample lift.  Its power is compared, edge by edge, with the
explicitly repeated parameter square. -/
structure ReturnedLift (degree : RootDegree) (additional : Nat) where
  liftBase : Gaussian
  liftVertices : List Gaussian
  liftWinding : Nat
  liftNormalized :
    RFAP.PolygonWinding.closedRaw
        RFAP.GlobalWinding.coordinatePolynomial
        liftBase liftVertices =
      (4 : Int) * liftWinding
  powerFormula :
    RFAP.PolygonWinding.ClosedPositivePowerFormula
      liftBase liftVertices (degree.value - 1)
  comparison : RFAP.PolygonWinding.ClosedHomotopyFormula
    (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
    RFAP.GlobalWinding.coordinatePolynomial
    liftBase liftVertices parameterBase
    (RFAP.PolygonWinding.repeatClosedVertices
      parameterBase parameterVertices additional)

/-- The finite product and Rouché telescopes turn a returned rational lift
into the exact natural identity `d * Wind(lift) = circuits`. -/
def ReturnedLift.returnWindingCertificate
    {degree : RootDegree} {additional : Nat}
    (lift : ReturnedLift degree additional) :
    ReturnWindingCertificate degree (additional + 1) := by
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 + 1 : Nat) : Int) =
      (degree.value : Int) := by
    rw [exponent]
  have powerWinding :=
    RFAP.PolygonWinding.closedRaw_coordinatePositivePower
      lift.liftBase lift.liftVertices (degree.value - 1) lift.powerFormula
  rw [castExponent] at powerWinding
  have compared := RFAP.PolygonWinding.closedRaw_eq_of_homotopy
    (RFAP.GlobalWinding.coordinatePositivePower (degree.value - 1))
    RFAP.GlobalWinding.coordinatePolynomial
    lift.liftBase lift.liftVertices parameterBase
    (RFAP.PolygonWinding.repeatClosedVertices
      parameterBase parameterVertices additional) lift.comparison
  have parameterWinding := repeatedParameterPolygon_windingFour additional
  have fourIdentity :
      (4 : Int) *
          ((degree.value : Int) * (lift.liftWinding : Int)) =
        4 * ((additional + 1 : Nat) : Int) := by
    calc
      (4 : Int) *
          ((degree.value : Int) * (lift.liftWinding : Int)) =
        (degree.value : Int) *
          (4 * (lift.liftWinding : Int)) := by ring1
      _ = (degree.value : Int) *
          RFAP.PolygonWinding.closedRaw
            RFAP.GlobalWinding.coordinatePolynomial
            lift.liftBase lift.liftVertices := by
        rw [lift.liftNormalized]
      _ = RFAP.PolygonWinding.closedRaw
          (RFAP.GlobalWinding.coordinatePositivePower
            (degree.value - 1)) lift.liftBase lift.liftVertices :=
        powerWinding.symm
      _ = RFAP.PolygonWinding.closedRaw
          RFAP.GlobalWinding.coordinatePolynomial parameterBase
          (RFAP.PolygonWinding.repeatClosedVertices
            parameterBase parameterVertices additional) := compared.symm
      _ = 4 * ((additional + 1 : Nat) : Int) := parameterWinding
  have intIdentity :
      (degree.value : Int) * (lift.liftWinding : Int) =
        ((additional + 1 : Nat) : Int) := by
    exact mul_left_cancel₀ (by decide : (4 : Int) ≠ 0) fourIdentity
  refine
    { liftWinding := lift.liftWinding
      power_identity := ?_ }
  apply Int.ofNat_inj.mp
  rw [Nat.cast_mul]
  exact intIdentity

theorem ReturnWindingCertificate.degree_dvd
    {degree : RootDegree} {circuits : Nat}
    (certificate : ReturnWindingCertificate degree circuits) :
    degree.value ∣ circuits := by
  exact ⟨certificate.liftWinding, certificate.power_identity.symm⟩

/-- Once every returning owner lift supplies the finite power-winding
identity, the computed monodromy is forced to be one full degree-cycle. -/
theorem monodromy_isSingleCycle_of_returnWinding
    {frame : CCL.FiniteMonodromy.ChamberFrame}
    (degree : RootDegree)
    (degreeEq : frame.degree = degree.value)
    (loop : CCL.FiniteMonodromy.ChamberPath frame frame)
    (returnWinding : ∀ (index : frame.Index) (circuits : Nat),
      0 < circuits →
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
          loop.monodromy circuits index = index →
        ReturnWindingCertificate degree circuits) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle loop.monodromy := by
  apply
    CCL.FiniteMonodromy.FiniteBijection.isSingleCycle_of_noEarlyReturn
  intro index circuits circuitsPositive circuitsSmall returned
  have divides :=
    (returnWinding index circuits circuitsPositive returned).degree_dvd
  rcases divides with ⟨factor, factorization⟩
  have factorPositive : 0 < factor := by
    by_cases factorZero : factor = 0
    · subst factor
      have circuitsZero : circuits = 0 := by
        simpa only [Nat.mul_zero] using factorization
      exact ((Nat.ne_of_gt circuitsPositive) circuitsZero).elim
    · exact Nat.pos_of_ne_zero factorZero
  have degreeLeCircuits : degree.value ≤ circuits := by
    calc
      degree.value ≤ degree.value * factor :=
        Nat.le_mul_of_pos_right degree.value factorPositive
      _ = circuits := factorization.symm
  have circuitsBelowDegree : circuits < degree.value := by
    rw [← degreeEq]
    exact circuitsSmall
  exact (Nat.not_lt_of_ge degreeLeCircuits circuitsBelowDegree).elim

/-- Headline finite monodromy theorem for `Z^d-w`: the explicitly computed
rational unit circuit permutes the `d` isolated owner boxes in one cycle.
Every ingredient is a bounded rational calculation; in particular, the
returned-lift winding used to exclude a shorter orbit is constructed by the
finite sign-event scanner above. -/
theorem unitCircuitMonodromy_isSingleCycle
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      (unitCircuitLoop degree degreeAtLeastTwo).monodromy := by
  apply monodromy_isSingleCycle_of_returnWinding degree
    (loop := unitCircuitLoop degree degreeAtLeastTwo)
  · unfold UnitVertex.frame
    exact robustChamberFrame_degree
      (nonzero_of_normSq_eq_one
        (unitCircuitVertex .first degree degreeAtLeastTwo 0).unit)
      (unitCircuitVertex .first degree degreeAtLeastTwo 0).unit
      degree degreeAtLeastTwo
  · intro index circuits _circuitsPositive returned
    exact unitCircuitReturnWindingCertificate degree degreeAtLeastTwo
      index circuits returned

/-- Geometric form of the single-cycle result.  Its premise contains only
the returned finite rational polygons and the per-edge executable product
and Rouché certificates; divisibility is no longer an assumed arithmetic
fact. -/
theorem monodromy_isSingleCycle_of_returnedLifts
    {frame : CCL.FiniteMonodromy.ChamberFrame}
    (degree : RootDegree)
    (degreeEq : frame.degree = degree.value)
    (loop : CCL.FiniteMonodromy.ChamberPath frame frame)
    (returnedLift : ∀ (index : frame.Index) (circuits : Nat),
      0 < circuits →
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
          loop.monodromy circuits index = index →
        ReturnedLift degree (circuits - 1)) :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle loop.monodromy := by
  apply monodromy_isSingleCycle_of_returnWinding degree degreeEq loop
  intro index circuits circuitsPositive returned
  have certificate :=
    (returnedLift index circuits circuitsPositive returned)
      |>.returnWindingCertificate
  have predecessor : circuits - 1 + 1 = circuits :=
    Nat.sub_add_cancel circuitsPositive
  simpa only [predecessor] using certificate

end CCL.PowerMonodromy
