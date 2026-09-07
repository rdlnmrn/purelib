import CCL.Riemann.LegendreGaussManin

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

namespace CCL.Riemann.LegendrePicardFuchs

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

open CCL.Riemann.LegendrePaths

/-! ## Displayed polynomial data -/

/-- The parameter-independent factor `g(x) = x(x-1)`. -/
def basePolynomial : GaussianPolynomial := ⟨[1, -1, 0]⟩

/-- The affine coordinate polynomial. -/
def coordinatePolynomial : GaussianPolynomial := ⟨[1, 0]⟩

/-- The numerator `x g(x)` of the parameter derivative of `x dx/y`. -/
def weightedBasePolynomial : GaussianPolynomial := ⟨[1, -1, 0, 0]⟩

/-- The explicit spatial derivative of the Legendre cubic. -/
def spatialDerivativePolynomial (parameter : Gaussian) :
    GaussianPolynomial :=
  ⟨[3, -2 * (1 + parameter), parameter]⟩

/-- The exact primitive numerator used in the first connection row. -/
def firstPrimitivePolynomial : GaussianPolynomial := ⟨[2, -2, 0]⟩

/-- The exact primitive numerator used in the second connection row. -/
def secondPrimitivePolynomial (parameter : Gaussian) :
    GaussianPolynomial :=
  ⟨[2 * parameter, -2 * parameter, 0]⟩

/-- The exact primitive numerator for the second-order scalar equation. -/
def picardFuchsPrimitivePolynomial : GaussianPolynomial :=
  ⟨[2, -4, 2, 0, 0]⟩

@[simp] theorem basePolynomial_eval (point : Gaussian) :
    basePolynomial.eval point = point * (point - 1) := by
  unfold basePolynomial RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem coordinatePolynomial_eval (point : Gaussian) :
    coordinatePolynomial.eval point = point := by
  unfold coordinatePolynomial RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem weightedBasePolynomial_eval (point : Gaussian) :
    weightedBasePolynomial.eval point =
      point * (point * (point - 1)) := by
  unfold weightedBasePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem spatialDerivativePolynomial_eval
    (parameter point : Gaussian) :
    (spatialDerivativePolynomial parameter).eval point =
      3 * point * point - 2 * (1 + parameter) * point + parameter := by
  unfold spatialDerivativePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The displayed quadratic agrees pointwise with the finite automatic
derivative of the displayed Legendre cubic.  Pointwise equality is the exact
interface consumed by finite quadrature and avoids any appeal to polynomial
function extensionality. -/
theorem spatialDerivativePolynomial_matches_automatic
    (parameter point : Gaussian) :
    (spatialDerivativePolynomial parameter).eval point =
      (RFAP.ConstructiveGCD.derivative (polynomial parameter)).eval point := by
  rw [spatialDerivativePolynomial_eval]
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold polynomial RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem firstPrimitivePolynomial_eval (point : Gaussian) :
    firstPrimitivePolynomial.eval point = 2 * (point * (point - 1)) := by
  unfold firstPrimitivePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem secondPrimitivePolynomial_eval
    (parameter point : Gaussian) :
    (secondPrimitivePolynomial parameter).eval point =
      2 * parameter * (point * (point - 1)) := by
  unfold secondPrimitivePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem picardFuchsPrimitivePolynomial_eval (point : Gaussian) :
    picardFuchsPrimitivePolynomial.eval point =
      2 * (point * (point - 1)) ^ 2 := by
  unfold picardFuchsPrimitivePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the first exact primitive is the displayed
linear polynomial. -/
theorem firstPrimitiveDerivative_eval (point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative firstPrimitivePolynomial).eval point =
      4 * point - 2 := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold firstPrimitivePolynomial
    RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the second exact primitive retains its
displayed parameter factor. -/
theorem secondPrimitiveDerivative_eval (parameter point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative
      (secondPrimitivePolynomial parameter)).eval point =
        parameter * (4 * point - 2) := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold secondPrimitivePolynomial
    RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the scalar-equation primitive numerator. -/
theorem picardFuchsPrimitiveDerivative_eval (point : Gaussian) :
    (RFAP.ConstructiveGCD.derivative
      picardFuchsPrimitivePolynomial).eval point =
        4 * (point * (point - 1)) * (2 * point - 1) := by
  unfold RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold picardFuchsPrimitivePolynomial
    RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-! ## Exact parameter clearance -/

/-- Rational lower bounds keeping one displayed parameter away from both
singular Legendre values. -/
structure ParameterClearance (parameter : Gaussian) where
  zeroBound : Coordinate
  zeroPositive : 0 < zeroBound
  zeroLower : zeroBound <=
    RFAP.ConstructiveGaussian.Gaussian.normSq parameter
  oneBound : Coordinate
  onePositive : 0 < oneBound
  oneLower : oneBound <=
    RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1)

namespace ParameterClearance

/-- Every point of an already certified Legendre segment carries the exact
parameter denominator clearance needed by the connection. -/
def ofSegmentPoint {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) (fraction : Coordinate) :
    ParameterClearance (segment.geometry.pointAt fraction) where
  zeroBound := segment.safe.avoidsZero.bound
  zeroPositive := segment.safe.avoidsZero.positive
  zeroLower := by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_zero] using
      segment.safe.avoidsZero.normSq_lower fraction
  oneBound := segment.safe.avoidsOne.bound
  onePositive := segment.safe.avoidsOne.positive
  oneLower := segment.safe.avoidsOne.normSq_lower fraction

theorem parameter_ne_zero {parameter : Gaussian}
    (clearance : ParameterClearance parameter) : parameter ≠ 0 := by
  intro parameterZero
  have normZero : RFAP.ConstructiveGaussian.Gaussian.normSq parameter = 0 := by
    rw [parameterZero]
    rfl
  have lower : clearance.zeroBound <= 0 :=
    clearance.zeroLower.trans_eq normZero
  exact (not_le_of_gt clearance.zeroPositive) lower

theorem parameter_sub_one_ne_zero {parameter : Gaussian}
    (clearance : ParameterClearance parameter) : parameter - 1 ≠ 0 := by
  intro differenceZero
  have normZero :
      RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1) = 0 := by
    rw [differenceZero]
    rfl
  have lower : clearance.oneBound <= 0 :=
    clearance.oneLower.trans_eq normZero
  exact (not_le_of_gt clearance.onePositive) lower

theorem one_sub_parameter_ne_zero {parameter : Gaussian}
    (clearance : ParameterClearance parameter) : 1 - parameter ≠ 0 := by
  intro differenceZero
  apply clearance.parameter_sub_one_ne_zero
  have oneEqual : (1 : Gaussian) = parameter := sub_eq_zero.mp differenceZero
  exact sub_eq_zero.mpr oneEqual.symm

/-- The common fraction-free connection denominator. -/
def connectionDenominator (parameter : Gaussian) : Gaussian :=
  2 * parameter * (1 - parameter)

theorem connectionDenominator_ne_zero {parameter : Gaussian}
    (clearance : ParameterClearance parameter) :
    connectionDenominator parameter ≠ 0 :=
  RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      (by decide) clearance.parameter_ne_zero)
    clearance.one_sub_parameter_ne_zero

/-- A positive rational lower bound for the squared norm of the common
connection denominator. -/
def connectionLowerSq {parameter : Gaussian}
    (clearance : ParameterClearance parameter) : Coordinate :=
  4 * clearance.zeroBound * clearance.oneBound

theorem connectionLowerSq_positive {parameter : Gaussian}
    (clearance : ParameterClearance parameter) :
    0 < clearance.connectionLowerSq := by
  unfold connectionLowerSq
  exact RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      clearance.zeroPositive) clearance.onePositive

theorem connectionLowerSq_le_normSq {parameter : Gaussian}
    (clearance : ParameterClearance parameter) :
    clearance.connectionLowerSq <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (connectionDenominator parameter) := by
  have productLower : clearance.zeroBound * clearance.oneBound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq parameter *
        RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct clearance.zeroLower
      clearance.oneLower clearance.onePositive.le
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg parameter)
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      productLower (by decide : (0 : Coordinate) <= 4)
  calc
    clearance.connectionLowerSq =
        4 * (clearance.zeroBound * clearance.oneBound) := by
      unfold connectionLowerSq
      ring1
    _ <= 4 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq parameter *
          RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1)) := scaled
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq
        (connectionDenominator parameter) := by
      unfold connectionDenominator
      rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
        RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
      have opposite : (1 - parameter : Gaussian) = -(parameter - 1) := by
        ring1
      rw [opposite, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
      change 4 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq parameter *
            RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1)) =
        (2 * 2 + 0 * 0) *
          RFAP.ConstructiveGaussian.Gaussian.normSq parameter *
            RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - 1)
      ring1

end ParameterClearance

/-! ## Fraction-free connection identities -/

def curveValue (parameter point : Gaussian) : Gaussian :=
  point * (point - 1) * (point - parameter)

def baseValue (point : Gaussian) : Gaussian := point * (point - 1)

def spatialDerivativeValue (parameter point : Gaussian) : Gaussian :=
  3 * point * point - 2 * (1 + parameter) * point + parameter

def connectionDenominator (parameter : Gaussian) : Gaussian :=
  ParameterClearance.connectionDenominator parameter

/-- First row of the fraction-free Gauss--Manin connection.  After division
by `2 y^3`, this is
`D ∂λ(dx/y) = λ dx/y - x dx/y + d(2x(x-1)/y)`.
-/
theorem firstConnection_cleared (parameter point : Gaussian) :
    connectionDenominator parameter * baseValue point =
      2 * (parameter - point) * curveValue parameter point +
        2 * (4 * point - 2) * curveValue parameter point -
          (2 * baseValue point) * spatialDerivativeValue parameter point := by
  unfold connectionDenominator ParameterClearance.connectionDenominator
    baseValue curveValue spatialDerivativeValue
  ring1

/-- Second row of the same connection, with primitive numerator
`2 λ x(x-1)`. -/
theorem secondConnection_cleared (parameter point : Gaussian) :
    connectionDenominator parameter * (point * baseValue point) =
      2 * (parameter - parameter * point) * curveValue parameter point +
        2 * (parameter * (4 * point - 2)) *
          curveValue parameter point -
        (2 * parameter * baseValue point) *
          spatialDerivativeValue parameter point := by
  unfold connectionDenominator ParameterClearance.connectionDenominator
    baseValue curveValue spatialDerivativeValue
  ring1

/-- One fully displayed row of the fraction-free connection reduction.  The
left side is twice the usual parameter-derivative numerator; the right side
is the basis contribution plus the numerator of `d(R/y)`, with all powers of
`y` cleared using `y² = f`. -/
structure ConnectionReduction (parameter : Gaussian) where
  parameterDerivativeNumerator : GaussianPolynomial
  basisConstant : Gaussian
  basisLinear : Gaussian
  primitiveNumerator : GaussianPolynomial
  clearedIdentity : forall point : Gaussian,
    connectionDenominator parameter *
        parameterDerivativeNumerator.eval point =
      2 * (basisConstant + basisLinear * point) *
          (polynomial parameter).eval point +
        2 * (RFAP.ConstructiveGCD.derivative primitiveNumerator).eval point *
          (polynomial parameter).eval point -
        primitiveNumerator.eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial parameter)).eval point

theorem firstConnectionPolynomialIdentity (parameter point : Gaussian) :
    connectionDenominator parameter * basePolynomial.eval point =
      2 * (parameter + (-1) * point) *
          (polynomial parameter).eval point +
        2 * (RFAP.ConstructiveGCD.derivative
          firstPrimitivePolynomial).eval point *
            (polynomial parameter).eval point -
        firstPrimitivePolynomial.eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial parameter)).eval point := by
  rw [basePolynomial_eval, polynomial_eval,
    firstPrimitiveDerivative_eval, firstPrimitivePolynomial_eval,
    ← spatialDerivativePolynomial_matches_automatic parameter point,
    spatialDerivativePolynomial_eval]
  unfold connectionDenominator ParameterClearance.connectionDenominator
  ring1

theorem secondConnectionPolynomialIdentity (parameter point : Gaussian) :
    connectionDenominator parameter * weightedBasePolynomial.eval point =
      2 * (parameter + (-parameter) * point) *
          (polynomial parameter).eval point +
        2 * (RFAP.ConstructiveGCD.derivative
          (secondPrimitivePolynomial parameter)).eval point *
            (polynomial parameter).eval point -
        (secondPrimitivePolynomial parameter).eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial parameter)).eval point := by
  rw [weightedBasePolynomial_eval, polynomial_eval,
    secondPrimitiveDerivative_eval, secondPrimitivePolynomial_eval,
    ← spatialDerivativePolynomial_matches_automatic parameter point,
    spatialDerivativePolynomial_eval]
  unfold connectionDenominator ParameterClearance.connectionDenominator
  ring1

/-- The first row
`D ∂λ ω₀ = λ ω₀ - ω₁ + d(2g/y)` as finite polynomial data. -/
def firstConnectionReduction (parameter : Gaussian) :
    ConnectionReduction parameter where
  parameterDerivativeNumerator := basePolynomial
  basisConstant := parameter
  basisLinear := -1
  primitiveNumerator := firstPrimitivePolynomial
  clearedIdentity := firstConnectionPolynomialIdentity parameter

/-- The second row
`D ∂λ ω₁ = λ ω₀ - λ ω₁ + d(2λg/y)` as finite polynomial data. -/
def secondConnectionReduction (parameter : Gaussian) :
    ConnectionReduction parameter where
  parameterDerivativeNumerator := weightedBasePolynomial
  basisConstant := parameter
  basisLinear := -parameter
  primitiveNumerator := secondPrimitivePolynomial parameter
  clearedIdentity := secondConnectionPolynomialIdentity parameter

/-- Numerator of the fraction-free scalar Picard--Fuchs residual over
`y^5`. -/
def picardFuchsResidualNumerator
    (parameter point : Gaussian) : Gaussian :=
  3 * parameter * (1 - parameter) * baseValue point ^ 2 +
    2 * (1 - 2 * parameter) * baseValue point *
      curveValue parameter point - curveValue parameter point ^ 2

/-- The same residual numerator as a literal high-to-low dense polynomial. -/
def picardFuchsResidualPolynomial (parameter : Gaussian) :
    GaussianPolynomial :=
  ⟨[-1, 4 - 2 * parameter, 5 * parameter - 5,
    2 - 4 * parameter, parameter, 0, 0]⟩

@[simp] theorem picardFuchsResidualPolynomial_eval
    (parameter point : Gaussian) :
    (picardFuchsResidualPolynomial parameter).eval point =
      picardFuchsResidualNumerator parameter point := by
  unfold picardFuchsResidualPolynomial picardFuchsResidualNumerator
    baseValue curveValue RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The residual is the spatial derivative of
`2 x^2 (x-1)^2 / y^3`, after clearing the factor `2` introduced by the
half-power derivative. -/
theorem picardFuchsResidual_cleared (parameter point : Gaussian) :
    2 * picardFuchsResidualNumerator parameter point =
      2 * (4 * baseValue point * (2 * point - 1)) *
          curveValue parameter point -
        3 * (2 * baseValue point ^ 2) *
          spatialDerivativeValue parameter point := by
  unfold picardFuchsResidualNumerator baseValue curveValue
    spatialDerivativeValue
  ring1

/-- The full finite symbolic certificate for the scalar equation.  Its
identity is between evaluations of explicit dense polynomials and their
finite automatic derivatives. -/
structure PicardFuchsReduction (parameter : Gaussian) where
  residualNumerator : GaussianPolynomial
  primitiveNumerator : GaussianPolynomial
  clearedIdentity : forall point : Gaussian,
    2 * residualNumerator.eval point =
      2 * (RFAP.ConstructiveGCD.derivative primitiveNumerator).eval point *
          (polynomial parameter).eval point -
        3 * primitiveNumerator.eval point *
          (RFAP.ConstructiveGCD.derivative
            (polynomial parameter)).eval point

/-- The Legendre scalar reduction with no remembered analytic formula: every
field is executable polynomial data and the identity is proved directly. -/
def picardFuchsReduction (parameter : Gaussian) :
    PicardFuchsReduction parameter where
  residualNumerator := picardFuchsResidualPolynomial parameter
  primitiveNumerator := picardFuchsPrimitivePolynomial
  clearedIdentity := by
    intro point
    rw [picardFuchsResidualPolynomial_eval,
      picardFuchsPrimitiveDerivative_eval,
      picardFuchsPrimitivePolynomial_eval, polynomial_eval,
      ← spatialDerivativePolynomial_matches_automatic parameter point,
      spatialDerivativePolynomial_eval]
    exact picardFuchsResidual_cleared parameter point

end CCL.Riemann.LegendrePicardFuchs
