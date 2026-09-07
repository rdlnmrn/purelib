import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.UnitCircle
import DivineProportions.Trigonometry.TripleTwist

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- Multiplication of finite Gaussian coordinate pairs. -/
def gaussianMul (left right : Point K) : Point K :=
  ⟨left.x * right.x - left.y * right.y,
    left.x * right.y + left.y * right.x⟩

/-- Scalar multiplication of a finite Gaussian coordinate pair. -/
def gaussianScale (scalar : K) (point : Point K) : Point K :=
  ⟨scalar * point.x, scalar * point.y⟩

/-- The Gaussian pair corresponding to `1+i*lambda`. -/
def onePlusIParameter (parameter : K) : Point K :=
  ⟨1, parameter⟩

/-- The source's rational-polar pair `(radius, parameter)`. -/
def rationalPolarPoint (radius parameter : K) : Point K :=
  gaussianScale radius (unitCirclePoint parameter)

/-- Recover the parameter of a non-excluded unit-circle point. -/
def unitCircleParameter (point : Point K) : K :=
  point.y / (1 + point.x)

/-- The imaginary-axis point `i*lambda`. -/
def imaginaryParameterPoint (parameter : K) : Point K :=
  ⟨0, parameter⟩

/-- The displayed imaginary axis `x=0`. -/
def imaginaryAxis [Nontrivial K] : Line K where
  a := 1
  b := 0
  c := 0
  direction_nonzero := Or.inl one_ne_zero

/-- The chord through `[-1,0]` and the point with parameter `lambda`. -/
def unitCircleParameterLine [Nontrivial K] (parameter : K) : Line K where
  a := parameter
  b := -1
  c := parameter
  direction_nonzero := Or.inr (neg_ne_zero.mpr one_ne_zero)

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

/-- Squaring `1+i*lambda` gives the numerator printed in Exercise 16.8. -/
theorem gaussianSquare_onePlusIParameter (parameter : K) :
    gaussianMul (onePlusIParameter parameter)
        (onePlusIParameter parameter) =
      (⟨1 - parameter ^ 2, 2 * parameter⟩ : Point K) := by
  apply Point.ext <;> unfold gaussianMul onePlusIParameter <;>
    dsimp only <;> ring1

/-- Rational polar form is exactly the scaled quotient
`radius*(1+i*lambda)^2/(1+lambda^2)` in finite Gaussian coordinates. -/
theorem rationalPolarPoint_eq_scaled_square (radius parameter : K) :
    rationalPolarPoint radius parameter =
      gaussianScale (radius / (1 + parameter ^ 2))
        (gaussianMul (onePlusIParameter parameter)
          (onePlusIParameter parameter)) := by
  apply Point.ext <;>
    unfold rationalPolarPoint unitCirclePoint gaussianScale gaussianMul
      onePlusIParameter <;>
    dsimp only <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

private theorem unitCirclePoint_parameter_equation
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (unitCirclePoint parameter).y =
      parameter * (1 + (unitCirclePoint parameter).x) := by
  let denominator := 1 + parameter ^ 2
  have denominatorNonzero : denominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have realCancel :
      ((1 - parameter ^ 2) / denominator) * denominator =
        1 - parameter ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel
      (1 - parameter ^ 2) denominatorNonzero
  have imaginaryCancel :
      ((2 * parameter) / denominator) * denominator = 2 * parameter :=
    RFAP.ExplicitField.div_mul_cancel
      (2 * parameter) denominatorNonzero
  apply eq_of_mul_eq_mul_right denominatorNonzero
  change ((2 * parameter) / denominator) * denominator =
    (parameter * (1 + (1 - parameter ^ 2) / denominator)) * denominator
  calc
    ((2 * parameter) / denominator) * denominator =
        2 * parameter := imaginaryCancel
    _ = parameter *
        (denominator + (1 - parameter ^ 2)) := by
      unfold denominator
      ring1
    _ = parameter *
        (((1 - parameter ^ 2) / denominator) * denominator +
          denominator) := by rw [realCancel]; ring1
    _ = (parameter *
        (1 + (1 - parameter ^ 2) / denominator)) * denominator := by ring1

private theorem unitCirclePoint_one_plus_x_times_denominator
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (1 + (unitCirclePoint parameter).x) * (1 + parameter ^ 2) = 2 := by
  have denominatorNonzero : 1 + parameter ^ 2 ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff parameter).2
      squareNotNegativeOne
  have realCancel :
      ((1 - parameter ^ 2) / (1 + parameter ^ 2)) *
          (1 + parameter ^ 2) = 1 - parameter ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel
      (1 - parameter ^ 2) denominatorNonzero
  change (1 + (1 - parameter ^ 2) / (1 + parameter ^ 2)) *
    (1 + parameter ^ 2) = 2
  calc
    (1 + (1 - parameter ^ 2) / (1 + parameter ^ 2)) *
        (1 + parameter ^ 2) =
      (1 + parameter ^ 2) +
        ((1 - parameter ^ 2) / (1 + parameter ^ 2)) *
          (1 + parameter ^ 2) := by ring1
    _ = 2 := by rw [realCancel]; ring1

/-- The finite quotient `y/(1+x)` recovers an admissible unit-circle
parameter. -/
theorem unitCircleParameter_unitCirclePoint
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    unitCircleParameter (unitCirclePoint parameter) = parameter := by
  have onePlusXNonzero : 1 + (unitCirclePoint parameter).x ≠ 0 := by
    intro onePlusXZero
    apply twoNonzero
    calc
      (2 : K) =
          (1 + (unitCirclePoint parameter).x) *
            (1 + parameter ^ 2) :=
        (unitCirclePoint_one_plus_x_times_denominator parameter
          squareNotNegativeOne).symm
      _ = 0 := by rw [onePlusXZero]; ring1
  apply eq_of_mul_eq_mul_right onePlusXNonzero
  calc
    unitCircleParameter (unitCirclePoint parameter) *
        (1 + (unitCirclePoint parameter).x) =
      (unitCirclePoint parameter).y :=
        RFAP.ExplicitField.div_mul_cancel _ onePlusXNonzero
    _ = parameter * (1 + (unitCirclePoint parameter).x) :=
      unitCirclePoint_parameter_equation parameter squareNotNegativeOne

/-- Admissible parameters give distinct unit-circle points outside the
excluded point `[-1,0]`. -/
theorem unitCirclePoint_ne_excluded
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    unitCirclePoint parameter ≠ unitCircleExcludedPoint := by
  intro pointEqual
  have xEqual := congrArg Point.x pointEqual
  change (unitCirclePoint parameter).x = -1 at xEqual
  have onePlusXZero : 1 + (unitCirclePoint parameter).x = 0 := by
    rw [xEqual]
    ring1
  apply twoNonzero
  calc
    (2 : K) =
        (1 + (unitCirclePoint parameter).x) * (1 + parameter ^ 2) :=
      (unitCirclePoint_one_plus_x_times_denominator parameter
        squareNotNegativeOne).symm
    _ = 0 := by rw [onePlusXZero]; ring1

/-- The unit-circle chart is injective on its admissible parameters. -/
theorem unitCirclePoint_injective
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0)
    (pointsEqual : unitCirclePoint left = unitCirclePoint right) :
    left = right := by
  calc
    left = unitCircleParameter (unitCirclePoint left) :=
      (unitCircleParameter_unitCirclePoint left
        leftSquareNotNegativeOne twoNonzero).symm
    _ = unitCircleParameter (unitCirclePoint right) := by rw [pointsEqual]
    _ = right := unitCircleParameter_unitCirclePoint right
      rightSquareNotNegativeOne twoNonzero

/-- Every non-excluded unit-circle point has exactly one admissible rational
parameter. -/
theorem unitCirclePoint_existsUnique [Nontrivial K] [DecidableEq K]
    (point : Point K) (twoNonzero : (2 : K) ≠ 0)
    (pointOnCircle : unitCircle.Contains point)
    (pointNotExcluded : point ≠ unitCircleExcludedPoint) :
    ∃! parameter : K,
      parameter ^ 2 ≠ -1 ∧ point = unitCirclePoint parameter := by
  rcases unitCirclePoint_exists point twoNonzero pointOnCircle
      pointNotExcluded with
    ⟨parameter, squareNotNegativeOne, pointFormula⟩
  refine ⟨parameter, ⟨squareNotNegativeOne, pointFormula⟩, ?_⟩
  intro other otherFormula
  exact (unitCirclePoint_injective parameter other squareNotNegativeOne
    otherFormula.1 twoNonzero (pointFormula.symm.trans otherFormula.2)).symm

/-- The parameter chord contains the excluded unit-circle point. -/
theorem unitCircleParameterLine_contains_excluded [Nontrivial K]
    (parameter : K) :
    (unitCircleParameterLine parameter).Contains
      unitCircleExcludedPoint := by
  unfold unitCircleParameterLine unitCircleExcludedPoint Line.Contains
  dsimp only
  ring1

/-- The parameter chord contains its parametrized unit-circle point. -/
theorem unitCircleParameterLine_contains_point [Nontrivial K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1) :
    (unitCircleParameterLine parameter).Contains
      (unitCirclePoint parameter) := by
  have parameterEquation := unitCirclePoint_parameter_equation parameter
    squareNotNegativeOne
  unfold unitCircleParameterLine Line.Contains
  dsimp only
  rw [parameterEquation]
  ring1

/-- The explicit parameter chord is the line through `[-1,0]` and the
parametrized unit-circle point, up to quotient-free line equivalence. -/
theorem unitCircleParameterLine_equivalent_lineThrough [Nontrivial K]
    [DecidableEq K]
    (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    (lineThrough unitCircleExcludedPoint (unitCirclePoint parameter)
      (Ne.symm (unitCirclePoint_ne_excluded parameter
        squareNotNegativeOne twoNonzero))).Equivalent
      (unitCircleParameterLine parameter) := by
  apply lineThrough_unique unitCircleExcludedPoint
    (unitCirclePoint parameter)
    (Ne.symm (unitCirclePoint_ne_excluded parameter
      squareNotNegativeOne twoNonzero))
  · exact unitCircleParameterLine_contains_excluded parameter
  · exact unitCircleParameterLine_contains_point parameter
      squareNotNegativeOne

/-- The point `i*lambda` lies on the imaginary axis. -/
theorem imaginaryAxis_contains_parameter [Nontrivial K]
    (parameter : K) :
    imaginaryAxis.Contains (imaginaryParameterPoint parameter) := by
  unfold imaginaryAxis imaginaryParameterPoint Line.Contains
  dsimp only
  ring1

/-- The point `i*lambda` lies on the corresponding parameter chord. -/
theorem unitCircleParameterLine_contains_imaginary [Nontrivial K]
    (parameter : K) :
    (unitCircleParameterLine parameter).Contains
      (imaginaryParameterPoint parameter) := by
  unfold unitCircleParameterLine imaginaryParameterPoint Line.Contains
  dsimp only
  ring1

/-- The imaginary axis and any parameter chord are nonparallel. -/
theorem imaginaryAxis_parameterLine_nonparallel [Nontrivial K]
    (parameter : K) :
    ¬ imaginaryAxis.Parallel (unitCircleParameterLine parameter) := by
  unfold imaginaryAxis unitCircleParameterLine Line.Parallel
  dsimp only
  intro negativeOneZero
  apply (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
  calc
    (-1 : K) = 1 * -1 - parameter * 0 := by ring1
    _ = 0 := negativeOneZero

/-- The book's point `i*lambda` is the unique intersection of the imaginary
axis and the chord through `-1` and the parametrized unit-circle point. -/
theorem imaginaryParameterPoint_is_intersection [Nontrivial K]
    (parameter : K) :
    imaginaryParameterPoint parameter =
      lineIntersection imaginaryAxis (unitCircleParameterLine parameter)
        (imaginaryAxis_parameterLine_nonparallel parameter) := by
  exact lineIntersection_unique imaginaryAxis
    (unitCircleParameterLine parameter)
    (imaginaryAxis_parameterLine_nonparallel parameter)
    (imaginaryParameterPoint parameter)
    (imaginaryAxis_contains_parameter parameter)
    (unitCircleParameterLine_contains_imaginary parameter)

/-- Gaussian multiplication commutes with two displayed scalar factors. -/
theorem gaussianMul_scale_scale
    (leftScalar rightScalar : K) (left right : Point K) :
    gaussianMul (gaussianScale leftScalar left)
        (gaussianScale rightScalar right) =
      gaussianScale (leftScalar * rightScalar) (gaussianMul left right) := by
  apply Point.ext <;> unfold gaussianMul gaussianScale <;>
    dsimp only <;> ring1

/-- Two successive Gaussian scalings multiply their scalar factors. -/
theorem gaussianScale_scale (first second : K) (point : Point K) :
    gaussianScale first (gaussianScale second point) =
      gaussianScale (first * second) point := by
  apply Point.ext <;> unfold gaussianScale <;> dsimp only <;> ring1

/-- The product of two Gaussian squares is the square of the product. -/
theorem gaussianMul_squares (left right : Point K) :
    gaussianMul (gaussianMul left left) (gaussianMul right right) =
      gaussianMul (gaussianMul left right) (gaussianMul left right) := by
  apply Point.ext <;> unfold gaussianMul <;> dsimp only <;> ring1

/-- Multiplying `1+i*left` and `1+i*right` exposes the numerator and
denominator of the rational turn-composition parameter. -/
theorem gaussianMul_onePlusIParameter (left right : K) :
    gaussianMul (onePlusIParameter left) (onePlusIParameter right) =
      (⟨1 - left * right, left + right⟩ : Point K) := by
  apply Point.ext <;> unfold gaussianMul onePlusIParameter <;>
    dsimp only <;> ring1

/-- When the turn-composition denominator is nonzero, the product
`(1+i*left)(1+i*right)` is that denominator times the next chart factor. -/
theorem gaussianMul_onePlusIParameter_eq_scale
    (left right : K) (compositionDenominatorNonzero :
      1 - left * right ≠ 0) :
    gaussianMul (onePlusIParameter left) (onePlusIParameter right) =
      gaussianScale (1 - left * right)
        (onePlusIParameter (turnComposition left right)) := by
  have compositionCancel :
      turnComposition left right * (1 - left * right) = left + right := by
    unfold turnComposition
    exact RFAP.ExplicitField.div_mul_cancel (left + right)
      compositionDenominatorNonzero
  apply Point.ext
  · unfold gaussianMul gaussianScale onePlusIParameter
    dsimp only
    ring1
  · unfold gaussianMul gaussianScale onePlusIParameter
    dsimp only
    calc
      1 * right + left * 1 = left + right := by ring1
      _ =
          turnComposition left right * (1 - left * right) :=
        compositionCancel.symm
      _ = (1 - left * right) * turnComposition left right := by ring1

/-- The turn-composition parameter remains admissible whenever both input
unit points and the composition denominator are admissible. -/
theorem turnComposition_square_ne_negative_one
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (compositionDenominatorNonzero : 1 - left * right ≠ 0) :
    turnComposition left right ^ 2 ≠ -1 := by
  let leftDenominator := 1 + left ^ 2
  let rightDenominator := 1 + right ^ 2
  let compositionDenominator := 1 - left * right
  let compositionNumerator := left + right
  let composed := turnComposition left right
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have inputProductNonzero : leftDenominator * rightDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero leftDenominatorNonzero
      rightDenominatorNonzero
  have composedCancel : composed * compositionDenominator =
      compositionNumerator := by
    exact RFAP.ExplicitField.div_mul_cancel compositionNumerator
      compositionDenominatorNonzero
  have denominatorIdentity :
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
        leftDenominator * rightDenominator := by
    calc
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
          compositionDenominator ^ 2 +
            (composed * compositionDenominator) ^ 2 := by ring1
      _ = compositionDenominator ^ 2 + compositionNumerator ^ 2 := by
        rw [composedCancel]
      _ = leftDenominator * rightDenominator := by
        unfold leftDenominator rightDenominator compositionDenominator
          compositionNumerator
        ring1
  apply (projectiveParameter_denominator_ne_zero_iff composed).1
  intro composedDenominatorZero
  apply inputProductNonzero
  calc
    leftDenominator * rightDenominator =
        (1 + composed ^ 2) * compositionDenominator ^ 2 :=
      denominatorIdentity.symm
    _ = 0 := by rw [composedDenominatorZero]; ring1

/-- The omitted denominator case has an exact geometric meaning: the product
of the two admissible unit points is the chart's excluded point `[-1,0]`. -/
theorem gaussianMul_unitCirclePoint_eq_excluded
    (left right : K)
    (leftSquareNotNegativeOne : left ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : right ^ 2 ≠ -1)
    (compositionDenominatorZero : 1 - left * right = 0) :
    gaussianMul (unitCirclePoint left) (unitCirclePoint right) =
      unitCircleExcludedPoint := by
  let leftDenominator := 1 + left ^ 2
  let rightDenominator := 1 + right ^ 2
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff left).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff right).2
      rightSquareNotNegativeOne
  have denominatorProductNonzero :
      leftDenominator * rightDenominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero leftDenominatorNonzero
      rightDenominatorNonzero
  have leftRealCancel :
      ((1 - left ^ 2) / leftDenominator) * leftDenominator =
        1 - left ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have leftImaginaryCancel :
      ((2 * left) / leftDenominator) * leftDenominator = 2 * left :=
    RFAP.ExplicitField.div_mul_cancel _ leftDenominatorNonzero
  have rightRealCancel :
      ((1 - right ^ 2) / rightDenominator) * rightDenominator =
        1 - right ^ 2 :=
    RFAP.ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have rightImaginaryCancel :
      ((2 * right) / rightDenominator) * rightDenominator = 2 * right :=
    RFAP.ExplicitField.div_mul_cancel _ rightDenominatorNonzero
  have realNumerator :
      (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) =
        -(leftDenominator * rightDenominator) := by
    calc
      (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) =
        -(leftDenominator * rightDenominator) +
          2 * (1 - left * right) ^ 2 := by
            unfold leftDenominator rightDenominator
            ring1
      _ = -(leftDenominator * rightDenominator) := by
        rw [compositionDenominatorZero]
        ring1
  have imaginaryNumerator :
      (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) = 0 := by
    calc
      (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) =
        2 * (left + right) * (1 - left * right) := by ring1
      _ = 0 := by rw [compositionDenominatorZero]; ring1
  apply Point.ext
  · apply eq_of_mul_eq_mul_right denominatorProductNonzero
    change
      (((1 - left ^ 2) / leftDenominator) *
          ((1 - right ^ 2) / rightDenominator) -
        ((2 * left) / leftDenominator) *
          ((2 * right) / rightDenominator)) *
          (leftDenominator * rightDenominator) =
        (-1 : K) * (leftDenominator * rightDenominator)
    calc
      (((1 - left ^ 2) / leftDenominator) *
            ((1 - right ^ 2) / rightDenominator) -
          ((2 * left) / leftDenominator) *
            ((2 * right) / rightDenominator)) *
            (leftDenominator * rightDenominator) =
        (((1 - left ^ 2) / leftDenominator) * leftDenominator) *
            (((1 - right ^ 2) / rightDenominator) * rightDenominator) -
          (((2 * left) / leftDenominator) * leftDenominator) *
            (((2 * right) / rightDenominator) * rightDenominator) := by ring1
      _ = (1 - left ^ 2) * (1 - right ^ 2) -
          (2 * left) * (2 * right) := by
        rw [leftRealCancel, rightRealCancel, leftImaginaryCancel,
          rightImaginaryCancel]
      _ = -(leftDenominator * rightDenominator) := realNumerator
      _ = (-1 : K) * (leftDenominator * rightDenominator) := by ring1
  · apply eq_of_mul_eq_mul_right denominatorProductNonzero
    change
      (((1 - left ^ 2) / leftDenominator) *
          ((2 * right) / rightDenominator) +
        ((2 * left) / leftDenominator) *
          ((1 - right ^ 2) / rightDenominator)) *
          (leftDenominator * rightDenominator) =
        (0 : K) * (leftDenominator * rightDenominator)
    calc
      (((1 - left ^ 2) / leftDenominator) *
            ((2 * right) / rightDenominator) +
          ((2 * left) / leftDenominator) *
            ((1 - right ^ 2) / rightDenominator)) *
            (leftDenominator * rightDenominator) =
        (((1 - left ^ 2) / leftDenominator) * leftDenominator) *
            (((2 * right) / rightDenominator) * rightDenominator) +
          (((2 * left) / leftDenominator) * leftDenominator) *
            (((1 - right ^ 2) / rightDenominator) * rightDenominator) := by
          ring1
      _ = (1 - left ^ 2) * (2 * right) +
          (2 * left) * (1 - right ^ 2) := by
        rw [leftRealCancel, rightImaginaryCancel, leftImaginaryCancel,
          rightRealCancel]
      _ = 0 := imaginaryNumerator
      _ = (0 : K) * (leftDenominator * rightDenominator) := by ring1

/-- Exercise 16.8's rational-polar multiplication formula.  All objects are
finite Gaussian pairs, and every denominator used for cancellation is carried
as a premise or derived certificate. -/
theorem rationalPolarPoint_mul
    (leftRadius rightRadius leftParameter rightParameter : K)
    (leftSquareNotNegativeOne : leftParameter ^ 2 ≠ -1)
    (rightSquareNotNegativeOne : rightParameter ^ 2 ≠ -1)
    (compositionDenominatorNonzero :
      1 - leftParameter * rightParameter ≠ 0) :
    let composed := turnComposition leftParameter rightParameter
    composed ^ 2 ≠ -1 ∧
      gaussianMul
          (rationalPolarPoint leftRadius leftParameter)
          (rationalPolarPoint rightRadius rightParameter) =
        rationalPolarPoint (leftRadius * rightRadius) composed := by
  dsimp only
  let leftDenominator := 1 + leftParameter ^ 2
  let rightDenominator := 1 + rightParameter ^ 2
  let compositionDenominator := 1 - leftParameter * rightParameter
  let composed := turnComposition leftParameter rightParameter
  have leftDenominatorNonzero : leftDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff leftParameter).2
      leftSquareNotNegativeOne
  have rightDenominatorNonzero : rightDenominator ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff rightParameter).2
      rightSquareNotNegativeOne
  have composedSquareNotNegativeOne : composed ^ 2 ≠ -1 :=
    turnComposition_square_ne_negative_one leftParameter rightParameter
      leftSquareNotNegativeOne rightSquareNotNegativeOne
      compositionDenominatorNonzero
  have composedDenominatorNonzero : 1 + composed ^ 2 ≠ 0 :=
    (projectiveParameter_denominator_ne_zero_iff composed).2
      composedSquareNotNegativeOne
  have leftCancel :
      (leftRadius / leftDenominator) * leftDenominator = leftRadius :=
    RFAP.ExplicitField.div_mul_cancel leftRadius leftDenominatorNonzero
  have rightCancel :
      (rightRadius / rightDenominator) * rightDenominator = rightRadius :=
    RFAP.ExplicitField.div_mul_cancel rightRadius rightDenominatorNonzero
  have compositionCancel :
      composed * compositionDenominator =
        leftParameter + rightParameter := by
    exact RFAP.ExplicitField.div_mul_cancel
      (leftParameter + rightParameter) compositionDenominatorNonzero
  have denominatorIdentity :
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
        leftDenominator * rightDenominator := by
    calc
      (1 + composed ^ 2) * compositionDenominator ^ 2 =
          compositionDenominator ^ 2 +
            (composed * compositionDenominator) ^ 2 := by ring1
      _ = compositionDenominator ^ 2 +
          (leftParameter + rightParameter) ^ 2 := by rw [compositionCancel]
      _ = leftDenominator * rightDenominator := by
        unfold leftDenominator rightDenominator compositionDenominator
        ring1
  have scalarEquality :
      (leftRadius / leftDenominator) *
          (rightRadius / rightDenominator) *
          compositionDenominator ^ 2 =
        (leftRadius * rightRadius) / (1 + composed ^ 2) := by
    apply eq_of_mul_eq_mul_right composedDenominatorNonzero
    calc
      ((leftRadius / leftDenominator) *
            (rightRadius / rightDenominator) *
            compositionDenominator ^ 2) * (1 + composed ^ 2) =
          (leftRadius / leftDenominator) *
            (rightRadius / rightDenominator) *
            (leftDenominator * rightDenominator) := by
        rw [← denominatorIdentity]
        ring1
      _ = ((leftRadius / leftDenominator) * leftDenominator) *
          ((rightRadius / rightDenominator) * rightDenominator) := by ring1
      _ = leftRadius * rightRadius := by rw [leftCancel, rightCancel]
      _ = ((leftRadius * rightRadius) / (1 + composed ^ 2)) *
          (1 + composed ^ 2) :=
        (RFAP.ExplicitField.div_mul_cancel
          (leftRadius * rightRadius) composedDenominatorNonzero).symm
  refine ⟨composedSquareNotNegativeOne, ?_⟩
  rw [rationalPolarPoint_eq_scaled_square,
    rationalPolarPoint_eq_scaled_square,
    rationalPolarPoint_eq_scaled_square]
  change gaussianMul
      (gaussianScale (leftRadius / leftDenominator)
        (gaussianMul (onePlusIParameter leftParameter)
          (onePlusIParameter leftParameter)))
      (gaussianScale (rightRadius / rightDenominator)
        (gaussianMul (onePlusIParameter rightParameter)
          (onePlusIParameter rightParameter))) =
    gaussianScale ((leftRadius * rightRadius) / (1 + composed ^ 2))
      (gaussianMul (onePlusIParameter composed)
        (onePlusIParameter composed))
  calc
    gaussianMul
        (gaussianScale (leftRadius / leftDenominator)
          (gaussianMul (onePlusIParameter leftParameter)
            (onePlusIParameter leftParameter)))
        (gaussianScale (rightRadius / rightDenominator)
          (gaussianMul (onePlusIParameter rightParameter)
            (onePlusIParameter rightParameter))) =
      gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (gaussianMul
          (gaussianMul (onePlusIParameter leftParameter)
            (onePlusIParameter leftParameter))
          (gaussianMul (onePlusIParameter rightParameter)
            (onePlusIParameter rightParameter))) :=
      gaussianMul_scale_scale _ _ _ _
    _ = gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (gaussianMul
          (gaussianMul (onePlusIParameter leftParameter)
            (onePlusIParameter rightParameter))
          (gaussianMul (onePlusIParameter leftParameter)
            (onePlusIParameter rightParameter))) := by
      rw [gaussianMul_squares]
    _ = gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (gaussianMul
          (gaussianScale compositionDenominator
            (onePlusIParameter composed))
          (gaussianScale compositionDenominator
            (onePlusIParameter composed))) := by
      rw [gaussianMul_onePlusIParameter_eq_scale leftParameter
        rightParameter compositionDenominatorNonzero]
    _ = gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator))
        (gaussianScale (compositionDenominator * compositionDenominator)
          (gaussianMul (onePlusIParameter composed)
            (onePlusIParameter composed))) := by
      rw [gaussianMul_scale_scale]
    _ = gaussianScale
        ((leftRadius / leftDenominator) *
          (rightRadius / rightDenominator) *
          compositionDenominator ^ 2)
        (gaussianMul (onePlusIParameter composed)
          (onePlusIParameter composed)) := by
      rw [gaussianScale_scale]
      congr 1
      ring1
    _ = gaussianScale ((leftRadius * rightRadius) / (1 + composed ^ 2))
        (gaussianMul (onePlusIParameter composed)
          (onePlusIParameter composed)) := by rw [scalarEquality]

/-- Exercise 16.8, packaged as unique parametrization, chord intersection,
and rational-polar multiplication using precisely the turn law from Exercise
9.2. -/
theorem exercise_16_8 [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (∀ point : Point K,
      unitCircle.Contains point → point ≠ unitCircleExcludedPoint →
        ∃! parameter : K,
          parameter ^ 2 ≠ -1 ∧ point = unitCirclePoint parameter) ∧
    (∀ parameter : K, parameter ^ 2 ≠ -1 →
      unitCircle.Contains (unitCirclePoint parameter)) ∧
    (∀ (parameter : K) (squareNotNegativeOne : parameter ^ 2 ≠ -1),
      (lineThrough unitCircleExcludedPoint (unitCirclePoint parameter)
          (Ne.symm (unitCirclePoint_ne_excluded parameter
            squareNotNegativeOne twoNonzero))).Equivalent
            (unitCircleParameterLine parameter) ∧
        imaginaryParameterPoint parameter =
          lineIntersection imaginaryAxis (unitCircleParameterLine parameter)
            (imaginaryAxis_parameterLine_nonparallel parameter)) ∧
    (∀ (leftRadius rightRadius leftParameter rightParameter : K),
      leftParameter ^ 2 ≠ -1 → rightParameter ^ 2 ≠ -1 →
      1 - leftParameter * rightParameter ≠ 0 →
      let composed := turnComposition leftParameter rightParameter
      composed ^ 2 ≠ -1 ∧
        gaussianMul
            (rationalPolarPoint leftRadius leftParameter)
            (rationalPolarPoint rightRadius rightParameter) =
          rationalPolarPoint (leftRadius * rightRadius) composed) := by
  refine ⟨?_, unitCirclePoint_contains, ?_, rationalPolarPoint_mul⟩
  · intro point pointOnCircle pointNotExcluded
    exact unitCirclePoint_existsUnique point twoNonzero pointOnCircle
      pointNotExcluded
  · intro parameter squareNotNegativeOne
    exact ⟨unitCircleParameterLine_equivalent_lineThrough parameter
      squareNotNegativeOne twoNonzero,
      imaginaryParameterPoint_is_intersection parameter⟩

end Conic

end DivineProportions
