import RationalRotations.AnchorProducts

/-!
# Rational rotations, section 10: three affine-chart breakdowns

This file makes the missing half-turn locus explicit without taking a limit.
The reciprocal-anchor path is stored by the denominator-cleared quadratic
formula, so its value at zero is an ordinary finite field calculation.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- The first breakdown: no defined affine cap can equal a half turn. -/
theorem cap_ne_halfTurn (vector axis : Vector K)
    (defined : capDenominator vector ≠ 0)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    cap vector defined ≠ halfTurn axis axisNonNull := by
  intro equalMatrices
  apply halfSpread_cap_ne_one vector defined twoNonzero
  calc
    halfSpread (capRotation vector defined) =
        halfSpread (halfTurnRotation axis axisNonNull) := by
      unfold halfSpread capRotation halfTurnRotation
      exact congrArg
        (fun matrix => (3 - Matrix3.trace matrix) / 4) equalMatrices
    _ = 1 := halfSpread_halfTurn axis axisNonNull twoNonzero

/-- The finite denominator of the reciprocal-anchor path in Example 53. -/
def reciprocalAnchorPathDenominator (x : K) (axis : Vector K) : K :=
  x ^ 2 + axis.quadrance

/-- The denominator-cleared path
`I + 2 (x A + A²) / (x² + Q(axis))` from Example 53. -/
def reciprocalAnchorPath (x : K) (axis : Vector K)
    (_defined : reciprocalAnchorPathDenominator x axis ≠ 0) : Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (2 / reciprocalAnchorPathDenominator x axis)
      (Matrix3.add
        (Matrix3.scale x (anchor axis))
        (Matrix3.mul (anchor axis) (anchor axis))))

theorem reciprocalAnchorPath_zeroDefined (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    reciprocalAnchorPathDenominator 0 axis ≠ 0 := by
  unfold reciprocalAnchorPathDenominator
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
  exact axisNonNull

/-- On the nonzero chart, the cap denominator is the path denominator times
the square of the reciprocal chart coordinate. -/
theorem capDenominator_inverseScale (x : K) (axis : Vector K)
    (xNonzero : x ≠ 0) :
    capDenominator (Vector.scale x⁻¹ axis) =
      x⁻¹ ^ 2 * reciprocalAnchorPathDenominator x axis := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel x xNonzero
  have reverseCancel : x⁻¹ * x = 1 := by
    calc
      x⁻¹ * x = x * x⁻¹ := by ring1
      _ = 1 := cancel
  have squareCancel : x⁻¹ ^ 2 * x ^ 2 = 1 := by
    calc
      x⁻¹ ^ 2 * x ^ 2 = (x⁻¹ * x) ^ 2 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold capDenominator reciprocalAnchorPathDenominator
  rw [Vector.quadrance_scale]
  calc
    1 + x⁻¹ ^ 2 * axis.quadrance =
        x⁻¹ ^ 2 * x ^ 2 + x⁻¹ ^ 2 * axis.quadrance := by
      rw [squareCancel]
    _ = x⁻¹ ^ 2 * (x ^ 2 + axis.quadrance) := by ring1

theorem reciprocalAnchorCapDefined (x : K) (axis : Vector K)
    (xNonzero : x ≠ 0)
    (pathDefined : reciprocalAnchorPathDenominator x axis ≠ 0) :
    capDenominator (Vector.scale x⁻¹ axis) ≠ 0 := by
  rw [capDenominator_inverseScale x axis xNonzero]
  exact RFAP.ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.inv_ne_zero xNonzero)
        (RFAP.ExplicitField.inv_ne_zero xNonzero))
    pathDefined

/-- For `x ≠ 0`, the denominator-cleared path is exactly the cap of the
reciprocal anchor `x⁻¹ axis`. -/
theorem reciprocalAnchorPath_eq_cap (x : K) (axis : Vector K)
    (xNonzero : x ≠ 0)
    (pathDefined : reciprocalAnchorPathDenominator x axis ≠ 0) :
    reciprocalAnchorPath x axis pathDefined =
      cap (Vector.scale x⁻¹ axis)
        (reciprocalAnchorCapDefined x axis xNonzero pathDefined) := by
  let capD := capDenominator (Vector.scale x⁻¹ axis)
  let pathD := reciprocalAnchorPathDenominator x axis
  have capDValue : capD = x⁻¹ ^ 2 * pathD := by
    exact capDenominator_inverseScale x axis xNonzero
  have capDNonzero : capD ≠ 0 :=
    reciprocalAnchorCapDefined x axis xNonzero pathDefined
  have capDCancel := RFAP.ExplicitField.mul_inv_cancel capD capDNonzero
  have pathDCancel := RFAP.ExplicitField.mul_inv_cancel pathD pathDefined
  have inverseQuadratic : capD⁻¹ * x⁻¹ ^ 2 = pathD⁻¹ := by
    calc
      capD⁻¹ * x⁻¹ ^ 2 =
          capD⁻¹ * x⁻¹ ^ 2 * (pathD * pathD⁻¹) := by
        rw [pathDCancel, mul_one]
      _ = capD⁻¹ * (x⁻¹ ^ 2 * pathD) * pathD⁻¹ := by ring1
      _ = capD⁻¹ * capD * pathD⁻¹ := by rw [← capDValue]
      _ = pathD⁻¹ := by rw [show capD⁻¹ * capD = capD * capD⁻¹ by ring1,
          capDCancel, one_mul]
  have xCancel := RFAP.ExplicitField.mul_inv_cancel x xNonzero
  have reverseCancel : x⁻¹ * x = 1 := by
    calc
      x⁻¹ * x = x * x⁻¹ := by ring1
      _ = 1 := xCancel
  have inverseLinear : capD⁻¹ * x⁻¹ = pathD⁻¹ * x := by
    calc
      capD⁻¹ * x⁻¹ = capD⁻¹ * (x⁻¹ ^ 2 * x) := by
        rw [show x⁻¹ ^ 2 * x = x⁻¹ by
          calc
            x⁻¹ ^ 2 * x = x⁻¹ * (x⁻¹ * x) := by ring1
            _ = x⁻¹ := by rw [reverseCancel, mul_one]]
      _ = (capD⁻¹ * x⁻¹ ^ 2) * x := by ring1
      _ = pathD⁻¹ * x := by rw [inverseQuadratic]
  have linearCoefficient : (2 / capD) * x⁻¹ = (2 / pathD) * x := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * capD⁻¹ * x⁻¹ = 2 * (capD⁻¹ * x⁻¹) := by ring1
      _ = 2 * (pathD⁻¹ * x) := by rw [inverseLinear]
      _ = 2 * pathD⁻¹ * x := by ring1
  have quadraticCoefficient :
      (2 / capD) * (x⁻¹ * x⁻¹) = 2 / pathD := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * capD⁻¹ * (x⁻¹ * x⁻¹) =
          2 * (capD⁻¹ * x⁻¹ ^ 2) := by ring1
      _ = 2 * pathD⁻¹ := by rw [inverseQuadratic]
  symm
  calc
    cap (Vector.scale x⁻¹ axis)
        (reciprocalAnchorCapDefined x axis xNonzero pathDefined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / capD)
          (Matrix3.add
            (Matrix3.scale x⁻¹ (anchor axis))
            (Matrix3.scale (x⁻¹ * x⁻¹)
              (Matrix3.mul (anchor axis) (anchor axis))))) := by
      unfold capD cap
      rw [anchor_scale, Matrix3.mul_scale_left,
        Matrix3.mul_scale_right, Matrix3.scale_scale]
    _ = Matrix3.add Matrix3.identity
        (Matrix3.add
          (Matrix3.scale ((2 / capD) * x⁻¹) (anchor axis))
          (Matrix3.scale ((2 / capD) * (x⁻¹ * x⁻¹))
            (Matrix3.mul (anchor axis) (anchor axis)))) := by
      rw [Matrix3.scale_add, Matrix3.scale_scale, Matrix3.scale_scale]
    _ = Matrix3.add Matrix3.identity
        (Matrix3.add
          (Matrix3.scale ((2 / pathD) * x) (anchor axis))
          (Matrix3.scale (2 / pathD)
            (Matrix3.mul (anchor axis) (anchor axis)))) := by
      rw [linearCoefficient, quadraticCoefficient]
    _ = reciprocalAnchorPath x axis pathDefined := by
      unfold reciprocalAnchorPath pathD
      rw [Matrix3.scale_add, Matrix3.scale_scale]

/-- At zero the same finite formula is the half turn about the axis.  This
is substitution in the field, not a limiting argument. -/
theorem reciprocalAnchorPath_zero (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    reciprocalAnchorPath 0 axis
        (reciprocalAnchorPath_zeroDefined axis axisNonNull) =
      halfTurn axis axisNonNull := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    axis.quadrance axisNonNull
  have denominatorAtZero :
      reciprocalAnchorPathDenominator 0 axis = axis.quadrance := by
    unfold reciprocalAnchorPathDenominator
    ring1
  have expandedCancel :
      (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
        (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ = 1 := by
    simpa only [Vector.quadrance, Vector.dot] using cancel
  unfold reciprocalAnchorPath
  rw [denominatorAtZero]
  ext <;>
    unfold halfTurn reflection <;>
    unfold Matrix3.neg Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity
      Matrix3.outer Matrix3.mul anchor Vector.quadrance Vector.dot <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    (try rw [← expandedCancel]) <;> ring1

namespace ExampleFiftyThree

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def fourth : Vector Scalar := ⟨-2, 2, 1⟩

def axis : Vector Scalar := ⟨15, 21, -2⟩

def displayed : Matrix3 Scalar :=
  ⟨(-22 : Scalar) / 67, 63 / 67, -6 / 67,
    63 / 67, 106 / 335, -42 / 335,
    -6 / 67, -42 / 335, -331 / 335⟩

private theorem natCast_ne_zero {value : Nat} (nonzero : value ≠ 0) :
    (value : Scalar) ≠ 0 := by
  intro castZero
  exact nonzero (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

theorem fourth_quadrance : fourth.quadrance = 9 := by
  unfold fourth Vector.quadrance Vector.dot
  ring1

theorem fourthDefined : capDenominator fourth ≠ 0 := by
  rw [show capDenominator fourth = (10 : Scalar) by
    unfold capDenominator
    rw [fourth_quadrance]
    ring1]
  exact natCast_ne_zero (by decide)

def product : Matrix3 Scalar :=
  Matrix3.mul
    (cap ExampleTwentyFive.vector ExampleTwentyFive.defined)
    (cap fourth fourthDefined)

theorem dot_one : Vector.dot ExampleTwentyFive.vector fourth = 1 := by
  unfold ExampleTwentyFive.vector fourth Vector.dot
  ring1

theorem cross_value :
    Vector.cross ExampleTwentyFive.vector fourth = ⟨-13, -18, 10⟩ := by
  apply Vector.ext <;> decide

theorem numerator_value :
    anchorProductNumerator ExampleTwentyFive.vector fourth = axis := by
  apply Vector.ext <;> decide

theorem product_denominator_zero :
    anchorProductDenominator ExampleTwentyFive.vector fourth = 0 := by
  unfold anchorProductDenominator
  rw [dot_one]
  ring1

theorem axis_quadrance : axis.quadrance = 670 := by
  unfold axis Vector.quadrance Vector.dot
  ring1

theorem axisNonNull : axis.quadrance ≠ 0 := by
  rw [axis_quadrance]
  exact natCast_ne_zero (by decide)

theorem twoNonzero : (2 : Scalar) ≠ 0 := natCast_ne_zero (by decide)

theorem first_halfSpread :
    halfSpread
        (capRotation ExampleTwentyFive.vector ExampleTwentyFive.defined) =
      (66 : Scalar) / 67 := by
  rw [halfSpread_cap ExampleTwentyFive.vector ExampleTwentyFive.defined
      twoNonzero, ExampleTwentyFive.quadrance]
  unfold capDenominator
  rw [ExampleTwentyFive.quadrance]
  rw [show (1 + 66 : Scalar) = 67 by ring1]

theorem fourth_halfSpread :
    halfSpread (capRotation fourth fourthDefined) = (9 : Scalar) / 10 := by
  rw [halfSpread_cap fourth fourthDefined twoNonzero, fourth_quadrance]
  unfold capDenominator
  rw [fourth_quadrance]
  rw [show (1 + 9 : Scalar) = 10 by ring1]

theorem product_halfTurn : product = halfTurn axis axisNonNull := by
  unfold product
  simpa only [numerator_value] using
    cap_mul_cap_eq_halfTurn_of_dot_eq_one
      ExampleTwentyFive.vector fourth ExampleTwentyFive.defined fourthDefined
      dot_one

theorem halfTurn_displayed : halfTurn axis axisNonNull = displayed := by
  have sixtySevenNonzero : (67 : Scalar) ≠ 0 :=
    natCast_ne_zero (by decide)
  have threeThirtyFiveNonzero : (335 : Scalar) ≠ 0 :=
    natCast_ne_zero (by decide)
  have sixSeventyNonzero : (670 : Scalar) ≠ 0 :=
    natCast_ne_zero (by decide)
  have cancel67 := RFAP.ExplicitField.mul_inv_cancel
    (67 : Scalar) sixtySevenNonzero
  have cancel335 := RFAP.ExplicitField.mul_inv_cancel
    (335 : Scalar) threeThirtyFiveNonzero
  have cancel670 := RFAP.ExplicitField.mul_inv_cancel
    (670 : Scalar) sixSeventyNonzero
  have inverse67Candidate :
      (67 : Scalar) * (5 * (335 : Scalar)⁻¹) = 1 := by
    calc
      (67 : Scalar) * (5 * 335⁻¹) = (67 * 5) * 335⁻¹ := by ring1
      _ = 335 * 335⁻¹ := by
        rw [show (67 : Scalar) * 5 = 335 by ring1]
      _ = 1 := cancel335
  have inverse67 : (67 : Scalar)⁻¹ = 5 * (335 : Scalar)⁻¹ := by
    calc
      (67 : Scalar)⁻¹ = 67⁻¹ * 1 := by rw [mul_one]
      _ = 67⁻¹ * (67 * (5 * 335⁻¹)) := by
        rw [inverse67Candidate]
      _ = (67 * 67⁻¹) * (5 * 335⁻¹) := by ring1
      _ = 5 * 335⁻¹ := by rw [cancel67, one_mul]
  have coefficient : (2 : Scalar) / 670 = 1 / 335 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (2 : Scalar) * 670⁻¹ =
          2 * 670⁻¹ * (335 * 335⁻¹) := by
        rw [cancel335, mul_one]
      _ = (2 * 335) * (670⁻¹ * 335⁻¹) := by ring1
      _ = 670 * (670⁻¹ * 335⁻¹) := by
        rw [show (2 : Scalar) * 335 = 670 by ring1]
      _ = (670 * 670⁻¹) * 335⁻¹ := by ring1
      _ = 1 * 335⁻¹ := by rw [cancel670]
  have reverse335 : (335 : Scalar)⁻¹ * 335 = 1 := by
    calc
      (335 : Scalar)⁻¹ * 335 = 335 * 335⁻¹ := by ring1
      _ = 1 := cancel335
  calc
    halfTurn axis axisNonNull =
        Matrix3.add (Matrix3.neg Matrix3.identity)
          (Matrix3.scale (2 / axis.quadrance)
            (Matrix3.outer axis axis)) := by
      apply Matrix3.ext <;> unfold halfTurn reflection Matrix3.neg Matrix3.sub
        Matrix3.add Matrix3.identity Matrix3.scale <;> ring1
    _ = Matrix3.add (Matrix3.neg Matrix3.identity)
          (Matrix3.scale (1 / 335) (Matrix3.outer axis axis)) := by
      rw [axis_quadrance, coefficient]
    _ = Matrix3.scale (1 / 335)
          (Matrix3.sub (Matrix3.outer axis axis)
            (Matrix3.scale 335 Matrix3.identity)) := by
      symm
      calc
        Matrix3.scale (1 / 335)
            (Matrix3.sub (Matrix3.outer axis axis)
              (Matrix3.scale 335 Matrix3.identity)) =
          Matrix3.sub
            (Matrix3.scale (1 / 335) (Matrix3.outer axis axis))
            (Matrix3.scale ((1 / 335) * 335) Matrix3.identity) := by
          apply Matrix3.ext <;> unfold Matrix3.scale Matrix3.sub <;> ring1
        _ = Matrix3.sub
            (Matrix3.scale (1 / 335) (Matrix3.outer axis axis))
            (Matrix3.scale 1 Matrix3.identity) := by
          simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul, reverse335]
        _ = Matrix3.add (Matrix3.neg Matrix3.identity)
            (Matrix3.scale (1 / 335) (Matrix3.outer axis axis)) := by
          rw [Matrix3.one_scale]
          apply Matrix3.ext <;> unfold Matrix3.sub Matrix3.add Matrix3.neg <;>
            ring1
    _ = displayed := by
      apply Matrix3.ext <;> unfold displayed axis Matrix3.sub Matrix3.identity
        Matrix3.scale Matrix3.outer <;>
        simp only [RFAP.ExplicitField.div_eq_mul_inv, inverse67] <;> ring1

theorem product_displayed : product = displayed := by
  rw [product_halfTurn, halfTurn_displayed]

theorem characteristic_polynomial (X : Scalar) :
    Matrix3.characteristicValue product X = (X - 1) * (X + 1) ^ 2 := by
  rw [product_halfTurn]
  calc
    Matrix3.characteristicValue (halfTurn axis axisNonNull) X =
        (X - 1) *
          (X ^ 2 -
            2 * (1 - 2 * halfSpread (halfTurnRotation axis axisNonNull)) * X +
              1) :=
      characteristicValue_rotation (halfTurnRotation axis axisNonNull)
        twoNonzero X
    _ = (X - 1) * (X + 1) ^ 2 := by
      rw [halfSpread_halfTurn axis axisNonNull twoNonzero]
      ring1

theorem path_denominator (x : Scalar) :
    reciprocalAnchorPathDenominator x axis = x ^ 2 + 670 := by
  unfold reciprocalAnchorPathDenominator
  rw [axis_quadrance]

theorem path_at_nonzero (x : Scalar) (xNonzero : x ≠ 0)
    (pathDefined : reciprocalAnchorPathDenominator x axis ≠ 0) :
    reciprocalAnchorPath x axis pathDefined =
      cap (Vector.scale x⁻¹ axis)
        (reciprocalAnchorCapDefined x axis xNonzero pathDefined) :=
  reciprocalAnchorPath_eq_cap x axis xNonzero pathDefined

theorem path_at_zero :
    reciprocalAnchorPath 0 axis
        (reciprocalAnchorPath_zeroDefined axis axisNonNull) = product := by
  rw [reciprocalAnchorPath_zero axis axisNonNull, product_halfTurn]

end ExampleFiftyThree

end RationalRotations
