import RationalRotations.AnchorProducts

/-!
# Conjecture 52: coefficient anchor products

The coefficient family is represented homogeneously with a constant and a
dot-product denominator coefficient.  Global nonzero rescaling of all five
coefficients leaves the same rational operation.  This exposes a missing
nondegeneracy hypothesis in Conjecture 52: the left projection belongs to
the displayed family and is associative, but is not the anchor product or
its opposite.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- Homogeneous coefficients for
`(αv+βu+γ(v×u))/(ε+δ(v·u))`. -/
@[ext]
structure CoefficientProductParameters (K : Type*) where
  leftCoefficient : K
  rightCoefficient : K
  crossCoefficient : K
  constantCoefficient : K
  dotCoefficient : K

namespace CoefficientProductParameters

def numerator (parameters : CoefficientProductParameters K)
    (left right : Vector K) : Vector K :=
  Vector.add
    (Vector.add (Vector.scale parameters.leftCoefficient left)
      (Vector.scale parameters.rightCoefficient right))
    (Vector.scale parameters.crossCoefficient (Vector.cross left right))

def denominator (parameters : CoefficientProductParameters K)
    (left right : Vector K) : K :=
  parameters.constantCoefficient +
    parameters.dotCoefficient * Vector.dot left right

/-- The partial coefficient product on its displayed affine domain. -/
def product (parameters : CoefficientProductParameters K)
    (left right : Vector K) (_defined : parameters.denominator left right ≠ 0) :
    Vector K :=
  Vector.scale (1 / parameters.denominator left right)
    (parameters.numerator left right)

theorem denominator_zero_right
    (parameters : CoefficientProductParameters K) (vector : Vector K) :
    parameters.denominator vector Vector.zero =
      parameters.constantCoefficient := by
  unfold denominator
  rw [Vector.dot_zero_right]
  ring1

theorem denominator_zero_left
    (parameters : CoefficientProductParameters K) (vector : Vector K) :
    parameters.denominator Vector.zero vector =
      parameters.constantCoefficient := by
  unfold denominator
  rw [Vector.dot_zero_left]
  ring1

/-- Compatibility with the anchor chart's identity: the constant denominator
is explicitly nonzero, and the displayed zero vector is a two-sided identity.
The nonzero certificate makes both identity products executable data. -/
structure HasZeroIdentity (parameters : CoefficientProductParameters K) : Prop where
  constantNonzero : parameters.constantCoefficient ≠ 0
  rightIdentity : ∀ vector : Vector K,
    parameters.product vector Vector.zero
      (by rwa [parameters.denominator_zero_right vector]) = vector
  leftIdentity : ∀ vector : Vector K,
    parameters.product Vector.zero vector
      (by rwa [parameters.denominator_zero_left vector]) = vector

theorem leftCoefficient_eq_constant
    (parameters : CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity) :
    parameters.leftCoefficient = parameters.constantCoefficient := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  have coordinate := congrArg Vector.t (identity.rightIdentity basisT)
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  dsimp only [product, numerator, denominator, basisT, Vector.scale, Vector.add,
    Vector.cross, Vector.zero] at coordinate
  have coordinate' : parameters.constantCoefficient⁻¹ *
      parameters.leftCoefficient = 1 := by
    simpa only [Vector.dot, RFAP.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self] using coordinate
  calc
    parameters.leftCoefficient =
        (parameters.constantCoefficient *
          parameters.constantCoefficient⁻¹) * parameters.leftCoefficient := by
      rw [cancel, one_mul]
    _ = parameters.constantCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.leftCoefficient) := by ring1
    _ = parameters.constantCoefficient := by rw [coordinate', mul_one]

theorem rightCoefficient_eq_constant
    (parameters : CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity) :
    parameters.rightCoefficient = parameters.constantCoefficient := by
  let basisT : Vector K := ⟨1, 0, 0⟩
  have coordinate := congrArg Vector.t (identity.leftIdentity basisT)
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  dsimp only [product, numerator, denominator, basisT, Vector.scale, Vector.add,
    Vector.cross, Vector.zero] at coordinate
  have coordinate' : parameters.constantCoefficient⁻¹ *
      parameters.rightCoefficient = 1 := by
    simpa only [Vector.dot, RFAP.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self] using coordinate
  calc
    parameters.rightCoefficient =
        (parameters.constantCoefficient *
          parameters.constantCoefficient⁻¹) * parameters.rightCoefficient := by
      rw [cancel, one_mul]
    _ = parameters.constantCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.rightCoefficient) := by ring1
    _ = parameters.constantCoefficient := by rw [coordinate', mul_one]

/-- Associativity wherever all four products in the two bracketings are
defined. -/
def AssociativeWhereDefined
    (parameters : CoefficientProductParameters K) : Prop :=
  ∀ (first second third : Vector K)
    (firstSecondDefined : parameters.denominator first second ≠ 0)
    (secondThirdDefined : parameters.denominator second third ≠ 0)
    (leftDefined : parameters.denominator
      (parameters.product first second firstSecondDefined) third ≠ 0)
    (rightDefined : parameters.denominator first
      (parameters.product second third secondThirdDefined) ≠ 0),
    parameters.product
        (parameters.product first second firstSecondDefined) third leftDefined =
      parameters.product first
        (parameters.product second third secondThirdDefined) rightDefined

/-- A single displayed scalar probe makes the unital associativity
classification finite over any explicit field.  Over the rationals one can
use `1`, except in the sole case where that denominator vanishes, and then
use `2`. -/
theorem constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
    (parameters : CoefficientProductParameters K)
    (identity : parameters.HasZeroIdentity)
    (associative : parameters.AssociativeWhereDefined)
    (probe : K) (probeNonzero : probe ≠ 0)
    (probeDefined : parameters.constantCoefficient +
      parameters.dotCoefficient * probe ^ 2 ≠ 0) :
    parameters.constantCoefficient * parameters.dotCoefficient =
      -(parameters.crossCoefficient ^ 2) := by
  let first : Vector K := ⟨probe, 0, 0⟩
  let third : Vector K := ⟨0, 1, 0⟩
  have leftCoefficient := parameters.leftCoefficient_eq_constant identity
  have rightCoefficient := parameters.rightCoefficient_eq_constant identity
  have constantCancel := RFAP.ExplicitField.mul_inv_cancel
    parameters.constantCoefficient identity.constantNonzero
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := constantCancel
  have firstSecondDenominator :
      parameters.denominator first first =
        parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2 := by
    unfold denominator first Vector.dot
    ring1
  let firstSecondDefined : parameters.denominator first first ≠ 0 := by
    rwa [firstSecondDenominator]
  have secondThirdDenominator :
      parameters.denominator first third =
        parameters.constantCoefficient := by
    unfold denominator first third Vector.dot
    ring1
  let secondThirdDefined : parameters.denominator first third ≠ 0 := by
    rw [secondThirdDenominator]
    exact identity.constantNonzero
  have firstSecondProduct :
      parameters.product first first firstSecondDefined =
        ⟨(parameters.constantCoefficient +
            parameters.dotCoefficient * probe ^ 2)⁻¹ *
              (2 * parameters.constantCoefficient * probe), 0, 0⟩ := by
    unfold product
    rw [firstSecondDenominator]
    apply Vector.ext <;>
      unfold numerator first Vector.scale Vector.add Vector.cross <;>
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, sub_self]
    all_goals ring1
  have secondThirdProduct :
      parameters.product first third secondThirdDefined =
        ⟨probe, 1,
          parameters.constantCoefficient⁻¹ *
            parameters.crossCoefficient * probe⟩ := by
    unfold product
    rw [secondThirdDenominator]
    apply Vector.ext
    · unfold numerator first third Vector.scale Vector.add Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero,
        add_zero, sub_self]
      rw [← mul_assoc, constantReverseCancel, one_mul]
    · unfold numerator first third Vector.scale Vector.add Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        mul_one, add_zero, zero_add, sub_self]
      exact constantReverseCancel
    · unfold numerator first third Vector.scale Vector.add Vector.cross
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero,
        add_zero]
      rw [sub_zero]
      ring1
  have leftOuterDenominator :
      parameters.denominator
          (parameters.product first first firstSecondDefined) third =
        parameters.constantCoefficient := by
    rw [firstSecondProduct]
    unfold denominator third Vector.dot
    ring1
  let leftDefined : parameters.denominator
      (parameters.product first first firstSecondDefined) third ≠ 0 := by
    rw [leftOuterDenominator]
    exact identity.constantNonzero
  have rightOuterDenominator :
      parameters.denominator first
          (parameters.product first third secondThirdDefined) =
        parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2 := by
    rw [secondThirdProduct]
    unfold denominator first Vector.dot
    ring1
  let rightDefined : parameters.denominator first
      (parameters.product first third secondThirdDefined) ≠ 0 := by
    rwa [rightOuterDenominator]
  have association := associative first first third firstSecondDefined
    secondThirdDefined leftDefined rightDefined
  have coordinate := congrArg Vector.r association
  have leftCoordinate :
      (parameters.product
          (parameters.product first first firstSecondDefined) third
            leftDefined).r = 1 := by
    change (Vector.scale
      (1 / parameters.denominator
        (parameters.product first first firstSecondDefined) third)
      (parameters.numerator
        (parameters.product first first firstSecondDefined) third)).r = 1
    rw [leftOuterDenominator, firstSecondProduct]
    unfold numerator third Vector.scale Vector.add Vector.cross
    simp only [leftCoefficient, rightCoefficient,
      RFAP.ExplicitField.div_eq_mul_inv, one_mul,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_self]
    exact constantReverseCancel
  have rightCoordinate :
      (parameters.product first
          (parameters.product first third secondThirdDefined)
            rightDefined).r =
        (parameters.constantCoefficient +
          parameters.dotCoefficient * probe ^ 2)⁻¹ *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
    change (Vector.scale
      (1 / parameters.denominator first
        (parameters.product first third secondThirdDefined))
      (parameters.numerator first
        (parameters.product first third secondThirdDefined))).r = _
    rw [rightOuterDenominator, secondThirdProduct]
    unfold numerator first Vector.scale Vector.add Vector.cross
    rw [leftCoefficient, rightCoefficient]
    simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul]
    ring1
  rw [leftCoordinate, rightCoordinate] at coordinate
  have firstSecondCancel := RFAP.ExplicitField.mul_inv_cancel
    (parameters.constantCoefficient +
      parameters.dotCoefficient * probe ^ 2) probeDefined
  have probeSquareNonzero : probe ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero probeNonzero probeNonzero
  have relationTimesProbeSquare :
      (parameters.constantCoefficient * parameters.dotCoefficient +
        parameters.crossCoefficient ^ 2) * probe ^ 2 = 0 := by
    have cleared :
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) =
          parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
      calc
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) =
          parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) * 1 := by rw [mul_one]
        _ = parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) *
              ((parameters.constantCoefficient +
                  parameters.dotCoefficient * probe ^ 2)⁻¹ *
                (parameters.constantCoefficient -
                  parameters.constantCoefficient⁻¹ *
                    parameters.crossCoefficient ^ 2 * probe ^ 2)) := by
              rw [coordinate]
        _ = parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
              calc
                parameters.constantCoefficient *
                    (parameters.constantCoefficient +
                      parameters.dotCoefficient * probe ^ 2) *
                      ((parameters.constantCoefficient +
                          parameters.dotCoefficient * probe ^ 2)⁻¹ *
                        (parameters.constantCoefficient -
                          parameters.constantCoefficient⁻¹ *
                            parameters.crossCoefficient ^ 2 * probe ^ 2)) =
                  parameters.constantCoefficient *
                    (((parameters.constantCoefficient +
                        parameters.dotCoefficient * probe ^ 2) *
                      (parameters.constantCoefficient +
                        parameters.dotCoefficient * probe ^ 2)⁻¹) *
                      (parameters.constantCoefficient -
                        parameters.constantCoefficient⁻¹ *
                          parameters.crossCoefficient ^ 2 * probe ^ 2)) := by
                            ring1
                _ = _ := by rw [firstSecondCancel, one_mul]
    calc
      (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * probe ^ 2 =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          (parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹) *
              parameters.crossCoefficient ^ 2) * probe ^ 2 := by
                rw [constantCancel, one_mul]
      _ =
        parameters.constantCoefficient *
            (parameters.constantCoefficient +
              parameters.dotCoefficient * probe ^ 2) -
          parameters.constantCoefficient *
            (parameters.constantCoefficient -
              parameters.constantCoefficient⁻¹ *
                parameters.crossCoefficient ^ 2 * probe ^ 2) := by
                  ring1
      _ = 0 := by rw [cleared]; ring1
  have relationZero :
      parameters.constantCoefficient * parameters.dotCoefficient +
        parameters.crossCoefficient ^ 2 = 0 := by
    have probeSquareCancel := RFAP.ExplicitField.mul_inv_cancel
      (probe ^ 2) probeSquareNonzero
    calc
      parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2 =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * 1 := by rw [mul_one]
      _ = (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) *
            ((probe ^ 2) * (probe ^ 2)⁻¹) := by rw [probeSquareCancel]
      _ = ((parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) * probe ^ 2) *
            (probe ^ 2)⁻¹ := by ring1
      _ = 0 := by rw [relationTimesProbeSquare, zero_mul]
  calc
    parameters.constantCoefficient * parameters.dotCoefficient =
        (parameters.constantCoefficient * parameters.dotCoefficient +
          parameters.crossCoefficient ^ 2) -
            parameters.crossCoefficient ^ 2 := by ring1
    _ = -(parameters.crossCoefficient ^ 2) := by rw [relationZero]; ring1

/-- The coefficient equalities forced by a zero identity are also sufficient
for that identity. -/
theorem hasZeroIdentity_of_coefficients
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient) :
    parameters.HasZeroIdentity := by
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  refine
    { constantNonzero := constantNonzero
      rightIdentity := ?_
      leftIdentity := ?_ }
  · intro vector
    apply Vector.ext <;>
      unfold product numerator denominator Vector.zero Vector.scale Vector.add
        Vector.cross Vector.dot <;>
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, sub_self] <;>
      rw [← mul_assoc, constantReverseCancel, one_mul]
  · intro vector
    apply Vector.ext <;>
      unfold product numerator denominator Vector.zero Vector.scale Vector.add
        Vector.cross Vector.dot <;>
      simp only [leftCoefficient, rightCoefficient,
        RFAP.ExplicitField.div_eq_mul_inv, one_mul, mul_zero, zero_mul,
        add_zero, zero_add, sub_self] <;>
      rw [← mul_assoc, constantReverseCancel, one_mul]

/-- The affine-coordinate dilation attached to homogeneous unital
coefficients. -/
def dilationFactor (parameters : CoefficientProductParameters K) : K :=
  parameters.crossCoefficient * parameters.constantCoefficient⁻¹

private theorem inverse_eq_of_mul_eq_one {value candidate : K}
    (valueNonzero : value ≠ 0) (certificate : value * candidate = 1) :
    value⁻¹ = candidate := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel value valueNonzero
  calc
    value⁻¹ = value⁻¹ * 1 := by rw [mul_one]
    _ = value⁻¹ * (value * candidate) := by rw [certificate]
    _ = (value * value⁻¹) * candidate := by ring1
    _ = candidate := by rw [cancel, one_mul]

theorem dilationFactor_mul_constant
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0) :
    parameters.dilationFactor * parameters.constantCoefficient =
      parameters.crossCoefficient := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  unfold dilationFactor
  calc
    parameters.crossCoefficient * parameters.constantCoefficient⁻¹ *
        parameters.constantCoefficient =
      parameters.crossCoefficient *
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) := by ring1
    _ = parameters.crossCoefficient := by rw [reverseCancel, mul_one]

private theorem normalized_dotCoefficient
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.constantCoefficient⁻¹ * parameters.dotCoefficient =
      -(parameters.dilationFactor ^ 2) := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have inverseSquaredTimesConstant :
      parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient =
        parameters.constantCoefficient⁻¹ := by
    calc
      parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient =
        parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient⁻¹ *
            parameters.constantCoefficient) := by ring1
      _ = parameters.constantCoefficient⁻¹ := by
        rw [reverseCancel, mul_one]
  calc
    parameters.constantCoefficient⁻¹ * parameters.dotCoefficient =
        (parameters.constantCoefficient⁻¹ ^ 2 *
          parameters.constantCoefficient) *
            parameters.dotCoefficient := by rw [inverseSquaredTimesConstant]
    _ = parameters.constantCoefficient⁻¹ ^ 2 *
        (parameters.constantCoefficient *
          parameters.dotCoefficient) := by ring1
    _ = parameters.constantCoefficient⁻¹ ^ 2 *
        (-(parameters.crossCoefficient ^ 2)) := by rw [coefficientRelation]
    _ = -(parameters.dilationFactor ^ 2) := by
      unfold dilationFactor
      ring1

theorem dilation_denominator
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Vector K) :
    anchorProductDenominator
        (Vector.scale parameters.dilationFactor left)
        (Vector.scale parameters.dilationFactor right) =
      parameters.constantCoefficient⁻¹ *
        parameters.denominator left right := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have normalized := normalized_dotCoefficient parameters constantNonzero
    coefficientRelation
  unfold anchorProductDenominator denominator
  rw [Vector.dot_scale_left, Vector.dot_scale_right]
  calc
    1 - parameters.dilationFactor *
        (parameters.dilationFactor * Vector.dot left right) =
      parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient +
        (parameters.constantCoefficient⁻¹ *
          parameters.dotCoefficient) * Vector.dot left right := by
            rw [reverseCancel, normalized]
            ring1
    _ = parameters.constantCoefficient⁻¹ *
        (parameters.constantCoefficient +
          parameters.dotCoefficient * Vector.dot left right) := by ring1

theorem dilationProductDefined
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    anchorProductDenominator
      (Vector.scale parameters.dilationFactor left)
      (Vector.scale parameters.dilationFactor right) ≠ 0 := by
  rw [parameters.dilation_denominator constantNonzero coefficientRelation]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.inv_ne_zero constantNonzero) defined

/-- After multiplying the output by the dilation factor, every nondegenerate
member of the classified family is literally the opposite anchor product on
dilated inputs. -/
theorem dilation_product
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2))
    (left right : Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    Vector.scale parameters.dilationFactor
        (parameters.product left right defined) =
      oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor left)
        (Vector.scale parameters.dilationFactor right)
        (parameters.dilationProductDefined constantNonzero
          coefficientRelation left right defined) := by
  have denominatorRelation := parameters.dilation_denominator
    constantNonzero coefficientRelation left right
  have dilatedDefined := parameters.dilationProductDefined constantNonzero
    coefficientRelation left right defined
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (parameters.denominator left right) defined
  have constantReverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  have dilatedInverse :
      (anchorProductDenominator
        (Vector.scale parameters.dilationFactor left)
        (Vector.scale parameters.dilationFactor right))⁻¹ =
      parameters.constantCoefficient *
        (parameters.denominator left right)⁻¹ := by
    apply inverse_eq_of_mul_eq_one dilatedDefined
    rw [denominatorRelation]
    calc
      parameters.constantCoefficient⁻¹ *
          parameters.denominator left right *
          (parameters.constantCoefficient *
            (parameters.denominator left right)⁻¹) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) *
          (parameters.denominator left right *
            (parameters.denominator left right)⁻¹) := by ring1
      _ = 1 := by rw [constantReverseCancel, denominatorCancel, one_mul]
  have factorTimesConstant := parameters.dilationFactor_mul_constant
    constantNonzero
  unfold product oppositeAnchorProduct
  simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul]
  rw [dilatedInverse]
  apply Vector.ext <;>
    unfold numerator oppositeAnchorProductNumerator Vector.scale Vector.add
      Vector.cross <;>
    rw [leftCoefficient, rightCoefficient, ← factorTimesConstant] <;>
    ring1

private theorem vector_eq_of_scale_eq_scale {factor : K}
    (factorNonzero : factor ≠ 0) {left right : Vector K}
    (scaled : Vector.scale factor left = Vector.scale factor right) :
    left = right := by
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  apply Vector.ext
  · have coordinate := congrArg Vector.t scaled
    dsimp only [Vector.scale] at coordinate
    calc
      left.t = (factor⁻¹ * factor) * left.t := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.t) := by ring1
      _ = factor⁻¹ * (factor * right.t) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.t := by ring1
      _ = right.t := by rw [reverseCancel, one_mul]
  · have coordinate := congrArg Vector.r scaled
    dsimp only [Vector.scale] at coordinate
    calc
      left.r = (factor⁻¹ * factor) * left.r := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.r) := by ring1
      _ = factor⁻¹ * (factor * right.r) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.r := by ring1
      _ = right.r := by rw [reverseCancel, one_mul]
  · have coordinate := congrArg Vector.s scaled
    dsimp only [Vector.scale] at coordinate
    calc
      left.s = (factor⁻¹ * factor) * left.s := by rw [reverseCancel, one_mul]
      _ = factor⁻¹ * (factor * left.s) := by ring1
      _ = factor⁻¹ * (factor * right.s) := by rw [coordinate]
      _ = (factor⁻¹ * factor) * right.s := by ring1
      _ = right.s := by rw [reverseCancel, one_mul]

private theorem oppositeAnchorProduct_congr_left
    {first second right : Vector K} (equal : first = second)
    (firstDefined : anchorProductDenominator first right ≠ 0)
    (secondDefined : anchorProductDenominator second right ≠ 0) :
    oppositeAnchorProduct first right firstDefined =
      oppositeAnchorProduct second right secondDefined := by
  subst second
  rfl

private theorem oppositeAnchorProduct_congr_right
    {left first second : Vector K} (equal : first = second)
    (firstDefined : anchorProductDenominator left first ≠ 0)
    (secondDefined : anchorProductDenominator left second ≠ 0) :
    oppositeAnchorProduct left first firstDefined =
      oppositeAnchorProduct left second secondDefined := by
  subst second
  rfl

/-- The nonzero-cross members of the homogeneous classified family are
associative because dilation transports them to the opposite anchor product.
All domain certificates are transported by explicit denominator equalities. -/
theorem associativeWhereDefined_of_coefficients_of_crossCoefficient_ne_zero
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (crossNonzero : parameters.crossCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.AssociativeWhereDefined := by
  have factorNonzero : parameters.dilationFactor ≠ 0 := by
    unfold dilationFactor
    exact RFAP.ExplicitField.mul_ne_zero crossNonzero
      (RFAP.ExplicitField.inv_ne_zero constantNonzero)
  intro first second third firstSecondDefined secondThirdDefined leftDefined
    rightDefined
  let firstSecondDilatedDefined := parameters.dilationProductDefined
    constantNonzero coefficientRelation first second firstSecondDefined
  let secondThirdDilatedDefined := parameters.dilationProductDefined
    constantNonzero coefficientRelation second third secondThirdDefined
  let leftDilatedDefined : anchorProductDenominator
      (oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor first)
        (Vector.scale parameters.dilationFactor second)
        firstSecondDilatedDefined)
      (Vector.scale parameters.dilationFactor third) ≠ 0 := by
    have transported := parameters.dilationProductDefined constantNonzero
      coefficientRelation
      (parameters.product first second firstSecondDefined) third leftDefined
    rw [parameters.dilation_product constantNonzero leftCoefficient
      rightCoefficient coefficientRelation first second firstSecondDefined]
      at transported
    exact transported
  let rightDilatedDefined : anchorProductDenominator
      (Vector.scale parameters.dilationFactor first)
      (oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor second)
        (Vector.scale parameters.dilationFactor third)
        secondThirdDilatedDefined) ≠ 0 := by
    have transported := parameters.dilationProductDefined constantNonzero
      coefficientRelation first
      (parameters.product second third secondThirdDefined) rightDefined
    rw [parameters.dilation_product constantNonzero leftCoefficient
      rightCoefficient coefficientRelation second third secondThirdDefined]
      at transported
    exact transported
  have dilatedAssociation := oppositeAnchorProduct_associative
    (Vector.scale parameters.dilationFactor first)
    (Vector.scale parameters.dilationFactor second)
    (Vector.scale parameters.dilationFactor third)
    firstSecondDilatedDefined secondThirdDilatedDefined leftDilatedDefined
    rightDilatedDefined
  have firstSecondDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation first second
    firstSecondDefined
  have secondThirdDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation second third
    secondThirdDefined
  have leftOuterDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation
    (parameters.product first second firstSecondDefined) third leftDefined
  have rightOuterDilated := parameters.dilation_product constantNonzero
    leftCoefficient rightCoefficient coefficientRelation first
    (parameters.product second third secondThirdDefined) rightDefined
  apply vector_eq_of_scale_eq_scale factorNonzero
  calc
    Vector.scale parameters.dilationFactor
        (parameters.product
          (parameters.product first second firstSecondDefined) third
            leftDefined) =
      oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor
          (parameters.product first second firstSecondDefined))
        (Vector.scale parameters.dilationFactor third) _ := leftOuterDilated
    _ = oppositeAnchorProduct
        (oppositeAnchorProduct
          (Vector.scale parameters.dilationFactor first)
          (Vector.scale parameters.dilationFactor second)
          firstSecondDilatedDefined)
        (Vector.scale parameters.dilationFactor third)
          leftDilatedDefined :=
      oppositeAnchorProduct_congr_left firstSecondDilated _ _
    _ = oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor first)
        (oppositeAnchorProduct
          (Vector.scale parameters.dilationFactor second)
          (Vector.scale parameters.dilationFactor third)
          secondThirdDilatedDefined)
        rightDilatedDefined := dilatedAssociation
    _ = oppositeAnchorProduct
        (Vector.scale parameters.dilationFactor first)
        (Vector.scale parameters.dilationFactor
          (parameters.product second third secondThirdDefined)) _ :=
      oppositeAnchorProduct_congr_right secondThirdDilated.symm _ _
    _ = Vector.scale parameters.dilationFactor
        (parameters.product first
          (parameters.product second third secondThirdDefined)
            rightDefined) := rightOuterDilated.symm

private theorem product_eq_add_of_cross_and_dot_zero
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (crossZero : parameters.crossCoefficient = 0)
    (dotZero : parameters.dotCoefficient = 0)
    (left right : Vector K)
    (defined : parameters.denominator left right ≠ 0) :
    parameters.product left right defined = Vector.add left right := by
  have reverseCancel : parameters.constantCoefficient⁻¹ *
      parameters.constantCoefficient = 1 := by
    calc
      parameters.constantCoefficient⁻¹ * parameters.constantCoefficient =
          parameters.constantCoefficient *
            parameters.constantCoefficient⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
  apply Vector.ext <;>
    unfold product numerator denominator Vector.scale Vector.add Vector.cross
      Vector.dot <;>
    rw [leftCoefficient, rightCoefficient, crossZero, dotZero] <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul, zero_mul, add_zero]
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.t +
            parameters.constantCoefficient * right.t) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.t +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.t := by ring1
      _ = left.t + right.t := by simp only [reverseCancel, one_mul]
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.r +
            parameters.constantCoefficient * right.r) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.r +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.r := by ring1
      _ = left.r + right.r := by simp only [reverseCancel, one_mul]
  · calc
      parameters.constantCoefficient⁻¹ *
          (parameters.constantCoefficient * left.s +
            parameters.constantCoefficient * right.s) =
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * left.s +
        (parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient) * right.s := by ring1
      _ = left.s + right.s := by simp only [reverseCancel, one_mul]

/-- Complete sufficiency: with decidable equality, the zero-cross case is
ordinary vector addition and the nonzero-cross case is transported to the
opposite anchor product by dilation. -/
theorem associativeWhereDefined_of_coefficients [DecidableEq K]
    (parameters : CoefficientProductParameters K)
    (constantNonzero : parameters.constantCoefficient ≠ 0)
    (leftCoefficient : parameters.leftCoefficient =
      parameters.constantCoefficient)
    (rightCoefficient : parameters.rightCoefficient =
      parameters.constantCoefficient)
    (coefficientRelation :
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2)) :
    parameters.AssociativeWhereDefined := by
  by_cases crossZero : parameters.crossCoefficient = 0
  · have productRelation :
        parameters.constantCoefficient * parameters.dotCoefficient = 0 := by
      calc
        parameters.constantCoefficient * parameters.dotCoefficient =
            -(parameters.crossCoefficient ^ 2) := coefficientRelation
        _ = 0 := by rw [crossZero]; ring1
    have dotZero : parameters.dotCoefficient = 0 := by
      have constantCancel := RFAP.ExplicitField.mul_inv_cancel
        parameters.constantCoefficient constantNonzero
      have reverseCancel : parameters.constantCoefficient⁻¹ *
          parameters.constantCoefficient = 1 := by
        calc
          parameters.constantCoefficient⁻¹ *
              parameters.constantCoefficient =
            parameters.constantCoefficient *
              parameters.constantCoefficient⁻¹ := by ring1
          _ = 1 := constantCancel
      calc
        parameters.dotCoefficient = 1 * parameters.dotCoefficient := by
          rw [one_mul]
        _ = (parameters.constantCoefficient⁻¹ *
            parameters.constantCoefficient) *
              parameters.dotCoefficient := by rw [reverseCancel]
        _ = parameters.constantCoefficient⁻¹ *
            (parameters.constantCoefficient *
              parameters.dotCoefficient) := by ring1
        _ = 0 := by rw [productRelation, mul_zero]
    intro first second third firstSecondDefined secondThirdDefined leftDefined
      rightDefined
    have firstSecondValue := product_eq_add_of_cross_and_dot_zero parameters
      constantNonzero leftCoefficient rightCoefficient crossZero dotZero first
      second firstSecondDefined
    have secondThirdValue := product_eq_add_of_cross_and_dot_zero parameters
      constantNonzero leftCoefficient rightCoefficient crossZero dotZero second
      third secondThirdDefined
    calc
      parameters.product
          (parameters.product first second firstSecondDefined) third
            leftDefined =
        Vector.add (parameters.product first second firstSecondDefined) third :=
          product_eq_add_of_cross_and_dot_zero parameters constantNonzero
            leftCoefficient rightCoefficient crossZero dotZero _ _ _
      _ = Vector.add (Vector.add first second) third :=
        congrArg (fun value => Vector.add value third) firstSecondValue
      _ = Vector.add first (Vector.add second third) := by
        apply Vector.ext <;> unfold Vector.add <;> ring1
      _ = Vector.add first
          (parameters.product second third secondThirdDefined) :=
        congrArg (Vector.add first) secondThirdValue.symm
      _ = parameters.product first
          (parameters.product second third secondThirdDefined) rightDefined :=
        (product_eq_add_of_cross_and_dot_zero parameters constantNonzero
          leftCoefficient rightCoefficient crossZero dotZero _ _ _).symm
  · exact
      parameters.associativeWhereDefined_of_coefficients_of_crossCoefficient_ne_zero
        constantNonzero crossZero leftCoefficient rightCoefficient
          coefficientRelation

/-- Hardened Conjecture 52 / Problem 68 over the paper's primary field.  A
homogeneous five-coefficient product is unital and associative exactly when
its two linear coefficients equal the nonzero denominator constant and its
dot and cross coefficients satisfy `ιδ = -γ²`.  The necessity proof tests
only the displayed probes `1` and, in the exceptional denominator case, `2`.
-/
theorem rational_hardenedAssociativityClassification
    (parameters : CoefficientProductParameters
      RFAP.ConstructiveFraction.Rational) :
    (parameters.HasZeroIdentity ∧ parameters.AssociativeWhereDefined) ↔
      parameters.constantCoefficient ≠ 0 ∧
      parameters.leftCoefficient = parameters.constantCoefficient ∧
      parameters.rightCoefficient = parameters.constantCoefficient ∧
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2) := by
  constructor
  · rintro ⟨identity, associative⟩
    refine ⟨identity.constantNonzero,
      parameters.leftCoefficient_eq_constant identity,
      parameters.rightCoefficient_eq_constant identity, ?_⟩
    by_cases firstProbeDefined :
        parameters.constantCoefficient +
          parameters.dotCoefficient * (1 :
            RFAP.ConstructiveFraction.Rational) ^ 2 ≠ 0
    · exact parameters.constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
        identity associative 1 (by decide) firstProbeDefined
    · have firstProbeZero :
          parameters.constantCoefficient +
            parameters.dotCoefficient * (1 :
              RFAP.ConstructiveFraction.Rational) ^ 2 = 0 := by
        exact Decidable.not_not.mp firstProbeDefined
      have secondProbeDefined :
          parameters.constantCoefficient +
            parameters.dotCoefficient * (2 :
              RFAP.ConstructiveFraction.Rational) ^ 2 ≠ 0 := by
        intro secondProbeZero
        have tripleConstantZero :
            (3 : RFAP.ConstructiveFraction.Rational) *
              parameters.constantCoefficient = 0 := by
          calc
            (3 : RFAP.ConstructiveFraction.Rational) *
                parameters.constantCoefficient =
              4 * (parameters.constantCoefficient +
                parameters.dotCoefficient * 1 ^ 2) -
              (parameters.constantCoefficient +
                parameters.dotCoefficient * 2 ^ 2) := by ring1
            _ = 0 := by rw [firstProbeZero, secondProbeZero]; ring1
        exact RFAP.ExplicitField.mul_ne_zero (by decide)
          identity.constantNonzero tripleConstantZero
      exact parameters.constant_mul_dotCoefficient_eq_neg_crossCoefficient_sq
        identity associative 2 (by decide) secondProbeDefined
  · rintro ⟨constantNonzero, leftCoefficient, rightCoefficient,
      coefficientRelation⟩
    exact
      ⟨parameters.hasZeroIdentity_of_coefficients constantNonzero
          leftCoefficient rightCoefficient,
        parameters.associativeWhereDefined_of_coefficients constantNonzero
          leftCoefficient rightCoefficient coefficientRelation⟩

/-- Equality up to global nonzero rescaling of the five homogeneous
coefficients. -/
def Equivalent (left right : CoefficientProductParameters K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.leftCoefficient = factor * left.leftCoefficient ∧
    right.rightCoefficient = factor * left.rightCoefficient ∧
    right.crossCoefficient = factor * left.crossCoefficient ∧
    right.constantCoefficient = factor * left.constantCoefficient ∧
    right.dotCoefficient = factor * left.dotCoefficient

/-- The anchor product `(v+u-v×u)/(1-v·u)`. -/
def anchorParameters : CoefficientProductParameters K :=
  ⟨1, 1, -1, 1, -1⟩

/-- The opposite product `(v+u+v×u)/(1-v·u)`. -/
def oppositeParameters : CoefficientProductParameters K :=
  ⟨1, 1, 1, 1, -1⟩

/-- The literal statement of Conjecture 52 (and Problem 68) in homogeneous
coefficient form. -/
def AssociativityConjecture : Prop :=
  ∀ parameters : CoefficientProductParameters K,
    parameters.AssociativeWhereDefined →
      parameters.Equivalent anchorParameters ∨
        parameters.Equivalent oppositeParameters

/-- A degenerate member of the displayed family: `v ⋆ u = v`. -/
def leftProjectionParameters : CoefficientProductParameters K :=
  ⟨1, 0, 0, 1, 0⟩

theorem leftProjection_denominator (left right : Vector K) :
    leftProjectionParameters.denominator left right = 1 := by
  unfold leftProjectionParameters denominator
  ring1

theorem leftProjection_product (left right : Vector K)
    (defined : leftProjectionParameters.denominator left right ≠ 0) :
    leftProjectionParameters.product left right defined = left := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (leftProjectionParameters.denominator left right) defined
  rw [leftProjection_denominator] at cancel
  have inverseOne : (1 : K)⁻¹ = 1 := by
    simpa only [one_mul] using cancel
  unfold product
  rw [leftProjection_denominator, RFAP.ExplicitField.div_eq_mul_inv,
    one_mul, inverseOne]
  apply Vector.ext <;> unfold numerator leftProjectionParameters Vector.scale
    Vector.add Vector.cross <;> ring1

theorem leftProjection_associative :
    AssociativeWhereDefined
      (leftProjectionParameters : CoefficientProductParameters K) := by
  intro first second third firstSecondDefined secondThirdDefined leftDefined
    rightDefined
  rw [leftProjection_product, leftProjection_product,
    leftProjection_product]

private theorem one_ne_zero_of_two_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 2 * 1 := by ring1
    _ = 2 * 0 := by rw [oneZero]
    _ = 0 := by ring1

theorem leftProjection_not_equivalent_anchor (twoNonzero : (2 : K) ≠ 0) :
    ¬ (leftProjectionParameters : CoefficientProductParameters K).Equivalent
      anchorParameters := by
  rintro ⟨factor, _, _, rightCoefficient, _⟩
  apply one_ne_zero_of_two_ne_zero twoNonzero
  calc
    (1 : K) = factor * 0 := rightCoefficient
    _ = 0 := by ring1

theorem leftProjection_not_equivalent_opposite
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (leftProjectionParameters : CoefficientProductParameters K).Equivalent
      oppositeParameters := by
  rintro ⟨factor, _, _, rightCoefficient, _⟩
  apply one_ne_zero_of_two_ne_zero twoNonzero
  calc
    (1 : K) = factor * 0 := rightCoefficient
    _ = 0 := by ring1

/-- Conjecture 52 is false as printed unless degenerate coefficient families
such as projections are excluded. -/
theorem associativityConjecture_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@AssociativityConjecture K _) := by
  intro conjecture
  rcases conjecture leftProjectionParameters leftProjection_associative with
    anchorCase | oppositeCase
  · exact leftProjection_not_equivalent_anchor twoNonzero anchorCase
  · exact leftProjection_not_equivalent_opposite twoNonzero oppositeCase

end CoefficientProductParameters

/-! ### The exact normalized family printed in Conjecture 52 -/

/-- The four coefficients in the paper's normalized expression
`(αv + βu + γ(v × u)) / (1 + δ(v · u))`. -/
@[ext]
structure NormalizedCoefficientProductParameters (K : Type*) where
  leftCoefficient : K
  rightCoefficient : K
  crossCoefficient : K
  dotCoefficient : K

namespace NormalizedCoefficientProductParameters

/-- Embed the paper's constant-denominator-one family into the homogeneous
five-coefficient family. -/
def toHomogeneous (parameters : NormalizedCoefficientProductParameters K) :
    CoefficientProductParameters K :=
  ⟨parameters.leftCoefficient, parameters.rightCoefficient,
    parameters.crossCoefficient, 1, parameters.dotCoefficient⟩

/-- The exact normalized form of Conjecture 52 and Problem 68. -/
def AssociativityConjecture : Prop :=
  ∀ parameters : NormalizedCoefficientProductParameters K,
    parameters.toHomogeneous.AssociativeWhereDefined →
      parameters.toHomogeneous.Equivalent
          CoefficientProductParameters.anchorParameters ∨
        parameters.toHomogeneous.Equivalent
          CoefficientProductParameters.oppositeParameters

/-- The normalized left projection `v ⋆ u = v`; unlike a counterexample with
zero constant denominator, this lies literally in the family printed in the
paper. -/
def leftProjection : NormalizedCoefficientProductParameters K :=
  ⟨1, 0, 0, 0⟩

theorem leftProjection_toHomogeneous :
    (leftProjection : NormalizedCoefficientProductParameters K).toHomogeneous =
      CoefficientProductParameters.leftProjectionParameters := rfl

theorem leftProjection_associative :
    CoefficientProductParameters.AssociativeWhereDefined
      (leftProjection : NormalizedCoefficientProductParameters K).toHomogeneous := by
  rw [leftProjection_toHomogeneous]
  exact CoefficientProductParameters.leftProjection_associative

/-- Conjecture 52 and Problem 68 are false in their exact normalized
four-coefficient form. -/
theorem associativityConjecture_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@AssociativityConjecture K _) := by
  intro conjecture
  rcases conjecture leftProjection leftProjection_associative with
    anchorCase | oppositeCase
  · rw [leftProjection_toHomogeneous] at anchorCase
    exact CoefficientProductParameters.leftProjection_not_equivalent_anchor
      twoNonzero anchorCase
  · rw [leftProjection_toHomogeneous] at oppositeCase
    exact CoefficientProductParameters.leftProjection_not_equivalent_opposite
      twoNonzero oppositeCase

end NormalizedCoefficientProductParameters

namespace ConjectureFiftyTwoNumerics

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def first : Vector Scalar := ⟨1, 2, 3⟩
def second : Vector Scalar := ⟨5, 1, 2⟩
def third : Vector Scalar := ⟨-3, 4, 1⟩

/-- The paper's variant with denominator `1+v·u`. -/
def plusDenominator : CoefficientProductParameters Scalar :=
  ⟨1, 1, -1, 1, 1⟩

theorem plus_firstSecond_defined :
    plusDenominator.denominator first second ≠ 0 := by decide

theorem plus_secondThird_defined :
    plusDenominator.denominator second third ≠ 0 := by decide

theorem plus_left_defined :
    plusDenominator.denominator
      (plusDenominator.product first second plus_firstSecond_defined) third ≠
        0 := by decide

theorem plus_right_defined :
    plusDenominator.denominator first
      (plusDenominator.product second third plus_secondThird_defined) ≠ 0 := by
  decide

theorem plusDenominator_not_associative_on_displayed_triple :
    plusDenominator.product
        (plusDenominator.product first second plus_firstSecond_defined) third
          plus_left_defined ≠
      plusDenominator.product first
        (plusDenominator.product second third plus_secondThird_defined)
          plus_right_defined := by decide

/-- The paper's variant with cross coefficient two. -/
def doubleCross : CoefficientProductParameters Scalar :=
  ⟨1, 1, 2, 1, -1⟩

theorem double_firstSecond_defined :
    doubleCross.denominator first second ≠ 0 := by decide

theorem double_secondThird_defined :
    doubleCross.denominator second third ≠ 0 := by decide

theorem double_left_defined :
    doubleCross.denominator
      (doubleCross.product first second double_firstSecond_defined) third ≠ 0 := by
  decide

theorem double_right_defined :
    doubleCross.denominator first
      (doubleCross.product second third double_secondThird_defined) ≠ 0 := by
  decide

theorem doubleCross_not_associative_on_displayed_triple :
    doubleCross.product
        (doubleCross.product first second double_firstSecond_defined) third
          double_left_defined ≠
      doubleCross.product first
        (doubleCross.product second third double_secondThird_defined)
          double_right_defined := by decide

end ConjectureFiftyTwoNumerics

end RationalRotations
