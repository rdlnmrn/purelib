import DivineProportions.Conics.Tangent

/-!
# Divine Proportions, §19.5: the lemniscate of Bernoulli

The quartic is retained as one finite polynomial equation.  Its tangent line,
tangent conic, discriminant conic, and the inverse-quadrance relation of
Exercise 19.5 are proved by exact coefficient calculations over any explicit
constructive field.
-/

namespace DivineProportions

namespace Lemniscate

variable {K : Type*} [RFAP.ExplicitField K]

/-- The Bernoulli lemniscate with parameter `A=a²`:
`(x²+y²)²=2A(x²-y²)`. -/
def evaluate (parameter : K) (point : Point K) : K :=
  (point.x ^ 2 + point.y ^ 2) ^ 2 -
    2 * parameter * (point.x ^ 2 - point.y ^ 2)

def Contains (parameter : K) (point : Point K) : Prop :=
  evaluate parameter point = 0

/-- The associated equation after setting `X=x²`, `Y=y²`. -/
def AssociatedContains (parameter : K) (point : Point K) : Prop :=
  (point.x + point.y) ^ 2 =
    2 * parameter * (point.x - point.y)

/-- Squaring a lemniscate point gives a point of its associated equation. -/
theorem squarePoint_associated
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point) :
    AssociatedContains parameter ⟨point.x ^ 2, point.y ^ 2⟩ := by
  unfold Contains evaluate at onLemniscate
  unfold AssociatedContains
  calc
    (point.x ^ 2 + point.y ^ 2) ^ 2 =
        2 * parameter * (point.x ^ 2 - point.y ^ 2) := by
      calc
        (point.x ^ 2 + point.y ^ 2) ^ 2 =
            ((point.x ^ 2 + point.y ^ 2) ^ 2 -
                2 * parameter * (point.x ^ 2 - point.y ^ 2)) +
              2 * parameter * (point.x ^ 2 - point.y ^ 2) := by ring1
        _ = 2 * parameter * (point.x ^ 2 - point.y ^ 2) := by
          rw [onLemniscate]
          ring1

/-- The associated parametrization printed in §19.5. -/
def associatedParameterPoint (parameter slope : K) : Point K :=
  let denominator := (1 + slope) ^ 2
  ⟨(2 * parameter * (1 - slope)) / denominator,
    (2 * parameter * slope * (1 - slope)) / denominator⟩

/-- Every allowed slope supplies a point of the associated equation. -/
theorem associatedParameterPoint_contains
    (parameter slope : K) (onePlusSlopeNonzero : 1 + slope ≠ 0) :
    AssociatedContains parameter (associatedParameterPoint parameter slope) := by
  let denominator := (1 + slope) ^ 2
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero onePlusSlopeNonzero onePlusSlopeNonzero
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold AssociatedContains associatedParameterPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    ((2 * parameter * (1 - slope)) * denominator⁻¹ +
        (2 * parameter * slope * (1 - slope)) * denominator⁻¹) ^ 2 =
      2 * parameter *
        ((2 * parameter * (1 - slope)) * denominator⁻¹ -
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹)
  calc
    ((2 * parameter * (1 - slope)) * denominator⁻¹ +
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹) ^ 2 =
        4 * parameter ^ 2 * (1 - slope) ^ 2 *
          denominator⁻¹ * (denominator * denominator⁻¹) := by
      unfold denominator
      ring1
    _ = 4 * parameter ^ 2 * (1 - slope) ^ 2 * denominator⁻¹ := by
      rw [cancel]
      ring1
    _ = 2 * parameter *
        ((2 * parameter * (1 - slope)) * denominator⁻¹ -
          (2 * parameter * slope * (1 - slope)) * denominator⁻¹) := by
      unfold denominator
      ring1

/-- The two first-order coefficients at a displayed point. -/
def tangentA (parameter : K) (point : Point K) : K :=
  point.x * (point.x ^ 2 + point.y ^ 2 - parameter)

def tangentB (parameter : K) (point : Point K) : K :=
  point.y * (point.x ^ 2 + point.y ^ 2 + parameter)

def IsNonSingularAt (parameter : K) (point : Point K) : Prop :=
  tangentA parameter point ≠ 0 ∨ tangentB parameter point ≠ 0

/-- The first-order tangent line translated back to its base point. -/
def tangentLine (parameter : K) (point : Point K)
    (nonSingular : IsNonSingularAt parameter point) : Line K where
  a := tangentA parameter point
  b := tangentB parameter point
  c := -parameter * (point.x ^ 2 - point.y ^ 2)
  direction_nonzero := nonSingular

/-- The source's tangent line contains its incident base point. -/
theorem tangentLine_contains
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point)
    (nonSingular : IsNonSingularAt parameter point) :
    (tangentLine parameter point nonSingular).Contains point := by
  unfold Contains evaluate at onLemniscate
  unfold tangentLine tangentA tangentB Line.Contains
  calc
    point.x * (point.x ^ 2 + point.y ^ 2 - parameter) * point.x +
          point.y * (point.x ^ 2 + point.y ^ 2 + parameter) * point.y +
          -parameter * (point.x ^ 2 - point.y ^ 2) =
        (point.x ^ 2 + point.y ^ 2) ^ 2 -
          2 * parameter * (point.x ^ 2 - point.y ^ 2) := by ring1
    _ = 0 := onLemniscate

/-- The three second-order Taylor coefficients. -/
def tangentD (parameter : K) (point : Point K) : K :=
  3 * point.x ^ 2 + point.y ^ 2 - parameter

def tangentE (point : Point K) : K :=
  4 * point.x * point.y

def tangentF (parameter : K) (point : Point K) : K :=
  point.x ^ 2 + 3 * point.y ^ 2 + parameter

def IsSecondOrderNonSingularAt (parameter : K) (point : Point K) : Prop :=
  tangentD parameter point ≠ 0 ∨ tangentE point ≠ 0 ∨
    tangentF parameter point ≠ 0

/-- The second-order tangent conic after translating back to the base point. -/
def tangentConic (parameter : K) (point : Point K)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    Conic K where
  d := tangentD parameter point
  e := tangentE point
  f := tangentF parameter point
  a := -4 * point.x * (point.x ^ 2 + point.y ^ 2)
  b := -4 * point.y * (point.x ^ 2 + point.y ^ 2)
  c := 3 * parameter * (point.x ^ 2 - point.y ^ 2)
  quadratic_nonzero := secondOrderNonSingular

/-- The second-order tangent conic contains its base point. -/
theorem tangentConic_contains
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    (tangentConic parameter point secondOrderNonSingular).Contains point := by
  unfold Contains evaluate at onLemniscate
  unfold tangentConic tangentD tangentE tangentF Conic.Contains Conic.evaluate
  calc
    (3 * point.x ^ 2 + point.y ^ 2 - parameter) * point.x ^ 2 +
          (4 * point.x * point.y) * point.x * point.y +
          (point.x ^ 2 + 3 * point.y ^ 2 + parameter) * point.y ^ 2 +
          (-4 * point.x * (point.x ^ 2 + point.y ^ 2)) * point.x +
          (-4 * point.y * (point.x ^ 2 + point.y ^ 2)) * point.y +
          3 * parameter * (point.x ^ 2 - point.y ^ 2) =
        -((point.x ^ 2 + point.y ^ 2) ^ 2 -
          2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
    _ = 0 := by rw [onLemniscate]; ring1

/-- The first-order tangent to the lemniscate is also the tangent to its
second-order tangent conic at the same point. -/
theorem tangentLine_is_tangent_to_tangentConic
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point)
    (twoNonzero : (2 : K) ≠ 0)
    (nonSingular : IsNonSingularAt parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    ∃ conicNonSingular :
        (tangentConic parameter point secondOrderNonSingular).IsNonSingularAt
          point,
      (tangentLine parameter point nonSingular).Equivalent
        (Conic.tangentLine
          (tangentConic parameter point secondOrderNonSingular)
          point conicNonSingular) := by
  let conic := tangentConic parameter point secondOrderNonSingular
  have firstGradient :
      conic.a + 2 * conic.d * point.x + conic.e * point.y =
        2 * tangentA parameter point := by
    unfold conic tangentConic tangentD tangentE tangentA
    ring1
  have secondGradient :
      conic.b + conic.e * point.x + 2 * conic.f * point.y =
        2 * tangentB parameter point := by
    unfold conic tangentConic tangentE tangentF tangentB
    ring1
  have conicNonSingular : conic.IsNonSingularAt point := by
    unfold Conic.IsNonSingularAt
    rw [firstGradient, secondGradient]
    rcases nonSingular with firstNonzero | secondNonzero
    · left
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero firstNonzero
    · right
      exact RFAP.ExplicitField.mul_ne_zero twoNonzero secondNonzero
  refine ⟨conicNonSingular, ?_⟩
  have constantCoefficient :
      conic.a * point.x + conic.b * point.y + 2 * conic.c =
        2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) := by
    unfold conic tangentConic
    unfold Contains evaluate at onLemniscate
    calc
      (-4 * point.x * (point.x ^ 2 + point.y ^ 2)) * point.x +
            (-4 * point.y * (point.x ^ 2 + point.y ^ 2)) * point.y +
            2 * (3 * parameter * (point.x ^ 2 - point.y ^ 2)) =
          2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) -
            4 * ((point.x ^ 2 + point.y ^ 2) ^ 2 -
              2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
      _ = 2 * (-parameter * (point.x ^ 2 - point.y ^ 2)) := by
        rw [onLemniscate]
        ring1
  unfold Line.Equivalent
  dsimp only [Conic.tangentLine, tangentLine]
  rw [firstGradient, secondGradient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩

/-- The conic whose equation is `8(x²-y²)=A`. -/
def discriminantConic [Nontrivial K]
    (parameter : K) (eightNonzero : (8 : K) ≠ 0) : Conic K where
  d := 8
  e := 0
  f := -8
  a := 0
  b := 0
  c := -parameter
  quadratic_nonzero := Or.inl eightNonzero

def discriminantValue (parameter : K) (point : Point K) : K :=
  8 * (point.x ^ 2 - point.y ^ 2) - parameter

theorem discriminantConic_evaluate [Nontrivial K]
    (parameter : K) (eightNonzero : (8 : K) ≠ 0) (point : Point K) :
    (discriminantConic parameter eightNonzero).evaluate point =
      discriminantValue parameter point := by
  unfold discriminantConic Conic.evaluate discriminantValue
  ring1

/-- The displayed tangent-conic discriminant factorization. -/
theorem tangentConic_discriminant
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    (tangentConic parameter point secondOrderNonSingular).centerDiscriminant =
      4 * (-8 * parameter * point.x ^ 2 +
        8 * parameter * point.y ^ 2 + parameter ^ 2) := by
  unfold Contains evaluate at onLemniscate
  unfold Conic.centerDiscriminant tangentConic tangentD tangentE tangentF
  calc
    (4 * point.x * point.y) ^ 2 -
          4 * (3 * point.x ^ 2 + point.y ^ 2 - parameter) *
            (point.x ^ 2 + 3 * point.y ^ 2 + parameter) =
        4 * (-8 * parameter * point.x ^ 2 +
            8 * parameter * point.y ^ 2 + parameter ^ 2) -
          12 * ((point.x ^ 2 + point.y ^ 2) ^ 2 -
            2 * parameter * (point.x ^ 2 - point.y ^ 2)) := by ring1
    _ = 4 * (-8 * parameter * point.x ^ 2 +
        8 * parameter * point.y ^ 2 + parameter ^ 2) := by
      rw [onLemniscate]
      ring1

/-- The same calculation exposes the discriminant conic as one product. -/
theorem tangentConic_discriminant_factor
    (parameter : K) (point : Point K)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    (tangentConic parameter point secondOrderNonSingular).centerDiscriminant =
      -(4 * parameter) * discriminantValue parameter point := by
  rw [tangentConic_discriminant parameter point onLemniscate]
  unfold discriminantValue
  ring1

private theorem eq_zero_of_nonzero_mul_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [cancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-- For nonzero `4A`, the tangent conic is central exactly away from the
displayed discriminant conic.  This theorem records the equality criterion
used in the source. -/
theorem tangentConic_discriminant_eq_zero_iff
    (parameter : K) (point : Point K)
    (fourParameterNonzero : (4 : K) * parameter ≠ 0)
    (onLemniscate : Contains parameter point)
    (secondOrderNonSingular : IsSecondOrderNonSingularAt parameter point) :
    (tangentConic parameter point secondOrderNonSingular).centerDiscriminant =
        0 ↔
      discriminantValue parameter point = 0 := by
  rw [tangentConic_discriminant_factor parameter point onLemniscate]
  constructor
  · intro productZero
    have negativeFactorNonzero : -((4 : K) * parameter) ≠ 0 := by
      intro negativeZero
      apply fourParameterNonzero
      calc
        (4 : K) * parameter = -(-((4 : K) * parameter)) := by ring1
        _ = 0 := by rw [negativeZero]; ring1
    exact eq_zero_of_nonzero_mul_left negativeFactorNonzero productZero
  · intro valueZero
    rw [valueZero]
    ring1

/-- Exercise 19.5: points on the lemniscate and discriminant conic lying on
the same line through the origin have constant quadrance product.  The
quotient-free constant is `4 Q(O,P) Q(O,R)=A²`. -/
theorem inverse_quadrance_product [Nontrivial K]
    (parameter scale : K) (lemniscatePoint discriminantPoint : Point K)
    (eightNonzero : (8 : K) ≠ 0)
    (onLemniscate : Contains parameter lemniscatePoint)
    (onDiscriminant :
      (discriminantConic parameter eightNonzero).Contains discriminantPoint)
    (sameOriginLine :
      discriminantPoint =
        ⟨scale * lemniscatePoint.x, scale * lemniscatePoint.y⟩) :
    4 * quadrance ⟨0, 0⟩ lemniscatePoint *
        quadrance ⟨0, 0⟩ discriminantPoint = parameter ^ 2 := by
  subst discriminantPoint
  have lemniscateEquation :
      (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 =
        2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
    unfold Contains evaluate at onLemniscate
    calc
      (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 =
          ((lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 -
              2 * parameter *
                (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) +
            2 * parameter *
              (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
        ring1
      _ = 2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
        rw [onLemniscate]
        ring1
  have discriminantEquation :
      8 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) = parameter := by
    unfold Conic.Contains at onDiscriminant
    rw [discriminantConic_evaluate] at onDiscriminant
    unfold discriminantValue at onDiscriminant
    calc
      8 * scale ^ 2 *
            (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) =
          (8 * ((scale * lemniscatePoint.x) ^ 2 -
              (scale * lemniscatePoint.y) ^ 2) - parameter) + parameter := by
        ring1
      _ = parameter := by rw [onDiscriminant]; ring1
  unfold quadrance
  dsimp only
  calc
    4 *
          ((lemniscatePoint.x - 0) ^ 2 +
            (lemniscatePoint.y - 0) ^ 2) *
          (((scale * lemniscatePoint.x - 0) ^ 2) +
            ((scale * lemniscatePoint.y - 0) ^ 2)) =
        4 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 := by ring1
    _ = 4 * scale ^ 2 *
        (2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) := by
      rw [lemniscateEquation]
    _ = parameter *
        (8 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) := by ring1
    _ = parameter ^ 2 := by rw [discriminantEquation]; ring1

end Lemniscate

end DivineProportions
