import DivineProportions.Quadrilaterals.Cyclic
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Theorem 115: the Four point relation

The Euler function is the explicitly expanded three-by-three determinant from
the source.  Its coordinate proof is a direct polynomial identity for four
displayed points in a two-dimensional plane.  Exercises 17.3--17.6 record the
alternative expansion, the finite Cayley--Menger determinant, the quadratic
form of the relation, and the circumquadrance deduction.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

/-- The Euler function `E(Q₁,Q₂,Q₃,P₁,P₂,P₃)`, written as the
explicit three-by-three determinant displayed before Theorem 115. -/
def eulerFunction (q₁ q₂ q₃ p₁ p₂ p₃ : K) : K :=
  determinantThree
    (2 * p₁) (p₁ + p₂ - q₃) (p₁ + p₃ - q₂)
    (p₁ + p₂ - q₃) (2 * p₂) (p₂ + p₃ - q₁)
    (p₁ + p₃ - q₂) (p₂ + p₃ - q₁) (2 * p₃)

/-- The coordinate polynomial underlying the Four point relation.  The point
called `base` is translated to the origin in the source proof; expanding the
quadrances performs that finite translation algebraically. -/
theorem euler_coordinate_identity
    (first second third base : Point K) :
    eulerFunction
      (quadrance second third)
      (quadrance first third)
      (quadrance first second)
      (quadrance first base)
      (quadrance second base)
      (quadrance third base) = 0 := by
  unfold eulerFunction determinantThree quadrance
  ring1

/-- Theorem 115 (Four point relation): the three triangle quadrances and the
three quadrances from any fourth point satisfy Euler's determinant equation. -/
theorem four_point_relation
    (first second third base : Point K) :
    eulerFunction
      (quadrance second third)
      (quadrance first third)
      (quadrance first second)
      (quadrance first base)
      (quadrance second base)
      (quadrance third base) = 0 :=
  euler_coordinate_identity first second third base

/-- Exercise 17.3: the fully expanded symmetric expression for the Euler
function. -/
theorem exercise_17_3 (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ =
      2 * (4 * p₁ * p₂ * p₃ +
        (p₁ + p₂ - q₃) * (p₁ + p₃ - q₂) *
          (p₂ + p₃ - q₁) -
        p₁ * (p₂ + p₃ - q₁) ^ 2 -
        p₂ * (p₁ + p₃ - q₂) ^ 2 -
        p₃ * (p₁ + p₂ - q₃) ^ 2) := by
  unfold eulerFunction determinantThree
  ring1

/-- An explicit four-by-four determinant, expanded along its first row. -/
def determinantFour
    (a₁₁ a₁₂ a₁₃ a₁₄
      a₂₁ a₂₂ a₂₃ a₂₄
      a₃₁ a₃₂ a₃₃ a₃₄
      a₄₁ a₄₂ a₄₃ a₄₄ : K) : K :=
  a₁₁ * determinantThree
      a₂₂ a₂₃ a₂₄ a₃₂ a₃₃ a₃₄ a₄₂ a₄₃ a₄₄ -
    a₁₂ * determinantThree
      a₂₁ a₂₃ a₂₄ a₃₁ a₃₃ a₃₄ a₄₁ a₄₃ a₄₄ +
    a₁₃ * determinantThree
      a₂₁ a₂₂ a₂₄ a₃₁ a₃₂ a₃₄ a₄₁ a₄₂ a₄₄ -
    a₁₄ * determinantThree
      a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ a₄₁ a₄₂ a₄₃

/-- The explicitly expanded five-by-five Cayley--Menger determinant displayed
in Exercise 17.4. -/
def fourPointCayleyMenger (q₁ q₂ q₃ p₁ p₂ p₃ : K) : K :=
  -p₁ * determinantFour
      p₁ q₃ q₂ 1
      p₂ 0 q₁ 1
      p₃ q₁ 0 1
      1 1 1 0 +
    p₂ * determinantFour
      p₁ 0 q₂ 1
      p₂ q₃ q₁ 1
      p₃ q₂ 0 1
      1 1 1 0 -
    p₃ * determinantFour
      p₁ 0 q₃ 1
      p₂ q₃ 0 1
      p₃ q₂ q₁ 1
      1 1 1 0 +
    determinantFour
      p₁ 0 q₃ q₂
      p₂ q₃ 0 q₁
      p₃ q₂ q₁ 0
      1 1 1 1

/-- Exercise 17.4: Euler's three-by-three determinant is the displayed
five-by-five Cayley--Menger determinant. -/
theorem exercise_17_4 (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ =
      fourPointCayleyMenger q₁ q₂ q₃ p₁ p₂ p₃ := by
  unfold eulerFunction fourPointCayleyMenger determinantFour determinantThree
  ring1

/-- The numerator obtained by multiplying Exercise 17.5's centered
quadratic expression by `Q₃`. -/
def fourPointQuadraticNumerator
    (q₁ q₂ q₃ p₁ p₂ p₃ : K) : K :=
  q₃ * (2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂) +
    (q₁ - q₂) * (p₂ - p₁)

/-- The denominator-cleared polynomial identity behind Exercise 17.5. -/
theorem fourPoint_quadratic_identity
    (q₁ q₂ q₃ p₁ p₂ p₃ : K) :
    fourPointQuadraticNumerator q₁ q₂ q₃ p₁ p₂ p₃ ^ 2 -
        archimedesFunction q₁ q₂ q₃ *
          archimedesFunction p₁ p₂ q₃ =
      -2 * q₃ * eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ := by
  unfold fourPointQuadraticNumerator eulerFunction determinantThree
    archimedesFunction
  ring1

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

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

/-- Exercise 17.5, corrected: the printed left side omits the factor `2`
before `P₃` and the division of the whole parenthesis by `2`.  With those
corrections, the Four point relation has the asserted quadratic form. -/
theorem exercise_17_5
    (q₁ q₂ q₃ p₁ p₂ p₃ : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (relation : eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ = 0) :
    ((2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂ +
        (q₁ - q₂) * (p₂ - p₁) / q₃) / 2) ^ 2 =
      archimedesFunction q₁ q₂ q₃ *
          archimedesFunction p₁ p₂ q₃ / (4 * q₃ ^ 2) := by
  let offset := 2 * p₃ - p₁ - p₂ + q₃ - q₁ - q₂
  let cross := (q₁ - q₂) * (p₂ - p₁)
  let rawCentered := offset + cross / q₃
  let centered := rawCentered / 2
  let numerator := fourPointQuadraticNumerator q₁ q₂ q₃ p₁ p₂ p₃
  let denominator := 4 * q₃ ^ 2
  have crossCancel : (cross / q₃) * q₃ = cross :=
    RFAP.ExplicitField.div_mul_cancel cross q₃Nonzero
  have rawCenteredCleared : rawCentered * q₃ = numerator := by
    calc
      rawCentered * q₃ = offset * q₃ + (cross / q₃) * q₃ := by
        unfold rawCentered
        ring1
      _ = offset * q₃ + cross := by rw [crossCancel]
      _ = numerator := by
        unfold numerator fourPointQuadraticNumerator offset cross
        ring1
  have centeredCleared : centered * 2 = rawCentered := by
    exact RFAP.ExplicitField.div_mul_cancel rawCentered twoNonzero
  have factored :=
    fourPoint_quadratic_identity q₁ q₂ q₃ p₁ p₂ p₃
  have numeratorEquation :
      numerator ^ 2 =
        archimedesFunction q₁ q₂ q₃ *
          archimedesFunction p₁ p₂ q₃ := by
    apply sub_eq_zero.mp
    calc
      numerator ^ 2 -
          archimedesFunction q₁ q₂ q₃ *
            archimedesFunction p₁ p₂ q₃ =
        -2 * q₃ * eulerFunction q₁ q₂ q₃ p₁ p₂ p₃ :=
          factored
      _ = 0 := by rw [relation]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    intro fourZero
    apply (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have q₃SquaredNonzero : q₃ ^ 2 ≠ 0 := by
    intro squareZero
    apply (RFAP.ExplicitField.mul_ne_zero q₃Nonzero q₃Nonzero)
    calc
      q₃ * q₃ = q₃ ^ 2 := by ring1
      _ = 0 := squareZero
  have denominatorNonzero : denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero q₃SquaredNonzero
  change centered ^ 2 =
    (archimedesFunction q₁ q₂ q₃ *
      archimedesFunction p₁ p₂ q₃) / denominator
  apply eq_of_mul_eq_mul_right denominatorNonzero
  calc
    centered ^ 2 * denominator =
        ((centered * 2) * q₃) ^ 2 := by
      unfold denominator
      ring1
    _ = (rawCentered * q₃) ^ 2 := by rw [centeredCleared]
    _ = numerator ^ 2 := by rw [rawCenteredCleared]
    _ = archimedesFunction q₁ q₂ q₃ *
        archimedesFunction p₁ p₂ q₃ := numeratorEquation
    _ = (archimedesFunction q₁ q₂ q₃ *
          archimedesFunction p₁ p₂ q₃) / denominator *
        denominator := by
      exact (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

/-- Substituting equal circumquadrances into Euler's function yields twice
the usual circumquadrance residual. -/
theorem eulerFunction_equal_radii (q₁ q₂ q₃ radius : K) :
    eulerFunction q₁ q₂ q₃ radius radius radius =
      2 * (archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃) := by
  unfold eulerFunction determinantThree archimedesFunction
  ring1

/-- The scalar form of Exercise 17.6: Euler's relation with three equal
radii recovers the circumquadrance quotient. -/
theorem exercise_17_6_of_euler_relation
    (q₁ q₂ q₃ radius : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadreaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0)
    (relation : eulerFunction q₁ q₂ q₃ radius radius radius = 0) :
    radius = q₁ * q₂ * q₃ / archimedesFunction q₁ q₂ q₃ := by
  have twiceResidualZero :
      2 * (archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃) = 0 := by
    rw [← eulerFunction_equal_radii]
    exact relation
  have residualZero :
      archimedesFunction q₁ q₂ q₃ * radius -
        q₁ * q₂ * q₃ = 0 :=
    eq_zero_of_mul_eq_zero_left twoNonzero twiceResidualZero
  have productEquation :
      archimedesFunction q₁ q₂ q₃ * radius =
        q₁ * q₂ * q₃ := sub_eq_zero.mp residualZero
  apply eq_of_mul_eq_mul_right quadreaNonzero
  calc
    radius * archimedesFunction q₁ q₂ q₃ =
        archimedesFunction q₁ q₂ q₃ * radius := by ring1
    _ = q₁ * q₂ * q₃ := productEquation
    _ = (q₁ * q₂ * q₃ / archimedesFunction q₁ q₂ q₃) *
        archimedesFunction q₁ q₂ q₃ := by
      exact (RFAP.ExplicitField.div_mul_cancel _ quadreaNonzero).symm

/-- Exercise 17.6 for an explicitly displayed circumcenter: applying the
Four point relation to the center re-derives the triangle circumquadrance
formula without any completed or infinite object. -/
theorem exercise_17_6
    (first second third center : Point K) (radius : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadreaNonzero : quadrea first second third ≠ 0)
    (firstRadius : quadrance first center = radius)
    (secondRadius : quadrance second center = radius)
    (thirdRadius : quadrance third center = radius) :
    radius =
      quadrance second third * quadrance first third *
          quadrance first second / quadrea first second third := by
  have relation := four_point_relation first second third center
  rw [firstRadius, secondRadius, thirdRadius] at relation
  unfold quadrea at quadreaNonzero ⊢
  exact exercise_17_6_of_euler_relation
    (quadrance second third) (quadrance first third)
    (quadrance first second) radius twoNonzero quadreaNonzero relation

end Quadrilateral

end DivineProportions
