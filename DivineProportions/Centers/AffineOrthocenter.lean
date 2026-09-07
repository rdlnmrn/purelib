import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.OrthocenterFormula

/-!
# Divine Proportions, §12.4: the affine orthocenter

The cyclic beta weights are executable rational expressions in the three
quadrances and quadrea.  Their sum-to-one identity is proved separately, then
coordinate cross-products identify their affine combination with the
orthocenter formula of Theorem 86.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- One cyclic weight
`(Qₖ+Qᵢ-Qⱼ)(Qᵢ+Qⱼ-Qₖ)/𝒜` from Theorem 87. -/
def affineOrthocenterWeight
    (current next previous area : K) : K :=
  (previous + current - next) * (current + next - previous) / area

/-- The three beta weights sum to one.  This is also the specialization of
the source's Exercise 5.15 used in the printed proof. -/
theorem affine_orthocenter_weights_sum
    [Nontrivial K]
    (q₁ q₂ q₃ : K)
    (areaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0) :
    affineOrthocenterWeight q₁ q₂ q₃
        (archimedesFunction q₁ q₂ q₃) +
      affineOrthocenterWeight q₂ q₃ q₁
        (archimedesFunction q₁ q₂ q₃) +
      affineOrthocenterWeight q₃ q₁ q₂
        (archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      archimedesFunction q₁ q₂ q₃ *
          (archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold affineOrthocenterWeight
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) *
          (archimedesFunction q₁ q₂ q₃)⁻¹ +
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) *
          (archimedesFunction q₁ q₂ q₃)⁻¹ +
        (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) *
          (archimedesFunction q₁ q₂ q₃)⁻¹ =
      archimedesFunction q₁ q₂ q₃ *
        (archimedesFunction q₁ q₂ q₃)⁻¹ := by
          unfold archimedesFunction
          ring1
    _ = 1 := areaCancel

/-- The affine point displayed in Theorem 87. -/
def affineOrthocenterPoint (first second third : Point K) : Point K :=
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  affineCombinationThree
    (affineOrthocenterWeight q₁ q₂ q₃ area) first
    (affineOrthocenterWeight q₂ q₃ q₁ area) second
    (affineOrthocenterWeight q₃ q₁ q₂ area) third

/-- The weights defining `affineOrthocenterPoint` really are affine. -/
theorem affineOrthocenterPoint_weights_sum
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let q₁ := quadrance second third
    let q₂ := quadrance first third
    let q₃ := quadrance first second
    let area := quadrea first second third
    affineOrthocenterWeight q₁ q₂ q₃ area +
      affineOrthocenterWeight q₂ q₃ q₁ area +
      affineOrthocenterWeight q₃ q₁ q₂ area = 1 := by
  dsimp only
  have areaNonzero : quadrea first second third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  unfold quadrea at areaNonzero ⊢
  exact affine_orthocenter_weights_sum
    (quadrance second third) (quadrance first third)
    (quadrance first second) areaNonzero

/-- Theorem 87 (Affine orthocenter). -/
theorem affine_orthocenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      affineOrthocenterPoint first second third := by
  rw [orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let determinant := pointDeterminant first second third
  let xNumerator := orthocenterXNumerator first second third
  let yNumerator := orthocenterYNumerator first second third
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  let weightedX :=
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) * first.x +
      (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * second.x +
      (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) * third.x
  let weightedY :=
    (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) * first.y +
      (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) * second.y +
      (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) * third.y
  have determinantNonzero : determinant ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have areaNonzero : area ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have antisymmetricDenominator :
      antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y =
        determinant := by
    exact (pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have formulaDenominatorNonzero :
      antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact determinantNonzero
  have affineX : (affineOrthocenterPoint first second third).x =
      weightedX / area := by
    unfold affineOrthocenterPoint affineCombinationThree
      affineOrthocenterWeight weightedX q₁ q₂ q₃ area
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have affineY : (affineOrthocenterPoint first second third).y =
      weightedY / area := by
    unfold affineOrthocenterPoint affineCombinationThree
      affineOrthocenterWeight weightedY q₁ q₂ q₃ area
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have xCross :
      xNumerator * area =
        weightedX *
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    rw [antisymmetricDenominator]
    unfold area
    rw [quadrea_coordinate_formula first second third]
    unfold weightedX xNumerator orthocenterXNumerator
      antisymmetricTripleProduct q₁ q₂ q₃ quadrance determinant
      pointDeterminant
    ring1
  have yCross :
      yNumerator * area =
        weightedY *
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    rw [antisymmetricDenominator]
    unfold area
    rw [quadrea_coordinate_formula first second third]
    unfold weightedY yNumerator orthocenterYNumerator
      antisymmetricTripleProduct q₁ q₂ q₃ quadrance determinant
      pointDeterminant
    ring1
  apply Point.ext
  · change
      xNumerator /
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y =
        (affineOrthocenterPoint first second third).x
    rw [affineX]
    exact ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      xCross
  · change
      yNumerator /
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y =
        (affineOrthocenterPoint first second third).y
    rw [affineY]
    exact ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      yCross

end DivineProportions
