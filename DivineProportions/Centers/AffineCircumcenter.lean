import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.CircumcenterFormula

/-!
# Divine Proportions, §12.2: the affine circumcenter

The three weights below are exactly the cyclic quadrance expressions printed
in Theorem 84.  Their normalization is a finite Archimedes-polynomial
identity.  Coordinate cross-multiplication then identifies the weighted point
with the antisymmetric formula of Theorem 83.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- One cyclic weight `Qᵢ(Qⱼ+Qₖ-Qᵢ)/𝒜` from Theorem 84. -/
def affineCircumcenterWeight
    (opposite adjacentOne adjacentTwo area : K) : K :=
  opposite * (adjacentOne + adjacentTwo - opposite) / area

/-- The three weights sum to one; this is also the content of the source's
Exercise 5.14 specialized to the triangle quadrea. -/
theorem affine_circumcenter_weights_sum
    [Nontrivial K]
    (q₁ q₂ q₃ : K)
    (areaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0) :
    affineCircumcenterWeight q₁ q₂ q₃
        (archimedesFunction q₁ q₂ q₃) +
      affineCircumcenterWeight q₂ q₃ q₁
        (archimedesFunction q₁ q₂ q₃) +
      affineCircumcenterWeight q₃ q₁ q₂
        (archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      archimedesFunction q₁ q₂ q₃ *
          (archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold affineCircumcenterWeight
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    q₁ * (q₂ + q₃ - q₁) * (archimedesFunction q₁ q₂ q₃)⁻¹ +
          q₂ * (q₃ + q₁ - q₂) * (archimedesFunction q₁ q₂ q₃)⁻¹ +
          q₃ * (q₁ + q₂ - q₃) * (archimedesFunction q₁ q₂ q₃)⁻¹ =
        archimedesFunction q₁ q₂ q₃ *
          (archimedesFunction q₁ q₂ q₃)⁻¹ := by
            unfold archimedesFunction
            ring1
    _ = 1 := areaCancel

/-- The affine point displayed in Theorem 84. -/
def affineCircumcenterPoint (first second third : Point K) : Point K :=
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  affineCombinationThree
    (affineCircumcenterWeight q₁ q₂ q₃ area) first
    (affineCircumcenterWeight q₂ q₃ q₁ area) second
    (affineCircumcenterWeight q₃ q₁ q₂ area) third

/-- The weights defining `affineCircumcenterPoint` really are affine. -/
theorem affineCircumcenterPoint_weights_sum
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let q₁ := quadrance second third
    let q₂ := quadrance first third
    let q₃ := quadrance first second
    let area := quadrea first second third
    affineCircumcenterWeight q₁ q₂ q₃ area +
      affineCircumcenterWeight q₂ q₃ q₁ area +
      affineCircumcenterWeight q₃ q₁ q₂ area = 1 := by
  dsimp only
  have areaNonzero : quadrea first second third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  unfold quadrea at areaNonzero ⊢
  exact affine_circumcenter_weights_sum
    (quadrance second third) (quadrance first third)
    (quadrance first second) areaNonzero

/-- Theorem 84 (Affine circumcenter). -/
theorem affine_circumcenter
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      affineCircumcenterPoint first second third := by
  rw [circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  let determinant := pointDeterminant first second third
  let xNumerator := circumcenterXNumerator first second third
  let yNumerator := circumcenterYNumerator first second third
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  let weightedX :=
    q₁ * (q₂ + q₃ - q₁) * first.x +
      q₂ * (q₃ + q₁ - q₂) * second.x +
      q₃ * (q₁ + q₂ - q₃) * third.x
  let weightedY :=
    q₁ * (q₂ + q₃ - q₁) * first.y +
      q₂ * (q₃ + q₁ - q₂) * second.y +
      q₃ * (q₁ + q₂ - q₃) * third.y
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
      2 * antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero determinantNonzero
  have affineX : (affineCircumcenterPoint first second third).x =
      weightedX / area := by
    unfold affineCircumcenterPoint affineCombinationThree
      affineCircumcenterWeight weightedX q₁ q₂ q₃ area
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have affineY : (affineCircumcenterPoint first second third).y =
      weightedY / area := by
    unfold affineCircumcenterPoint affineCombinationThree
      affineCircumcenterWeight weightedY q₁ q₂ q₃ area
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have xCross :
      xNumerator * area =
        weightedX *
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    rw [antisymmetricDenominator]
    unfold area
    rw [quadrea_coordinate_formula first second third]
    unfold weightedX xNumerator circumcenterXNumerator
      antisymmetricTripleProduct q₁ q₂ q₃ quadrance determinant
      pointDeterminant
    ring1
  have yCross :
      yNumerator * area =
        weightedY *
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    rw [antisymmetricDenominator]
    unfold area
    rw [quadrea_coordinate_formula first second third]
    unfold weightedY yNumerator circumcenterYNumerator
      antisymmetricTripleProduct q₁ q₂ q₃ quadrance determinant
      pointDeterminant
    ring1
  apply Point.ext
  · change
      xNumerator /
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) =
        (affineCircumcenterPoint first second third).x
    rw [affineX]
    exact ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      xCross
  · change
      yNumerator /
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) =
        (affineCircumcenterPoint first second third).y
    rw [affineY]
    exact ratio_eq_of_cross_product formulaDenominatorNonzero areaNonzero
      yCross

end DivineProportions
