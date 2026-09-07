import DivineProportions.Quadrilaterals.Circumquadrance
import DivineProportions.Oriented.SignedArea

/-!
# Divine Proportions, Theorem 112: cyclic quadrilateral quadrea

The source obtains the quadrea equation through two diagonal quotients and a
long circumquadrance elimination.  The finite polynomial underneath is much
shorter: for any four displayed points, the difference between the requested
quadrea polynomial and zero is `-64` times the square of their circle
determinant.  Cyclicity therefore proves Theorem 112 directly, without the
source's solvability and nonzero-product assumptions.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

/-- The coefficient `m` in Theorem 112. -/
def cyclicQuadreaCoefficientM (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ + q₂₃ + q₃₄ + q₁₄) ^ 2 -
    2 * (q₁₂ ^ 2 + q₂₃ ^ 2 + q₃₄ ^ 2 + q₁₄ ^ 2)

/-- The direct four-point identity behind Theorem 112.  It also quantifies
the failure of the quadrea equation away from cyclicity. -/
theorem cyclicQuadrea_polynomial_identity
    (first second third fourth : Point K) :
    let area := polygonQuadrea [first, second, third, fourth]
    let q₁₂ := quadrance first second
    let q₂₃ := quadrance second third
    let q₃₄ := quadrance third fourth
    let q₁₄ := quadrance first fourth
    area ^ 2 -
        2 * cyclicQuadreaCoefficientM q₁₂ q₂₃ q₃₄ q₁₄ * area +
        circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ =
      -64 * coordinateCircleDeterminant first second third fourth ^ 2 := by
  dsimp only
  simp only [polygonQuadrea, polygonDoubleSignedArea,
    polygonDoubleSignedAreaAux, positionDeterminant]
  unfold cyclicQuadreaCoefficientM circumquadranceCoefficientP
    quadrupleQuadFunction coordinateCircleDeterminant circleRowNorm
    determinantThree quadrance
  ring1

/-- Theorem 112 (Cyclic quadrilateral quadrea), strengthened: every displayed
cyclic quadrilateral satisfies the equation, with no solvability or nonzero
coefficient assumptions. -/
theorem cyclic_quadrilateral_quadrea
    (quadrilateral : Quadrilateral K) (cyclic : quadrilateral.IsCyclic) :
    let area := polygonQuadrea [quadrilateral.first, quadrilateral.second,
      quadrilateral.third, quadrilateral.fourth]
    let q₁₂ := quadrance quadrilateral.first quadrilateral.second
    let q₂₃ := quadrance quadrilateral.second quadrilateral.third
    let q₃₄ := quadrance quadrilateral.third quadrilateral.fourth
    let q₁₄ := quadrance quadrilateral.first quadrilateral.fourth
    area ^ 2 -
        2 * cyclicQuadreaCoefficientM q₁₂ q₂₃ q₃₄ q₁₄ * area +
        circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ = 0 := by
  dsimp only
  have determinantZero :=
    coordinateCircleDeterminant_eq_zero_of_isCyclic quadrilateral cyclic
  calc
    polygonQuadrea [quadrilateral.first, quadrilateral.second,
          quadrilateral.third, quadrilateral.fourth] ^ 2 -
        2 * cyclicQuadreaCoefficientM
          (quadrance quadrilateral.first quadrilateral.second)
          (quadrance quadrilateral.second quadrilateral.third)
          (quadrance quadrilateral.third quadrilateral.fourth)
          (quadrance quadrilateral.first quadrilateral.fourth) *
          polygonQuadrea [quadrilateral.first, quadrilateral.second,
            quadrilateral.third, quadrilateral.fourth] +
        circumquadranceCoefficientP
          (quadrance quadrilateral.first quadrilateral.second)
          (quadrance quadrilateral.second quadrilateral.third)
          (quadrance quadrilateral.third quadrilateral.fourth)
          (quadrance quadrilateral.first quadrilateral.fourth) =
      -64 * coordinateCircleDeterminant quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth ^ 2 :=
      cyclicQuadrea_polynomial_identity quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth
    _ = 0 := by rw [determinantZero]; ring1

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

/-- The two distinct quadrea roots have the average and product stated after
Theorem 112. -/
theorem cyclicQuadrea_roots_vieta
    (firstArea secondArea m p : K)
    (twoNonzero : (2 : K) ≠ 0)
    (areasDistinct : firstArea ≠ secondArea)
    (firstRoot : firstArea ^ 2 - 2 * m * firstArea + p = 0)
    (secondRoot : secondArea ^ 2 - 2 * m * secondArea + p = 0) :
    (firstArea + secondArea) / 2 = m ∧
      firstArea * secondArea = p := by
  have differenceNonzero : firstArea - secondArea ≠ 0 := by
    intro differenceZero
    apply areasDistinct
    exact sub_eq_zero.mp differenceZero
  have factoredDifference :
      (firstArea - secondArea) *
        (firstArea + secondArea - 2 * m) = 0 := by
    calc
      (firstArea - secondArea) *
          (firstArea + secondArea - 2 * m) =
        (firstArea ^ 2 - 2 * m * firstArea + p) -
          (secondArea ^ 2 - 2 * m * secondArea + p) := by ring1
      _ = 0 := by rw [firstRoot, secondRoot]; ring1
  have sumDifferenceZero : firstArea + secondArea - 2 * m = 0 :=
    eq_zero_of_mul_eq_zero_left differenceNonzero factoredDifference
  have sumEquation : firstArea + secondArea = 2 * m :=
    sub_eq_zero.mp sumDifferenceZero
  constructor
  · apply eq_of_mul_eq_mul_right twoNonzero
    calc
      ((firstArea + secondArea) / 2) * 2 = firstArea + secondArea :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
      _ = 2 * m := sumEquation
      _ = m * 2 := by ring1
  · calc
      firstArea * secondArea =
          firstArea * (2 * m - firstArea) := by rw [← sumEquation]; ring1
      _ = p - (firstArea ^ 2 - 2 * m * firstArea + p) := by ring1
      _ = p := by rw [firstRoot]; ring1

end Quadrilateral

end DivineProportions
