import DivineProportions.Plane.Medians
import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, Chapter 5 triangle exercises

The centroid calculation is reduced to two finite affine-scaling identities.
All divisions retain explicit characteristic-two and characteristic-three
certificates.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem quadrance_affineCombination_left
    (left right : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    quadrance left
        (affineCombination leftWeight left rightWeight right) =
      rightWeight ^ 2 * quadrance left right := by
  have leftWeightFormula : leftWeight = 1 - rightWeight := by
    calc
      leftWeight = (leftWeight + rightWeight) - rightWeight := by ring1
      _ = 1 - rightWeight := by rw [weightsSum]
  rw [leftWeightFormula]
  unfold quadrance affineCombination
  ring1

private theorem quadrance_affineCombination_right
    (left right : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    quadrance
        (affineCombination leftWeight left rightWeight right) right =
      leftWeight ^ 2 * quadrance left right := by
  have rightWeightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weightsSum]
  rw [rightWeightFormula]
  unfold quadrance affineCombination
  ring1

/-- Exercise 5.2: the centroid divides a median in the exact quadrance ratios
`4/9` and `1/9`, and hence the vertex--centroid quadrance is four times the
centroid--midpoint quadrance. -/
theorem exercise_5_2
    (first second third : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    let oppositeMidpoint := midpoint second third
    let centroid := centroidPoint first second third
    quadrance first centroid =
        4 * quadrance first oppositeMidpoint / 9 ∧
      quadrance centroid oppositeMidpoint =
        quadrance first oppositeMidpoint / 9 ∧
      quadrance first centroid =
        4 * quadrance centroid oppositeMidpoint := by
  dsimp only
  have threeCancel : (3 : K) * (3 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 3 threeNonzero
  have nineNonzero : (9 : K) ≠ 0 := by
    intro nineZero
    apply (RFAP.ExplicitField.mul_ne_zero threeNonzero threeNonzero)
    calc
      (3 : K) * 3 = 9 := by ring1
      _ = 0 := nineZero
  have nineCancel : (9 : K) * (9 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 9 nineNonzero
  have inverseSquare : ((3 : K)⁻¹) ^ 2 = (9 : K)⁻¹ := by
    calc
      ((3 : K)⁻¹) ^ 2 =
          ((3 : K)⁻¹) ^ 2 * (9 * (9 : K)⁻¹) := by
            rw [nineCancel]
            ring1
      _ = (3 * (3 : K)⁻¹) ^ 2 * (9 : K)⁻¹ := by ring1
      _ = (9 : K)⁻¹ := by rw [threeCancel]; ring1
  have weightsSum : (1 : K) / 3 + 2 / 3 = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 * (3 : K)⁻¹ + 2 * (3 : K)⁻¹ =
          3 * (3 : K)⁻¹ := by ring1
      _ = 1 := threeCancel
  have centroidFormula := centroidPoint_eq_median_affineCombination
    first second third twoNonzero
  have firstScaled :
      quadrance first (centroidPoint first second third) =
        ((2 : K) / 3) ^ 2 * quadrance first (midpoint second third) := by
    rw [centroidFormula]
    exact quadrance_affineCombination_left first (midpoint second third)
      ((1 : K) / 3) (2 / 3) weightsSum
  have secondScaled :
      quadrance (centroidPoint first second third) (midpoint second third) =
        ((1 : K) / 3) ^ 2 * quadrance first (midpoint second third) := by
    rw [centroidFormula]
    exact quadrance_affineCombination_right first (midpoint second third)
      ((1 : K) / 3) (2 / 3) weightsSum
  have fourNinths : ((2 : K) / 3) ^ 2 = 4 / 9 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (2 * (3 : K)⁻¹) ^ 2 = 4 * ((3 : K)⁻¹) ^ 2 := by ring1
      _ = 4 * (9 : K)⁻¹ := by rw [inverseSquare]
  have oneNinth : ((1 : K) / 3) ^ 2 = 1 / 9 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (1 * (3 : K)⁻¹) ^ 2 = 1 * ((3 : K)⁻¹) ^ 2 := by ring1
      _ = 1 * (9 : K)⁻¹ := by rw [inverseSquare]
  have firstResult :
      quadrance first (centroidPoint first second third) =
        4 * quadrance first (midpoint second third) / 9 := by
    calc
      quadrance first (centroidPoint first second third) =
          ((2 : K) / 3) ^ 2 *
            quadrance first (midpoint second third) := firstScaled
      _ = 4 * quadrance first (midpoint second third) / 9 := by
        rw [fourNinths]
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  have secondResult :
      quadrance (centroidPoint first second third) (midpoint second third) =
        quadrance first (midpoint second third) / 9 := by
    calc
      quadrance (centroidPoint first second third) (midpoint second third) =
          ((1 : K) / 3) ^ 2 *
            quadrance first (midpoint second third) := secondScaled
      _ = quadrance first (midpoint second third) / 9 := by
        rw [oneNinth]
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  exact ⟨firstResult, secondResult,
    firstResult.trans (by
      rw [secondResult]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1)⟩

end DivineProportions
