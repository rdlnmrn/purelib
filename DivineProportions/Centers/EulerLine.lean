import DivineProportions.Centers.AffineOrthocenter
import DivineProportions.Plane.Medians

/-!
# Divine Proportions, Theorem 116: the Euler line

The centroid is an explicit finite affine combination.  The key identity is
the source's relation `G = (2/3)C + (1/3)O`, proved first for the already
formalized affine circumcenter and orthocenter weights and then transferred to
the geometric center constructions.  No completed line or infinite locus is
introduced: collinearity is the finite three-point determinant relation.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Each pair of the affine center weights satisfies `2αᵢ+βᵢ=1`, the
coefficient identity behind the Euler relation. -/
theorem euler_center_weight_identity
    (q₁ q₂ q₃ : K)
    (areaNonzero : archimedesFunction q₁ q₂ q₃ ≠ 0) :
    2 * affineCircumcenterWeight q₁ q₂ q₃
          (archimedesFunction q₁ q₂ q₃) +
        affineOrthocenterWeight q₁ q₂ q₃
          (archimedesFunction q₁ q₂ q₃) = 1 := by
  have areaCancel :
      archimedesFunction q₁ q₂ q₃ *
          (archimedesFunction q₁ q₂ q₃)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel _ areaNonzero
  unfold affineCircumcenterWeight affineOrthocenterWeight
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    2 * (q₁ * (q₂ + q₃ - q₁) *
          (archimedesFunction q₁ q₂ q₃)⁻¹) +
        (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) *
          (archimedesFunction q₁ q₂ q₃)⁻¹ =
      archimedesFunction q₁ q₂ q₃ *
        (archimedesFunction q₁ q₂ q₃)⁻¹ := by
          unfold archimedesFunction
          ring1
    _ = 1 := areaCancel

/-- The affine relation among the three finite center formulas. -/
theorem euler_affine_center_relation
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    affineCombination ((2 : K) / 3)
        (affineCircumcenterPoint first second third)
        ((1 : K) / 3)
        (affineOrthocenterPoint first second third) =
      centroidPoint first second third := by
  let q₁ := quadrance second third
  let q₂ := quadrance first third
  let q₃ := quadrance first second
  let area := quadrea first second third
  let c₁ := affineCircumcenterWeight q₁ q₂ q₃ area
  let c₂ := affineCircumcenterWeight q₂ q₃ q₁ area
  let c₃ := affineCircumcenterWeight q₃ q₁ q₂ area
  let o₁ := affineOrthocenterWeight q₁ q₂ q₃ area
  let o₂ := affineOrthocenterWeight q₂ q₃ q₁ area
  let o₃ := affineOrthocenterWeight q₃ q₁ q₂ area
  have areaNonzero : area ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have firstWeight : 2 * c₁ + o₁ = 1 := by
    unfold c₁ o₁ area quadrea q₁ q₂ q₃
    exact euler_center_weight_identity
      (quadrance second third) (quadrance first third)
      (quadrance first second) areaNonzero
  have secondWeight : 2 * c₂ + o₂ = 1 := by
    unfold c₂ o₂ area quadrea q₁ q₂ q₃
    have rotatedArea :
        archimedesFunction (quadrance first third)
            (quadrance first second) (quadrance second third) =
          archimedesFunction (quadrance second third)
            (quadrance first third) (quadrance first second) := by
      unfold archimedesFunction
      ring1
    have rotatedAreaNonzero :
        archimedesFunction (quadrance first third)
          (quadrance first second) (quadrance second third) ≠ 0 := by
      rw [rotatedArea]
      exact areaNonzero
    have result := euler_center_weight_identity
      (quadrance first third) (quadrance first second)
      (quadrance second third) rotatedAreaNonzero
    rw [rotatedArea] at result
    exact result
  have thirdWeight : 2 * c₃ + o₃ = 1 := by
    unfold c₃ o₃ area quadrea q₁ q₂ q₃
    have rotatedArea :
        archimedesFunction (quadrance first second)
            (quadrance second third) (quadrance first third) =
          archimedesFunction (quadrance second third)
            (quadrance first third) (quadrance first second) := by
      unfold archimedesFunction
      ring1
    have rotatedAreaNonzero :
        archimedesFunction (quadrance first second)
          (quadrance second third) (quadrance first third) ≠ 0 := by
      rw [rotatedArea]
      exact areaNonzero
    have result := euler_center_weight_identity
      (quadrance first second) (quadrance second third)
      (quadrance first third) rotatedAreaNonzero
    rw [rotatedArea] at result
    exact result
  apply Point.ext
  · change
      (2 / 3 : K) * (c₁ * first.x + c₂ * second.x + c₃ * third.x) +
          (1 / 3 : K) *
            (o₁ * first.x + o₂ * second.x + o₃ * third.x) =
        (first.x + second.x + third.x) / 3
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (3 : K)⁻¹ *
            (c₁ * first.x + c₂ * second.x + c₃ * third.x) +
          (1 * (3 : K)⁻¹) *
            (o₁ * first.x + o₂ * second.x + o₃ * third.x) =
        (3 : K)⁻¹ *
          ((2 * c₁ + o₁) * first.x +
            (2 * c₂ + o₂) * second.x +
            (2 * c₃ + o₃) * third.x) := by ring1
      _ = (3 : K)⁻¹ * (first.x + second.x + third.x) := by
        rw [firstWeight, secondWeight, thirdWeight]
        ring1
      _ = (first.x + second.x + third.x) * (3 : K)⁻¹ := by ring1
  · change
      (2 / 3 : K) * (c₁ * first.y + c₂ * second.y + c₃ * third.y) +
          (1 / 3 : K) *
            (o₁ * first.y + o₂ * second.y + o₃ * third.y) =
        (first.y + second.y + third.y) / 3
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (3 : K)⁻¹ *
            (c₁ * first.y + c₂ * second.y + c₃ * third.y) +
          (1 * (3 : K)⁻¹) *
            (o₁ * first.y + o₂ * second.y + o₃ * third.y) =
        (3 : K)⁻¹ *
          ((2 * c₁ + o₁) * first.y +
            (2 * c₂ + o₂) * second.y +
            (2 * c₃ + o₃) * third.y) := by ring1
      _ = (3 : K)⁻¹ * (first.y + second.y + third.y) := by
        rw [firstWeight, secondWeight, thirdWeight]
        ring1
      _ = (first.y + second.y + third.y) * (3 : K)⁻¹ := by ring1

/-- The source's affine Euler relation for the actual constructed centers. -/
theorem euler_center_relation
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    affineCombination ((2 : K) / 3)
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        ((1 : K) / 3)
        (orthocenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) =
      centroidPoint first second third := by
  rw [affine_circumcenter first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [affine_orthocenter first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  exact euler_affine_center_relation first second third notCollinear
    twoNonzero

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

/-- The denominator-cleared coordinate form `2C+O=A₁+A₂+A₃`.  Unlike
the divided centroid relation, this identity remains meaningful in
characteristic three. -/
theorem euler_center_cleared_coordinates
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let circumcenter :=
      circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    2 * circumcenter.x + orthocenter.x = first.x + second.x + third.x ∧
      2 * circumcenter.y + orthocenter.y = first.y + second.y + third.y := by
  dsimp only
  rw [circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let denominator := antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  let circumcenterX := circumcenterXNumerator first second third
  let circumcenterY := circumcenterYNumerator first second third
  let orthocenterX := orthocenterXNumerator first second third
  let orthocenterY := orthocenterYNumerator first second third
  have denominatorEqualsDeterminant :
      denominator = pointDeterminant first second third := by
    exact (pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have denominatorNonzero : denominator ≠ 0 := by
    rw [denominatorEqualsDeterminant]
    intro determinantZero
    apply notCollinear
    exact (collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have twiceDenominatorNonzero : 2 * denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  constructor
  · change 2 * (circumcenterX / (2 * denominator)) +
        orthocenterX / denominator = first.x + second.x + third.x
    apply eq_of_mul_eq_mul_right twiceDenominatorNonzero
    calc
      (2 * (circumcenterX / (2 * denominator)) +
          orthocenterX / denominator) * (2 * denominator) =
        2 * ((circumcenterX / (2 * denominator)) * (2 * denominator)) +
          2 * ((orthocenterX / denominator) * denominator) := by ring1
      _ = 2 * circumcenterX + 2 * orthocenterX := by
        rw [RFAP.ExplicitField.div_mul_cancel circumcenterX
            twiceDenominatorNonzero,
          RFAP.ExplicitField.div_mul_cancel orthocenterX denominatorNonzero]
      _ = (first.x + second.x + third.x) * (2 * denominator) := by
        unfold circumcenterX orthocenterX denominator
          circumcenterXNumerator orthocenterXNumerator
          antisymmetricTripleProduct
        ring1
  · change 2 * (circumcenterY / (2 * denominator)) +
        orthocenterY / denominator = first.y + second.y + third.y
    apply eq_of_mul_eq_mul_right twiceDenominatorNonzero
    calc
      (2 * (circumcenterY / (2 * denominator)) +
          orthocenterY / denominator) * (2 * denominator) =
        2 * ((circumcenterY / (2 * denominator)) * (2 * denominator)) +
          2 * ((orthocenterY / denominator) * denominator) := by ring1
      _ = 2 * circumcenterY + 2 * orthocenterY := by
        rw [RFAP.ExplicitField.div_mul_cancel circumcenterY
            twiceDenominatorNonzero,
          RFAP.ExplicitField.div_mul_cancel orthocenterY denominatorNonzero]
      _ = (first.y + second.y + third.y) * (2 * denominator) := by
        unfold circumcenterY orthocenterY denominator
          circumcenterYNumerator orthocenterYNumerator
          antisymmetricTripleProduct
        ring1

/-- Any two displayed points and an affine combination with weights summing
to one are collinear, including the case where the first two points coincide. -/
theorem collinear_affineCombination
    [Nontrivial K] [DecidableEq K]
    (first second : Point K) (leftWeight rightWeight : K)
    (weightsSum : leftWeight + rightWeight = 1) :
    Collinear first second
      (affineCombination leftWeight first rightWeight second) := by
  apply (collinear_iff_pointDeterminant_eq_zero first second
    (affineCombination leftWeight first rightWeight second)).2
  unfold pointDeterminant
  change
    first.x * second.y -
          first.x * (leftWeight * first.y + rightWeight * second.y) +
        second.x * (leftWeight * first.y + rightWeight * second.y) -
          (leftWeight * first.x + rightWeight * second.x) * second.y +
        (leftWeight * first.x + rightWeight * second.x) * first.y -
      second.x * first.y = 0
  calc
    first.x * second.y -
          first.x * (leftWeight * first.y + rightWeight * second.y) +
        second.x * (leftWeight * first.y + rightWeight * second.y) -
          (leftWeight * first.x + rightWeight * second.x) * second.y +
        (leftWeight * first.x + rightWeight * second.x) * first.y -
          second.x * first.y =
      (leftWeight + rightWeight - 1) *
        (second.x * first.y - first.x * second.y) := by ring1
    _ = 0 := by rw [weightsSum]; ring1

/-- Theorem 116 (Euler line): outside characteristics two and three, the
circumcenter, orthocenter, and centroid of a noncollinear triangle are
collinear. -/
theorem euler_line
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    Collinear
      (circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      (orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      (centroidPoint first second third) := by
  have weightsSum : (2 / 3 : K) + 1 / 3 = 1 := by
    apply eq_of_mul_eq_mul_right threeNonzero
    calc
      ((2 / 3 : K) + 1 / 3) * 3 =
          (2 / 3 : K) * 3 + (1 / 3 : K) * 3 := by ring1
      _ = 2 + 1 := by
        rw [RFAP.ExplicitField.div_mul_cancel 2 threeNonzero,
          RFAP.ExplicitField.div_mul_cancel 1 threeNonzero]
      _ = 1 * 3 := by ring1
  have centersCollinear := collinear_affineCombination
    (circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    (orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    ((2 : K) / 3) ((1 : K) / 3) weightsSum
  rw [euler_center_relation first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero] at centersCollinear
  exact centersCollinear

/-- Multiplying the centroid coordinates by three recovers the coordinate
sums, with the nonzero characteristic-three premise made explicit. -/
theorem centroidPoint_scaled_coordinates
    (first second third : Point K) (threeNonzero : (3 : K) ≠ 0) :
    (centroidPoint first second third).x * 3 =
        first.x + second.x + third.x ∧
      (centroidPoint first second third).y * 3 =
        first.y + second.y + third.y := by
  constructor
  · unfold centroidPoint
    exact RFAP.ExplicitField.div_mul_cancel _ threeNonzero
  · unfold centroidPoint
    exact RFAP.ExplicitField.div_mul_cancel _ threeNonzero

/-- The first centroid quadrance-difference identity used in Exercise 18.1. -/
theorem centroid_quadrance_difference_first_second
    (first second third : Point K) (threeNonzero : (3 : K) ≠ 0) :
    3 * (quadrance (centroidPoint first second third) first -
        quadrance (centroidPoint first second third) second) =
      quadrance first third - quadrance second third := by
  have scaled := centroidPoint_scaled_coordinates first second third
    threeNonzero
  calc
    3 * (quadrance (centroidPoint first second third) first -
          quadrance (centroidPoint first second third) second) =
      (first.x - second.x) *
          (3 * (first.x + second.x) -
            2 * ((centroidPoint first second third).x * 3)) +
        (first.y - second.y) *
          (3 * (first.y + second.y) -
            2 * ((centroidPoint first second third).y * 3)) := by
              unfold quadrance
              ring1
    _ = quadrance first third - quadrance second third := by
      rw [scaled.1, scaled.2]
      unfold quadrance
      ring1

/-- The second cyclic centroid quadrance-difference identity. -/
theorem centroid_quadrance_difference_second_third
    (first second third : Point K) (threeNonzero : (3 : K) ≠ 0) :
    3 * (quadrance (centroidPoint first second third) second -
        quadrance (centroidPoint first second third) third) =
      quadrance first second - quadrance first third := by
  have scaled := centroidPoint_scaled_coordinates first second third
    threeNonzero
  calc
    3 * (quadrance (centroidPoint first second third) second -
          quadrance (centroidPoint first second third) third) =
      (second.x - third.x) *
          (3 * (second.x + third.x) -
            2 * ((centroidPoint first second third).x * 3)) +
        (second.y - third.y) *
          (3 * (second.y + third.y) -
            2 * ((centroidPoint first second third).y * 3)) := by
              unfold quadrance
              ring1
    _ = quadrance first second - quadrance first third := by
      rw [scaled.1, scaled.2]
      unfold quadrance
      ring1

/-- A triangle is equilateral when its three finite quadrances agree. -/
def IsEquilateralTriangle (first second third : Point K) : Prop :=
  quadrance second third = quadrance first third ∧
    quadrance first third = quadrance first second

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

private theorem points_equal_of_euler_affine_fixed
    (fixed other : Point K) (threeNonzero : (3 : K) ≠ 0)
    (relation :
      affineCombination ((2 : K) / 3) fixed ((1 : K) / 3) other = fixed) :
    fixed = other := by
  have xRelation := congrArg Point.x relation
  have yRelation := congrArg Point.y relation
  change ((2 : K) / 3) * fixed.x + ((1 : K) / 3) * other.x =
    fixed.x at xRelation
  change ((2 : K) / 3) * fixed.y + ((1 : K) / 3) * other.y =
    fixed.y at yRelation
  have twoCancel : ((2 : K) / 3) * 3 = 2 :=
    RFAP.ExplicitField.div_mul_cancel 2 threeNonzero
  have oneCancel : ((1 : K) / 3) * 3 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 threeNonzero
  apply Point.ext
  · have cleared : 2 * fixed.x + other.x = fixed.x * 3 := by
      calc
        2 * fixed.x + other.x =
            (((2 : K) / 3) * 3) * fixed.x +
              (((1 : K) / 3) * 3) * other.x := by
                rw [twoCancel, oneCancel]
                ring1
        _ = (((2 : K) / 3) * fixed.x +
              ((1 : K) / 3) * other.x) * 3 := by ring1
        _ = fixed.x * 3 := by rw [xRelation]
    calc
      fixed.x = fixed.x * 3 - 2 * fixed.x := by ring1
      _ = other.x := by rw [← cleared]; ring1
  · have cleared : 2 * fixed.y + other.y = fixed.y * 3 := by
      calc
        2 * fixed.y + other.y =
            (((2 : K) / 3) * 3) * fixed.y +
              (((1 : K) / 3) * 3) * other.y := by
                rw [twoCancel, oneCancel]
                ring1
        _ = (((2 : K) / 3) * fixed.y +
              ((1 : K) / 3) * other.y) * 3 := by ring1
        _ = fixed.y * 3 := by rw [yRelation]
    calc
      fixed.y = fixed.y * 3 - 2 * fixed.y := by ring1
      _ = other.y := by rw [← cleared]; ring1

/-- Exercise 18.1: the centroid, circumcenter, and orthocenter coincide
precisely for an equilateral noncollinear triangle. -/
theorem exercise_18_1
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    let centroid := centroidPoint first second third
    let circumcenter :=
      circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    (centroid = circumcenter ∧ centroid = orthocenter) ↔
      IsEquilateralTriangle first second third := by
  dsimp only
  let centroid := centroidPoint first second third
  let circumcenter :=
    circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let orthocenter :=
    orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  have centerFacts := DivineProportions.circumcenter first second third firstSecondDistinct
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  dsimp only at centerFacts
  constructor
  · rintro ⟨centroidIsCircumcenter, _centroidIsOrthocenter⟩
    have firstSecondRadii :
        quadrance centroid first = quadrance centroid second := by
      unfold centroid
      rw [centroidIsCircumcenter]
      exact centerFacts.2.2.2.1
    have secondThirdRadii :
        quadrance centroid second = quadrance centroid third := by
      unfold centroid
      rw [centroidIsCircumcenter]
      exact centerFacts.2.2.2.2
    have firstDifference :=
      centroid_quadrance_difference_first_second first second third
        threeNonzero
    have secondDifference :=
      centroid_quadrance_difference_second_third first second third
        threeNonzero
    have firstQuadrances :
        quadrance first third = quadrance second third := by
      apply sub_eq_zero.mp
      calc
        quadrance first third - quadrance second third =
            3 * (quadrance centroid first - quadrance centroid second) :=
          firstDifference.symm
        _ = 0 := by rw [firstSecondRadii]; ring1
    have secondQuadrances :
        quadrance first second = quadrance first third := by
      apply sub_eq_zero.mp
      calc
        quadrance first second - quadrance first third =
            3 * (quadrance centroid second - quadrance centroid third) :=
          secondDifference.symm
        _ = 0 := by rw [secondThirdRadii]; ring1
    exact ⟨firstQuadrances.symm, secondQuadrances.symm⟩
  · intro equilateral
    have firstDifference :=
      centroid_quadrance_difference_first_second first second third
        threeNonzero
    have secondDifference :=
      centroid_quadrance_difference_second_third first second third
        threeNonzero
    have firstDifferenceZero :
        quadrance centroid first - quadrance centroid second = 0 := by
      apply eq_zero_of_mul_eq_zero_left threeNonzero
      calc
        3 * (quadrance centroid first - quadrance centroid second) =
            quadrance first third - quadrance second third := firstDifference
        _ = 0 := by rw [equilateral.1]; ring1
    have secondDifferenceZero :
        quadrance centroid second - quadrance centroid third = 0 := by
      apply eq_zero_of_mul_eq_zero_left threeNonzero
      calc
        3 * (quadrance centroid second - quadrance centroid third) =
            quadrance first second - quadrance first third := secondDifference
        _ = 0 := by rw [← equilateral.2]; ring1
    have firstSecondRadii :
        quadrance centroid first = quadrance centroid second :=
      sub_eq_zero.mp firstDifferenceZero
    have secondThirdRadii :
        quadrance centroid second = quadrance centroid third :=
      sub_eq_zero.mp secondDifferenceZero
    have onSecondThird :
        (perpendicularBisector second third secondThirdDistinct).Contains
          centroid :=
      (equal_quadrance_iff_perpendicularBisector_contains second third
        centroid secondThirdDistinct twoNonzero).1 secondThirdRadii
    have onFirstThird :
        (perpendicularBisector first third firstThirdDistinct).Contains
          centroid :=
      (equal_quadrance_iff_perpendicularBisector_contains first third
        centroid firstThirdDistinct twoNonzero).1
        (firstSecondRadii.trans secondThirdRadii)
    have centroidIsCircumcenter : centroid = circumcenter := by
      unfold circumcenter circumcenterPoint
      exact lineIntersection_unique
        (perpendicularBisector second third secondThirdDistinct)
        (perpendicularBisector first third firstThirdDistinct)
        (circumcenter_bisectors_not_parallel first second third
          firstThirdDistinct secondThirdDistinct notCollinear)
        centroid onSecondThird onFirstThird
    have relation := euler_center_relation first second third
      firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
    change affineCombination ((2 : K) / 3) circumcenter ((1 : K) / 3)
      orthocenter = centroid at relation
    rw [← centroidIsCircumcenter] at relation
    have centroidIsOrthocenter : centroid = orthocenter :=
      points_equal_of_euler_affine_fixed centroid orthocenter threeNonzero
        relation
    exact ⟨centroidIsCircumcenter, centroidIsOrthocenter⟩

end DivineProportions
