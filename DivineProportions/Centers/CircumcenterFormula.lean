import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.ExtendedSpread

/-!
# Divine Proportions, §12.2: the circumcenter formula

The source abbreviates its coordinate numerators with the six-term
antisymmetric bracket `[uv]⁻₁₂₃`.  We expose that polynomial directly and use
it to define the printed circumcenter.  The proof compares its two fractions
with the explicit intersection of two perpendicular bisectors.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The book's six-term antisymmetric product `[uv]⁻₁₂₃`. -/
def antisymmetricTripleProduct
    (u₁ u₂ u₃ v₁ v₂ v₃ : K) : K :=
  u₁ * v₂ - u₁ * v₃ + u₂ * v₃ - u₃ * v₂ +
    u₃ * v₁ - u₂ * v₁

/-- The coordinate determinant is the basic antisymmetric product `[xy]⁻`. -/
theorem pointDeterminant_eq_antisymmetricTripleProduct
    (first second third : Point K) :
    pointDeterminant first second third =
      antisymmetricTripleProduct
        first.x second.x third.x first.y second.y third.y := by
  unfold pointDeterminant antisymmetricTripleProduct
  ring1

/-- The numerator `[x²y]⁻ + [y²y]⁻` of the printed x-coordinate. -/
def circumcenterXNumerator (first second third : Point K) : K :=
  antisymmetricTripleProduct
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2)
      first.y second.y third.y +
    antisymmetricTripleProduct
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)
      first.y second.y third.y

/-- The numerator `[xx²]⁻ + [xy²]⁻` of the printed y-coordinate. -/
def circumcenterYNumerator (first second third : Point K) : K :=
  antisymmetricTripleProduct
      first.x second.x third.x
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2) +
    antisymmetricTripleProduct
      first.x second.x third.x
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)

/-- The point displayed in Theorem 83. -/
def circumcenterFormula (first second third : Point K) : Point K :=
  let denominator := 2 * antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨circumcenterXNumerator first second third / denominator,
    circumcenterYNumerator first second third / denominator⟩

private theorem neg_ne_zero_of_ne_zero {value : K} (nonzero : value ≠ 0) :
    -value ≠ 0 := by
  intro negativeZero
  apply nonzero
  calc
    value = -(-value) := by ring1
    _ = 0 := by rw [negativeZero]; ring1

/-- Theorem 83 (Circumcenter formula).  The right side is exactly the pair of
antisymmetric quotients printed in the source. -/
theorem circumcenter_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      circumcenterFormula first second third := by
  let determinant := pointDeterminant first second third
  let xNumerator := circumcenterXNumerator first second third
  let yNumerator := circumcenterYNumerator first second third
  let firstBisector := perpendicularBisector second third secondThirdDistinct
  let secondBisector := perpendicularBisector first third firstThirdDistinct
  have determinantNonzero : determinant ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have negativeDeterminantNonzero : -determinant ≠ 0 :=
    neg_ne_zero_of_ne_zero determinantNonzero
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
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have intersectionDenominator :
      firstBisector.a * secondBisector.b -
          secondBisector.a * firstBisector.b = -determinant := by
    unfold firstBisector secondBisector perpendicularBisector determinant
      pointDeterminant
    ring1
  have intersectionXNumerator :
      firstBisector.b * secondBisector.c -
          secondBisector.b * firstBisector.c = -xNumerator / 2 := by
    unfold firstBisector secondBisector perpendicularBisector xNumerator
      circumcenterXNumerator antisymmetricTripleProduct
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have intersectionYNumerator :
      firstBisector.c * secondBisector.a -
          secondBisector.c * firstBisector.a = -yNumerator / 2 := by
    unfold firstBisector secondBisector perpendicularBisector yNumerator
      circumcenterYNumerator antisymmetricTripleProduct
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have xRatio :
      (-xNumerator / 2) / (-determinant) =
        xNumerator /
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    apply ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-xNumerator * (2 : K)⁻¹) * (2 * determinant) =
          -xNumerator * ((2 : K) * (2 : K)⁻¹) * determinant := by ring1
      _ = xNumerator * -determinant := by rw [twoCancel]; ring1
  have yRatio :
      (-yNumerator / 2) / (-determinant) =
        yNumerator /
          (2 * antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    apply ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-yNumerator * (2 : K)⁻¹) * (2 * determinant) =
          -yNumerator * ((2 : K) * (2 : K)⁻¹) * determinant := by ring1
      _ = yNumerator * -determinant := by rw [twoCancel]; ring1
  unfold circumcenterPoint
  change lineIntersection firstBisector secondBisector
      (circumcenter_bisectors_not_parallel first second third
        firstThirdDistinct secondThirdDistinct notCollinear) =
    circumcenterFormula first second third
  apply Point.ext
  · unfold lineIntersection circumcenterFormula
    dsimp only
    rw [intersectionXNumerator, intersectionDenominator]
    exact xRatio
  · unfold lineIntersection circumcenterFormula
    dsimp only
    rw [intersectionYNumerator, intersectionDenominator]
    exact yRatio

end DivineProportions
