import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Centers.Orthocenter

/-!
# Divine Proportions, §12.4: the orthocenter formula

The two numerators below are the source's antisymmetric brackets
`[x₁x₂y₂]⁻ + [y₁y₂²]⁻` and
`[x₁y₁y₂]⁻ + [x₁²x₂]⁻`.  Each is written with the reusable six-term
antisymmetric product introduced for Theorem 83.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The printed x-numerator `[x₁x₂y₂]⁻ + [y₁y₂²]⁻`. -/
def orthocenterXNumerator (first second third : Point K) : K :=
  antisymmetricTripleProduct
      first.x second.x third.x
      (first.x * first.y) (second.x * second.y) (third.x * third.y) +
    antisymmetricTripleProduct
      first.y second.y third.y
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)

/-- The printed y-numerator `[x₁y₁y₂]⁻ + [x₁²x₂]⁻`. -/
def orthocenterYNumerator (first second third : Point K) : K :=
  antisymmetricTripleProduct
      (first.x * first.y) (second.x * second.y) (third.x * third.y)
      first.y second.y third.y +
    antisymmetricTripleProduct
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2)
      first.x second.x third.x

/-- The point displayed in Theorem 86. -/
def orthocenterFormula (first second third : Point K) : Point K :=
  let denominator := antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨orthocenterXNumerator first second third / denominator,
    orthocenterYNumerator first second third / denominator⟩

private theorem neg_ne_zero_of_ne_zero {value : K} (nonzero : value ≠ 0) :
    -value ≠ 0 := by
  intro negativeZero
  apply nonzero
  calc
    value = -(-value) := by ring1
    _ = 0 := by rw [negativeZero]; ring1

/-- Theorem 86 (Orthocenter formula). -/
theorem orthocenter_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      orthocenterFormula first second third := by
  let determinant := pointDeterminant first second third
  let xNumerator := orthocenterXNumerator first second third
  let yNumerator := orthocenterYNumerator first second third
  let firstAltitude :=
    triangleAltitudeFromFirst first second third secondThirdDistinct
  let secondAltitude :=
    triangleAltitudeFromSecond first second third firstThirdDistinct
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
      antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact determinantNonzero
  have intersectionDenominator :
      firstAltitude.a * secondAltitude.b -
          secondAltitude.a * firstAltitude.b = -determinant := by
    unfold firstAltitude secondAltitude triangleAltitudeFromFirst
      triangleAltitudeFromSecond altitudeThrough lineThrough determinant
      pointDeterminant
    ring1
  have intersectionXNumerator :
      firstAltitude.b * secondAltitude.c -
          secondAltitude.b * firstAltitude.c = -xNumerator := by
    unfold firstAltitude secondAltitude triangleAltitudeFromFirst
      triangleAltitudeFromSecond altitudeThrough lineThrough xNumerator
      orthocenterXNumerator antisymmetricTripleProduct
    ring1
  have intersectionYNumerator :
      firstAltitude.c * secondAltitude.a -
          secondAltitude.c * firstAltitude.a = -yNumerator := by
    unfold firstAltitude secondAltitude triangleAltitudeFromFirst
      triangleAltitudeFromSecond altitudeThrough lineThrough yNumerator
      orthocenterYNumerator antisymmetricTripleProduct
    ring1
  have xRatio :
      (-xNumerator) / (-determinant) =
        xNumerator /
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    apply ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    ring1
  have yRatio :
      (-yNumerator) / (-determinant) =
        yNumerator /
          antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    apply ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    ring1
  unfold orthocenterPoint
  change lineIntersection firstAltitude secondAltitude
      (triangle_altitudes_not_parallel first second third
        firstThirdDistinct secondThirdDistinct notCollinear) =
    orthocenterFormula first second third
  apply Point.ext
  · unfold lineIntersection orthocenterFormula
    dsimp only
    rw [intersectionXNumerator, intersectionDenominator]
    exact xRatio
  · unfold lineIntersection orthocenterFormula
    dsimp only
    rw [intersectionYNumerator, intersectionDenominator]
    exact yRatio

end DivineProportions
