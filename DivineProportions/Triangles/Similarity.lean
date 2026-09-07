import DivineProportions.Trigonometry.TriangleRatios

/-!
# Divine Proportions, §10.4: congruent and similar triangles

The source compares the three quadrances or spreads without prescribing which
side of one triangle corresponds to which side of the other.  `SameEntries`
therefore records the six possible matches explicitly.  This is a finite
replacement for quotienting triples by permutations or constructing a
multiset.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Three displayed scalar entries. -/
@[ext]
structure ScalarTriple (K : Type*) where
  first : K
  second : K
  third : K

namespace ScalarTriple

/-- The six finite ways in which two triples can have identical entries.
Repeated entries may of course admit more than one constructor. -/
inductive SameEntries (left right : ScalarTriple K) : Prop
  | abc (first : left.first = right.first)
      (second : left.second = right.second)
      (third : left.third = right.third)
  | acb (first : left.first = right.first)
      (second : left.second = right.third)
      (third : left.third = right.second)
  | bac (first : left.first = right.second)
      (second : left.second = right.first)
      (third : left.third = right.third)
  | bca (first : left.first = right.second)
      (second : left.second = right.third)
      (third : left.third = right.first)
  | cab (first : left.first = right.third)
      (second : left.second = right.first)
      (third : left.third = right.second)
  | cba (first : left.first = right.third)
      (second : left.second = right.second)
      (third : left.third = right.first)

/-- Multiply all three displayed entries by one scalar. -/
def scale (factor : K) (entries : ScalarTriple K) : ScalarTriple K :=
  ⟨factor * entries.first, factor * entries.second, factor * entries.third⟩

/-- The three denominator products in the Quadrea--spread identities. -/
def spreadDenominators (entries : ScalarTriple K) : ScalarTriple K :=
  ⟨4 * entries.second * entries.third,
    4 * entries.first * entries.third,
    4 * entries.first * entries.second⟩

/-- Archimedes' symmetric polynomial evaluated on the three entries. -/
def archimedesValue (entries : ScalarTriple K) : K :=
  archimedesFunction entries.first entries.second entries.third

theorem archimedesValue_eq_of_sameEntries
    {left right : ScalarTriple K} (same : SameEntries left right) :
    left.archimedesValue = right.archimedesValue := by
  rcases same with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  all_goals
    (unfold archimedesValue archimedesFunction
     rw [first, second, third] <;> ring1)

/-- Permuting three entries permutes the three complementary products in the
same way. -/
theorem spreadDenominators_sameEntries
    {left right : ScalarTriple K} (same : SameEntries left right) :
    SameEntries left.spreadDenominators right.spreadDenominators := by
  rcases same with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply SameEntries.abc
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]
  · apply SameEntries.acb
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]
  · apply SameEntries.bac
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]
  · apply SameEntries.bca
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]
  · apply SameEntries.cab
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]
  · apply SameEntries.cba
    all_goals
      simp only [spreadDenominators, first, second, third, mul_comm, mul_left_comm]

end ScalarTriple

/-- The three side quadrances, indexed by their opposite vertices. -/
def triangleQuadrances (first second third : Point K) : ScalarTriple K :=
  ⟨quadrance second third, quadrance first third, quadrance first second⟩

/-- The book's definition of congruence: equality of the unordered triple of
side quadrances.  No choice of a corresponding side is hidden in the
definition. -/
def CongruentTriangles
    (first second third otherFirst otherSecond otherThird : Point K) : Prop :=
  ScalarTriple.SameEntries
    (triangleQuadrances first second third)
    (triangleQuadrances otherFirst otherSecond otherThird)

/-- A genuine non-null triangle supplies exactly the finite data needed to
form all three vertex spreads. -/
structure NonNullTriangle (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] where
  first : Point K
  second : Point K
  third : Point K
  notCollinear : ¬ Collinear first second third
  firstSecondDistinct : first ≠ second
  firstThirdDistinct : first ≠ third
  secondThirdDistinct : second ≠ third
  firstSecondNonNull :
    ¬ (lineThrough first second firstSecondDistinct).IsNull
  firstThirdNonNull :
    ¬ (lineThrough first third firstThirdDistinct).IsNull
  secondThirdNonNull :
    ¬ (lineThrough second third secondThirdDistinct).IsNull

namespace NonNullTriangle

variable [DecidableEq K]

theorem firstSecondReversedNonNull (triangle : NonNullTriangle K) :
    ¬ (lineThrough triangle.second triangle.first
      triangle.firstSecondDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.firstSecondNonNull
  apply (null_line_iff_quadrance_zero triangle.first triangle.second
    triangle.firstSecondDistinct).2
  calc
    quadrance triangle.first triangle.second =
        quadrance triangle.second triangle.first :=
      quadrance_symm triangle.first triangle.second
    _ = 0 :=
      (null_line_iff_quadrance_zero triangle.second triangle.first
        triangle.firstSecondDistinct.symm).1 reversedNull

theorem firstThirdReversedNonNull (triangle : NonNullTriangle K) :
    ¬ (lineThrough triangle.third triangle.first
      triangle.firstThirdDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.firstThirdNonNull
  apply (null_line_iff_quadrance_zero triangle.first triangle.third
    triangle.firstThirdDistinct).2
  calc
    quadrance triangle.first triangle.third =
        quadrance triangle.third triangle.first :=
      quadrance_symm triangle.first triangle.third
    _ = 0 :=
      (null_line_iff_quadrance_zero triangle.third triangle.first
        triangle.firstThirdDistinct.symm).1 reversedNull

theorem secondThirdReversedNonNull (triangle : NonNullTriangle K) :
    ¬ (lineThrough triangle.third triangle.second
      triangle.secondThirdDistinct.symm).IsNull := by
  intro reversedNull
  apply triangle.secondThirdNonNull
  apply (null_line_iff_quadrance_zero triangle.second triangle.third
    triangle.secondThirdDistinct).2
  calc
    quadrance triangle.second triangle.third =
        quadrance triangle.third triangle.second :=
      quadrance_symm triangle.second triangle.third
    _ = 0 :=
      (null_line_iff_quadrance_zero triangle.third triangle.second
        triangle.secondThirdDistinct.symm).1 reversedNull

/-- The three spreads at the first, second, and third vertices. -/
def spreads (triangle : NonNullTriangle K) : ScalarTriple K :=
  ⟨spread
      (lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct)
      (lineThrough triangle.first triangle.third
        triangle.firstThirdDistinct)
      triangle.firstSecondNonNull triangle.firstThirdNonNull,
    spread
      (lineThrough triangle.second triangle.first
        triangle.firstSecondDistinct.symm)
      (lineThrough triangle.second triangle.third
        triangle.secondThirdDistinct)
      triangle.firstSecondReversedNonNull triangle.secondThirdNonNull,
    spread
      (lineThrough triangle.third triangle.first
        triangle.firstThirdDistinct.symm)
      (lineThrough triangle.third triangle.second
        triangle.secondThirdDistinct.symm)
      triangle.firstThirdReversedNonNull
      triangle.secondThirdReversedNonNull⟩

/-- The three side quadrances of a non-null triangle. -/
def quadrances (triangle : NonNullTriangle K) : ScalarTriple K :=
  triangleQuadrances triangle.first triangle.second triangle.third

/-- The book's definition of similarity: equality of the unordered triple of
vertex spreads. -/
def Similar (left right : NonNullTriangle K) : Prop :=
  ScalarTriple.SameEntries left.spreads right.spreads

/-- Congruence specialized to the vertices stored by two non-null triangles. -/
def Congruent (left right : NonNullTriangle K) : Prop :=
  CongruentTriangles left.first left.second left.third
    right.first right.second right.third

theorem firstQuadranceNonzero (triangle : NonNullTriangle K) :
    triangle.quadrances.first ≠ 0 := by
  intro quadranceZero
  apply triangle.secondThirdNonNull
  apply (null_line_iff_quadrance_zero triangle.second triangle.third
    triangle.secondThirdDistinct).2
  exact quadranceZero

theorem secondQuadranceNonzero (triangle : NonNullTriangle K) :
    triangle.quadrances.second ≠ 0 := by
  intro quadranceZero
  apply triangle.firstThirdNonNull
  apply (null_line_iff_quadrance_zero triangle.first triangle.third
    triangle.firstThirdDistinct).2
  exact quadranceZero

theorem thirdQuadranceNonzero (triangle : NonNullTriangle K) :
    triangle.quadrances.third ≠ 0 := by
  intro quadranceZero
  apply triangle.firstSecondNonNull
  apply (null_line_iff_quadrance_zero triangle.first triangle.second
    triangle.firstSecondDistinct).2
  exact quadranceZero

/-- Reversing both point orders negates both line representatives and hence
does not change their spread. -/
theorem spread_lineThrough_reverse_both
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (firstSecondNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull) :
    spread
        (lineThrough first second firstSecondDistinct)
        (lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      spread
        (lineThrough second first firstSecondDistinct.symm)
        (lineThrough third first firstThirdDistinct.symm)
        (by
          intro reversedNull
          apply firstSecondNonNull
          apply (null_line_iff_quadrance_zero first second
            firstSecondDistinct).2
          calc
            quadrance first second = quadrance second first :=
              quadrance_symm first second
            _ = 0 :=
              (null_line_iff_quadrance_zero second first
                firstSecondDistinct.symm).1 reversedNull)
        (by
          intro reversedNull
          apply firstThirdNonNull
          apply (null_line_iff_quadrance_zero first third
            firstThirdDistinct).2
          calc
            quadrance first third = quadrance third first :=
              quadrance_symm first third
            _ = 0 :=
              (null_line_iff_quadrance_zero third first
                firstThirdDistinct.symm).1 reversedNull) := by
  unfold spread lineNorm lineThrough
  congr 1 <;> ring1

/-- Reversing both displayed representatives does not change their spread. -/
theorem firstSpread_eq_reversed (triangle : NonNullTriangle K) :
    triangle.spreads.first =
      spread
        (lineThrough triangle.second triangle.first
          triangle.firstSecondDistinct.symm)
        (lineThrough triangle.third triangle.first
          triangle.firstThirdDistinct.symm)
        triangle.firstSecondReversedNonNull
        triangle.firstThirdReversedNonNull := by
  exact spread_lineThrough_reverse_both triangle.first triangle.second
    triangle.third triangle.firstSecondDistinct
    triangle.firstThirdDistinct triangle.firstSecondNonNull
    triangle.firstThirdNonNull

/-- The three denominator-cleared Quadrea--spread identities, packaged in the
same opposite-vertex order as `quadrances` and `spreads`. -/
theorem quadrea_spread_products (triangle : NonNullTriangle K) :
    quadrea triangle.first triangle.second triangle.third =
        triangle.quadrances.spreadDenominators.first *
          triangle.spreads.first ∧
      quadrea triangle.first triangle.second triangle.third =
        triangle.quadrances.spreadDenominators.second *
          triangle.spreads.second ∧
      quadrea triangle.first triangle.second triangle.third =
        triangle.quadrances.spreadDenominators.third *
          triangle.spreads.third := by
  have firstArea := quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm triangle.firstSecondReversedNonNull
    triangle.firstThirdReversedNonNull
  rw [quadrea_cyclic triangle.first triangle.second triangle.third,
    quadrance_symm triangle.third triangle.first,
    quadrance_symm triangle.second triangle.first,
    ← spread_lineThrough_reverse_both triangle.first triangle.second
      triangle.third triangle.firstSecondDistinct
      triangle.firstThirdDistinct triangle.firstSecondNonNull
      triangle.firstThirdNonNull] at firstArea
  have secondArea := quadrea_spread triangle.first triangle.third
    triangle.second triangle.firstSecondDistinct
    triangle.secondThirdDistinct.symm triangle.firstSecondNonNull
    triangle.secondThirdReversedNonNull
  rw [quadrea_swap_second_third triangle.first triangle.second triangle.third,
    quadrance_symm triangle.third triangle.second,
    ← spread_lineThrough_reverse_both triangle.second triangle.first
      triangle.third triangle.firstSecondDistinct.symm
      triangle.secondThirdDistinct triangle.firstSecondReversedNonNull
      triangle.secondThirdNonNull] at secondArea
  have thirdArea := quadrea_spread triangle.first triangle.second
    triangle.third triangle.firstThirdDistinct
    triangle.secondThirdDistinct triangle.firstThirdNonNull
    triangle.secondThirdNonNull
  rw [← spread_lineThrough_reverse_both triangle.third triangle.first
      triangle.second triangle.firstThirdDistinct.symm
      triangle.secondThirdDistinct.symm triangle.firstThirdReversedNonNull
      triangle.secondThirdReversedNonNull] at thirdArea
  change quadrea triangle.first triangle.second triangle.third =
    triangle.quadrances.spreadDenominators.first *
      triangle.spreads.first at firstArea
  change quadrea triangle.first triangle.second triangle.third =
    triangle.quadrances.spreadDenominators.second *
      triangle.spreads.second at secondArea
  change quadrea triangle.first triangle.second triangle.third =
    triangle.quadrances.spreadDenominators.third *
      triangle.spreads.third at thirdArea
  exact ⟨firstArea, secondArea, thirdArea⟩

theorem spreadDenominatorsNonzero (triangle : NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) :
    triangle.quadrances.spreadDenominators.first ≠ 0 ∧
      triangle.quadrances.spreadDenominators.second ≠ 0 ∧
      triangle.quadrances.spreadDenominators.third ≠ 0 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  exact ⟨
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero
        triangle.secondQuadranceNonzero)
      triangle.thirdQuadranceNonzero,
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero
        triangle.firstQuadranceNonzero)
      triangle.thirdQuadranceNonzero,
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero
        triangle.firstQuadranceNonzero)
      triangle.secondQuadranceNonzero⟩

theorem firstSpreadNonzero [Nontrivial K] (triangle : NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) : triangle.spreads.first ≠ 0 := by
  have areaNonzero : quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third twoNonzero).2 triangle.notCollinear
  have areaAtFirst := quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm triangle.firstSecondReversedNonNull
    triangle.firstThirdReversedNonNull
  rw [quadrea_cyclic triangle.first triangle.second triangle.third] at areaAtFirst
  rw [← triangle.firstSpread_eq_reversed] at areaAtFirst
  intro spreadZero
  apply areaNonzero
  calc
    quadrea triangle.first triangle.second triangle.third =
        4 * quadrance triangle.third triangle.first *
          quadrance triangle.second triangle.first *
            triangle.spreads.first := areaAtFirst
    _ = 0 := by rw [spreadZero]; ring1

/-- The common value in the Spread law. -/
def commonSpreadRatio (triangle : NonNullTriangle K) : K :=
  triangle.spreads.first / triangle.quadrances.first

theorem spreadRatioLaws (triangle : NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) :
    triangle.commonSpreadRatio =
        triangle.spreads.second / triangle.quadrances.second ∧
      triangle.spreads.second / triangle.quadrances.second =
        triangle.spreads.third / triangle.quadrances.third := by
  change
    spread
          (lineThrough triangle.first triangle.second
            triangle.firstSecondDistinct)
          (lineThrough triangle.first triangle.third
            triangle.firstThirdDistinct)
          triangle.firstSecondNonNull triangle.firstThirdNonNull /
        quadrance triangle.second triangle.third =
      spread
          (lineThrough triangle.second triangle.first
            triangle.firstSecondDistinct.symm)
          (lineThrough triangle.second triangle.third
            triangle.secondThirdDistinct)
          triangle.firstSecondReversedNonNull
          triangle.secondThirdNonNull /
        quadrance triangle.first triangle.third ∧
      spread
          (lineThrough triangle.second triangle.first
            triangle.firstSecondDistinct.symm)
          (lineThrough triangle.second triangle.third
            triangle.secondThirdDistinct)
          triangle.firstSecondReversedNonNull
          triangle.secondThirdNonNull /
        quadrance triangle.first triangle.third =
      spread
          (lineThrough triangle.third triangle.first
            triangle.firstThirdDistinct.symm)
          (lineThrough triangle.third triangle.second
            triangle.secondThirdDistinct.symm)
          triangle.firstThirdReversedNonNull
          triangle.secondThirdReversedNonNull /
        quadrance triangle.first triangle.second
  exact spread_law triangle.first triangle.second triangle.third
    triangle.firstSecondDistinct triangle.firstThirdDistinct
    triangle.secondThirdDistinct triangle.firstSecondNonNull
    triangle.firstThirdNonNull triangle.secondThirdNonNull twoNonzero

theorem spreads_eq_commonRatio_mul_quadrances
    (triangle : NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0) :
    triangle.spreads.first =
        triangle.commonSpreadRatio * triangle.quadrances.first ∧
      triangle.spreads.second =
        triangle.commonSpreadRatio * triangle.quadrances.second ∧
      triangle.spreads.third =
        triangle.commonSpreadRatio * triangle.quadrances.third := by
  have laws := triangle.spreadRatioLaws twoNonzero
  constructor
  · exact (RFAP.ExplicitField.div_mul_cancel triangle.spreads.first
      triangle.firstQuadranceNonzero).symm
  constructor
  · calc
      triangle.spreads.second =
          (triangle.spreads.second / triangle.quadrances.second) *
            triangle.quadrances.second :=
        (RFAP.ExplicitField.div_mul_cancel triangle.spreads.second
          triangle.secondQuadranceNonzero).symm
      _ = triangle.commonSpreadRatio * triangle.quadrances.second := by
        rw [← laws.1]
  · calc
      triangle.spreads.third =
          (triangle.spreads.third / triangle.quadrances.third) *
            triangle.quadrances.third :=
        (RFAP.ExplicitField.div_mul_cancel triangle.spreads.third
          triangle.thirdQuadranceNonzero).symm
      _ = triangle.commonSpreadRatio * triangle.quadrances.third := by
        rw [← laws.2, ← laws.1]

theorem commonSpreadRatioNonzero [Nontrivial K]
    (triangle : NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) : triangle.commonSpreadRatio ≠ 0 := by
  exact RFAP.ExplicitField.div_ne_zero
    (triangle.firstSpreadNonzero twoNonzero)
    triangle.firstQuadranceNonzero

omit [DecidableEq K] in
private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

/-- The source's observation following the definition of similarity:
congruent non-null triangles are similar. -/
theorem congruent_triangles_are_similar
    (left right : NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0)
    (congruent : left.Congruent right) : left.Similar right := by
  have quadrancesSame :
      ScalarTriple.SameEntries left.quadrances right.quadrances :=
    congruent
  have denominatorsSame :=
    ScalarTriple.spreadDenominators_sameEntries quadrancesSame
  have areaEqual :
      quadrea left.first left.second left.third =
        quadrea right.first right.second right.third := by
    change left.quadrances.archimedesValue =
      right.quadrances.archimedesValue
    exact ScalarTriple.archimedesValue_eq_of_sameEntries quadrancesSame
  have leftProducts := left.quadrea_spread_products
  have rightProducts := right.quadrea_spread_products
  have leftDenominatorsNonzero := left.spreadDenominatorsNonzero twoNonzero
  have spreadEqual
      (leftDenominator rightDenominator leftSpread rightSpread : K)
      (leftDenominatorNonzero : leftDenominator ≠ 0)
      (leftProduct :
        quadrea left.first left.second left.third =
          leftDenominator * leftSpread)
      (rightProduct :
        quadrea right.first right.second right.third =
          rightDenominator * rightSpread)
      (denominatorsEqual : leftDenominator = rightDenominator) :
      leftSpread = rightSpread := by
    apply eq_of_mul_eq_mul_left leftDenominatorNonzero
    calc
      leftDenominator * leftSpread =
          quadrea left.first left.second left.third := leftProduct.symm
      _ = quadrea right.first right.second right.third := areaEqual
      _ = rightDenominator * rightSpread := rightProduct
      _ = leftDenominator * rightSpread := by rw [denominatorsEqual]
  unfold Similar
  rcases denominatorsSame with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply ScalarTriple.SameEntries.abc
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.2 third
  · apply ScalarTriple.SameEntries.acb
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.2 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.1 third
  · apply ScalarTriple.SameEntries.bac
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.2 third
  · apply ScalarTriple.SameEntries.bca
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.1 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.2 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.1 third
  · apply ScalarTriple.SameEntries.cab
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.2 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.2.1 third
  · apply ScalarTriple.SameEntries.cba
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.1
        leftProducts.1 rightProducts.2.2 first
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.1
        leftProducts.2.1 rightProducts.2.1 second
    · exact spreadEqual _ _ _ _ leftDenominatorsNonzero.2.2
        leftProducts.2.2 rightProducts.1 third

omit [DecidableEq K] in
private theorem quadrance_scale_of_equal_spread
    (leftRatio rightRatio leftSpread rightSpread leftQuadrance
      rightQuadrance : K)
    (leftRatioNonzero : leftRatio ≠ 0)
    (leftFactor : leftSpread = leftRatio * leftQuadrance)
    (rightFactor : rightSpread = rightRatio * rightQuadrance)
    (spreadsEqual : leftSpread = rightSpread) :
    leftQuadrance = (rightRatio / leftRatio) * rightQuadrance := by
  apply eq_of_mul_eq_mul_left leftRatioNonzero
  calc
    leftRatio * leftQuadrance = leftSpread := leftFactor.symm
    _ = rightSpread := spreadsEqual
    _ = rightRatio * rightQuadrance := rightFactor
    _ = ((rightRatio / leftRatio) * leftRatio) * rightQuadrance := by
      rw [RFAP.ExplicitField.div_mul_cancel rightRatio leftRatioNonzero]
    _ = leftRatio *
        ((rightRatio / leftRatio) * rightQuadrance) := by ring1

/-- Exercise 10.9.  Similar non-null, noncollinear triangles have quadrance
triples differing by one explicit nonzero scale.  The matching remains one of
the same six finite side permutations used by the similarity witness. -/
theorem exercise_10_9 [Nontrivial K] (left right : NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) (similar : left.Similar right) :
    ∃ factor : K, factor ≠ 0 ∧
      ScalarTriple.SameEntries left.quadrances
        (ScalarTriple.scale factor right.quadrances) := by
  let factor := right.commonSpreadRatio / left.commonSpreadRatio
  have leftRatioNonzero := left.commonSpreadRatioNonzero twoNonzero
  have rightRatioNonzero := right.commonSpreadRatioNonzero twoNonzero
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero rightRatioNonzero leftRatioNonzero
  have leftFactors := left.spreads_eq_commonRatio_mul_quadrances twoNonzero
  have rightFactors := right.spreads_eq_commonRatio_mul_quadrances twoNonzero
  have entryScale (leftSpread rightSpread leftQuadrance rightQuadrance : K)
      (leftFactor : leftSpread = left.commonSpreadRatio * leftQuadrance)
      (rightFactor : rightSpread = right.commonSpreadRatio * rightQuadrance)
      (spreadsEqual : leftSpread = rightSpread) :
      leftQuadrance = factor * rightQuadrance := by
    exact quadrance_scale_of_equal_spread left.commonSpreadRatio
      right.commonSpreadRatio leftSpread rightSpread leftQuadrance
      rightQuadrance leftRatioNonzero leftFactor rightFactor spreadsEqual
  refine ⟨factor, factorNonzero, ?_⟩
  rcases similar with
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩
  · apply ScalarTriple.SameEntries.abc
    · exact entryScale left.spreads.first right.spreads.first
        left.quadrances.first right.quadrances.first leftFactors.1
        rightFactors.1 first
    · exact entryScale left.spreads.second right.spreads.second
        left.quadrances.second right.quadrances.second leftFactors.2.1
        rightFactors.2.1 second
    · exact entryScale left.spreads.third right.spreads.third
        left.quadrances.third right.quadrances.third leftFactors.2.2
        rightFactors.2.2 third
  · apply ScalarTriple.SameEntries.acb
    · exact entryScale left.spreads.first right.spreads.first
        left.quadrances.first right.quadrances.first leftFactors.1
        rightFactors.1 first
    · exact entryScale left.spreads.second right.spreads.third
        left.quadrances.second right.quadrances.third leftFactors.2.1
        rightFactors.2.2 second
    · exact entryScale left.spreads.third right.spreads.second
        left.quadrances.third right.quadrances.second leftFactors.2.2
        rightFactors.2.1 third
  · apply ScalarTriple.SameEntries.bac
    · exact entryScale left.spreads.first right.spreads.second
        left.quadrances.first right.quadrances.second leftFactors.1
        rightFactors.2.1 first
    · exact entryScale left.spreads.second right.spreads.first
        left.quadrances.second right.quadrances.first leftFactors.2.1
        rightFactors.1 second
    · exact entryScale left.spreads.third right.spreads.third
        left.quadrances.third right.quadrances.third leftFactors.2.2
        rightFactors.2.2 third
  · apply ScalarTriple.SameEntries.bca
    · exact entryScale left.spreads.first right.spreads.second
        left.quadrances.first right.quadrances.second leftFactors.1
        rightFactors.2.1 first
    · exact entryScale left.spreads.second right.spreads.third
        left.quadrances.second right.quadrances.third leftFactors.2.1
        rightFactors.2.2 second
    · exact entryScale left.spreads.third right.spreads.first
        left.quadrances.third right.quadrances.first leftFactors.2.2
        rightFactors.1 third
  · apply ScalarTriple.SameEntries.cab
    · exact entryScale left.spreads.first right.spreads.third
        left.quadrances.first right.quadrances.third leftFactors.1
        rightFactors.2.2 first
    · exact entryScale left.spreads.second right.spreads.first
        left.quadrances.second right.quadrances.first leftFactors.2.1
        rightFactors.1 second
    · exact entryScale left.spreads.third right.spreads.second
        left.quadrances.third right.quadrances.second leftFactors.2.2
        rightFactors.2.1 third
  · apply ScalarTriple.SameEntries.cba
    · exact entryScale left.spreads.first right.spreads.third
        left.quadrances.first right.quadrances.third leftFactors.1
        rightFactors.2.2 first
    · exact entryScale left.spreads.second right.spreads.second
        left.quadrances.second right.quadrances.second leftFactors.2.1
        rightFactors.2.1 second
    · exact entryScale left.spreads.third right.spreads.first
        left.quadrances.third right.quadrances.first leftFactors.2.2
        rightFactors.1 third

end NonNullTriangle

end DivineProportions
