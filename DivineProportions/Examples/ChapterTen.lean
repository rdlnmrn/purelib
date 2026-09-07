import DivineProportions.Triangles.ChapterTenFiniteFields
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 10 rational examples

The two examples below retain the source's literal rational coordinates.  All
side matches and spread matches are explicit finite permutation witnesses.
-/

namespace DivineProportions

namespace ChapterTenExamples

abbrev Rational := RFAP.ConstructiveFraction.Rational

private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem rational_natCast_ne {left right : Nat}
    (different : left ≠ right) : (left : Rational) ≠ (right : Rational) := by
  intro castsEqual
  exact different
    (RFAP.ConstructiveFraction.natCast_injective_direct castsEqual)

private theorem rational_div_ne_div_same_denominator
    {left right denominator : Nat} (different : left ≠ right)
    (denominatorNonzero : denominator ≠ 0) :
    (left : Rational) / denominator ≠ (right : Rational) / denominator := by
  intro fractionsEqual
  have castDenominatorNonzero : (denominator : Rational) ≠ 0 :=
    rational_natCast_nonzero denominatorNonzero
  have productsEqual := congrArg
    (fun value : Rational => value * denominator) fractionsEqual
  rw [RFAP.ExplicitField.div_mul_cancel _ castDenominatorNonzero,
    RFAP.ExplicitField.div_mul_cancel _ castDenominatorNonzero] at productsEqual
  exact rational_natCast_ne different productsEqual

private theorem ratio_eq_of_cross_product
    {K : Type*} [RFAP.ExplicitField K]
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ leftNonzero
  have rightCancel :
      rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
      rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

private theorem eq_of_mul_eq_mul_left
    {K : Type*} [RFAP.ExplicitField K]
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

private theorem rational_div_one (value : Rational) : value / 1 = value := by
  have oneNonzero : (1 : Rational) ≠ 0 :=
    fun oneZero => RFAP.ConstructiveFraction.zero_ne_one oneZero.symm
  calc
    value / 1 = (value / 1) * 1 := by rw [mul_one]
    _ = value := RFAP.ExplicitField.div_mul_cancel value oneNonzero

private theorem rational_fraction_product_eq
    (a b c d e f g h : Nat)
    (bNonzero : b ≠ 0) (dNonzero : d ≠ 0)
    (fNonzero : f ≠ 0) (hNonzero : h ≠ 0)
    (crossProduct :
      ((a : Rational) * c) * ((f : Rational) * h) =
        ((e : Rational) * g) * ((b : Rational) * d)) :
    ((a : Rational) / b) * (c / d) =
      ((e : Rational) / f) * (g / h) := by
  calc
    ((a : Rational) / b) * (c / d) =
        ((a : Rational) * c) / ((b : Rational) * d) :=
      RFAP.ConstructiveFraction.div_mul_div_direct
        (a : Rational) (b : Rational) (c : Rational) (d : Rational)
    _ = ((e : Rational) * g) / ((f : Rational) * h) := by
      apply ratio_eq_of_cross_product
        (RFAP.ExplicitField.mul_ne_zero
          (rational_natCast_nonzero bNonzero)
          (rational_natCast_nonzero dNonzero))
        (RFAP.ExplicitField.mul_ne_zero
          (rational_natCast_nonzero fNonzero)
          (rational_natCast_nonzero hNonzero))
      exact crossProduct
    _ = ((e : Rational) / f) * (g / h) :=
      (RFAP.ConstructiveFraction.div_mul_div_direct
        (e : Rational) (f : Rational) (g : Rational) (h : Rational)).symm

namespace ExerciseTenSix

def first : Point Rational := ⟨3, 0⟩
def second : Point Rational := ⟨0, 4⟩
def third : Point Rational := ⟨0, 0⟩

private theorem firstSecondDistinct : first ≠ second := by decide
private theorem firstThirdDistinct : first ≠ third := by decide
private theorem secondThirdDistinct : second ≠ third := by decide

private theorem notCollinear : ¬ Collinear first second third := by
  intro collinear
  have determinantZero :=
    pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : pointDeterminant first second third ≠ 0 := by
    unfold pointDeterminant first second third
    decide
  exact determinantNonzero determinantZero

private theorem firstSecondNonNull :
    ¬ (lineThrough first second firstSecondDistinct).IsNull := by
  unfold Line.IsNull lineThrough first second
  decide

private theorem firstThirdNonNull :
    ¬ (lineThrough first third firstThirdDistinct).IsNull := by
  unfold Line.IsNull lineThrough first third
  decide

private theorem secondThirdNonNull :
    ¬ (lineThrough second third secondThirdDistinct).IsNull := by
  unfold Line.IsNull lineThrough second third
  decide

def triangle : NonNullTriangle Rational where
  first := first
  second := second
  third := third
  notCollinear := notCollinear
  firstSecondDistinct := firstSecondDistinct
  firstThirdDistinct := firstThirdDistinct
  secondThirdDistinct := secondThirdDistinct
  firstSecondNonNull := firstSecondNonNull
  firstThirdNonNull := firstThirdNonNull
  secondThirdNonNull := secondThirdNonNull

private theorem rightAtThird :
    (lineThrough first third firstThirdDistinct).Perpendicular
      (lineThrough second third secondThirdDistinct) := by
  unfold Line.Perpendicular lineThrough first second third
  ring1

theorem quadrance_values : triangle.quadrances = ⟨16, 9, 25⟩ := by
  apply ScalarTriple.ext <;>
    unfold NonNullTriangle.quadrances triangleQuadrances quadrance
      triangle first second third <;>
    ring1

theorem corrected_values :
    quadrance first triangle.thirdAltitudeFoot = (81 : Rational) / 25 ∧
      quadrance second triangle.thirdAltitudeFoot = (256 : Rational) / 25 ∧
      quadrance third triangle.thirdAltitudeFoot = (144 : Rational) / 25 := by
  have corrected := exercise_10_6_corrected triangle
    (rational_natCast_nonzero (by decide : 2 ≠ 0)) rightAtThird
  rw [quadrance_values] at corrected
  refine ⟨?_, ?_, ?_⟩
  · calc
      quadrance first triangle.thirdAltitudeFoot =
          (9 : Rational) ^ 2 / 25 := corrected.1
      _ = 81 / 25 := by rw [show (9 : Rational) ^ 2 = 81 by ring1]
  · calc
      quadrance second triangle.thirdAltitudeFoot =
          (16 : Rational) ^ 2 / 25 := corrected.2.1
      _ = 256 / 25 := by rw [show (16 : Rational) ^ 2 = 256 by ring1]
  · calc
      quadrance third triangle.thirdAltitudeFoot =
          (16 : Rational) * 9 / 25 := corrected.2.2
      _ = 144 / 25 := by rw [show (16 : Rational) * 9 = 144 by ring1]

/-- The first printed equation in Exercise 10.6 uses `Q₁²/Q₃`, but
this explicit right triangle gives `81/25`, whereas that printed expression
is `256/25`. -/
theorem exercise_10_6_printed_counterexample :
    quadrance first triangle.thirdAltitudeFoot ≠
      triangle.quadrances.first ^ 2 / triangle.quadrances.third := by
  intro printed
  have impossible : (81 : Rational) / 25 = 256 / 25 := by
    calc
      (81 : Rational) / 25 =
          quadrance first triangle.thirdAltitudeFoot :=
        corrected_values.1.symm
      _ = triangle.quadrances.first ^ 2 /
          triangle.quadrances.third := printed
      _ = (256 : Rational) / 25 := by
        rw [quadrance_values]
        rw [show (16 : Rational) ^ 2 = 256 by ring1]
  exact rational_div_ne_div_same_denominator
    (by decide : 81 ≠ 256) (by decide : 25 ≠ 0) impossible

end ExerciseTenSix

namespace ExerciseTenSeven

def firstA : Point Rational := ⟨2, 3⟩
def secondA : Point Rational := ⟨3, 1⟩
def thirdA : Point Rational := ⟨10, 2⟩

def firstB : Point Rational := ⟨0, 1⟩
def secondB : Point Rational := ⟨-2, 2⟩
def thirdB : Point Rational := ⟨5, 6⟩

/-- Exercise 10.7.  The side triples are respectively `{50,65,5}` and
`{65,50,5}`, so the first two opposite sides are exchanged. -/
theorem exercise_10_7 :
    CongruentTriangles firstA secondA thirdA firstB secondB thirdB := by
  apply ScalarTriple.SameEntries.bac
  · unfold triangleQuadrances quadrance firstA secondA thirdA firstB secondB thirdB
    ring1
  · unfold triangleQuadrances quadrance firstA secondA thirdA firstB secondB thirdB
    ring1
  · unfold triangleQuadrances quadrance firstA secondA thirdA firstB secondB thirdB
    ring1

end ExerciseTenSeven

namespace ExerciseTenEight

def firstA : Point Rational := ⟨-4, 3⟩
def secondA : Point Rational := ⟨6, 5⟩
def thirdA : Point Rational := ⟨-1, 1⟩

def firstB : Point Rational := ⟨4, -7⟩
def secondB : Point Rational := ⟨-2, -11⟩
def thirdB : Point Rational := ⟨2, 9⟩

private theorem firstSecondDistinctA : firstA ≠ secondA := by decide
private theorem firstThirdDistinctA : firstA ≠ thirdA := by decide
private theorem secondThirdDistinctA : secondA ≠ thirdA := by decide
private theorem firstSecondDistinctB : firstB ≠ secondB := by decide
private theorem firstThirdDistinctB : firstB ≠ thirdB := by decide
private theorem secondThirdDistinctB : secondB ≠ thirdB := by decide

private theorem notCollinearA : ¬ Collinear firstA secondA thirdA := by
  intro collinear
  have determinantZero :=
    pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : pointDeterminant firstA secondA thirdA ≠ 0 := by
    unfold pointDeterminant firstA secondA thirdA
    decide
  exact determinantNonzero determinantZero

private theorem notCollinearB : ¬ Collinear firstB secondB thirdB := by
  intro collinear
  have determinantZero :=
    pointDeterminant_eq_zero_of_collinear collinear
  have determinantNonzero : pointDeterminant firstB secondB thirdB ≠ 0 := by
    unfold pointDeterminant firstB secondB thirdB
    decide
  exact determinantNonzero determinantZero

private theorem firstSecondNonNullA :
    ¬ (lineThrough firstA secondA firstSecondDistinctA).IsNull := by
  unfold Line.IsNull lineThrough firstA secondA
  decide

private theorem firstThirdNonNullA :
    ¬ (lineThrough firstA thirdA firstThirdDistinctA).IsNull := by
  unfold Line.IsNull lineThrough firstA thirdA
  decide

private theorem secondThirdNonNullA :
    ¬ (lineThrough secondA thirdA secondThirdDistinctA).IsNull := by
  unfold Line.IsNull lineThrough secondA thirdA
  decide

private theorem firstSecondNonNullB :
    ¬ (lineThrough firstB secondB firstSecondDistinctB).IsNull := by
  unfold Line.IsNull lineThrough firstB secondB
  decide

private theorem firstThirdNonNullB :
    ¬ (lineThrough firstB thirdB firstThirdDistinctB).IsNull := by
  unfold Line.IsNull lineThrough firstB thirdB
  decide

private theorem secondThirdNonNullB :
    ¬ (lineThrough secondB thirdB secondThirdDistinctB).IsNull := by
  unfold Line.IsNull lineThrough secondB thirdB
  decide

def triangleA : NonNullTriangle Rational where
  first := firstA
  second := secondA
  third := thirdA
  notCollinear := notCollinearA
  firstSecondDistinct := firstSecondDistinctA
  firstThirdDistinct := firstThirdDistinctA
  secondThirdDistinct := secondThirdDistinctA
  firstSecondNonNull := firstSecondNonNullA
  firstThirdNonNull := firstThirdNonNullA
  secondThirdNonNull := secondThirdNonNullA

def triangleB : NonNullTriangle Rational where
  first := firstB
  second := secondB
  third := thirdB
  notCollinear := notCollinearB
  firstSecondDistinct := firstSecondDistinctB
  firstThirdDistinct := firstThirdDistinctB
  secondThirdDistinct := secondThirdDistinctB
  firstSecondNonNull := firstSecondNonNullB
  firstThirdNonNull := firstThirdNonNullB
  secondThirdNonNull := secondThirdNonNullB

/-- The first triangle has opposite-side quadrances `65,13,104`; the second
has `416,260,52`. -/
theorem quadrance_values :
    triangleA.quadrances = ⟨65, 13, 104⟩ ∧
      triangleB.quadrances = ⟨416, 260, 52⟩ := by
  constructor
  · apply ScalarTriple.ext <;>
      unfold NonNullTriangle.quadrances triangleQuadrances quadrance
        triangleA firstA secondA thirdA <;>
      ring1
  · apply ScalarTriple.ext <;>
      unfold NonNullTriangle.quadrances triangleQuadrances quadrance
        triangleB firstB secondB thirdB <;>
      ring1

/-- The first spread triple is `(1/2,1/10,4/5)`. -/
theorem triangleA_spread_values :
    triangleA.spreads.first = (1 : Rational) / 2 ∧
      triangleA.spreads.second = (1 : Rational) / 10 ∧
      triangleA.spreads.third = (4 : Rational) / 5 := by
  constructor
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstSecondNonNullA firstThirdNonNullA)
      (rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold triangleA lineThrough firstA secondA thirdA
    ring1
  constructor
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        triangleA.firstSecondReversedNonNull secondThirdNonNullA)
      (rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold triangleA lineThrough firstA secondA thirdA
    ring1
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        triangleA.firstThirdReversedNonNull
        triangleA.secondThirdReversedNonNull)
      (rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold triangleA lineThrough firstA secondA thirdA
    ring1

/-- The second spread triple is `(4/5,1/2,1/10)`. -/
theorem triangleB_spread_values :
    triangleB.spreads.first = (4 : Rational) / 5 ∧
      triangleB.spreads.second = (1 : Rational) / 2 ∧
      triangleB.spreads.third = (1 : Rational) / 10 := by
  constructor
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero firstSecondNonNullB firstThirdNonNullB)
      (rational_natCast_nonzero (by decide : 5 ≠ 0))
    unfold triangleB lineThrough firstB secondB thirdB
    ring1
  constructor
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        triangleB.firstSecondReversedNonNull secondThirdNonNullB)
      (rational_natCast_nonzero (by decide : 2 ≠ 0))
    unfold triangleB lineThrough firstB secondB thirdB
    ring1
  · unfold NonNullTriangle.spreads spread
    apply ratio_eq_of_cross_product
      (RFAP.ExplicitField.mul_ne_zero
        triangleB.firstThirdReversedNonNull
        triangleB.secondThirdReversedNonNull)
      (rational_natCast_nonzero (by decide : 10 ≠ 0))
    unfold triangleB lineThrough firstB secondB thirdB
    ring1

theorem triangles_similar : triangleA.Similar triangleB := by
  apply ScalarTriple.SameEntries.bca
  · exact triangleA_spread_values.1.trans triangleB_spread_values.2.1.symm
  · exact triangleA_spread_values.2.1.trans
      triangleB_spread_values.2.2.symm
  · exact triangleA_spread_values.2.2.trans triangleB_spread_values.1.symm

theorem triangles_not_congruent : ¬ triangleA.Congruent triangleB := by
  intro congruent
  have sameValues :
      ScalarTriple.SameEntries triangleA.quadrances triangleB.quadrances :=
    congruent
  rw [quadrance_values.1, quadrance_values.2] at sameValues
  rcases sameValues with
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩ |
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩ |
    ⟨first, _second, _third⟩ | ⟨first, _second, _third⟩
  · exact rational_natCast_ne (by decide : 65 ≠ 416) first
  · exact rational_natCast_ne (by decide : 65 ≠ 416) first
  · exact rational_natCast_ne (by decide : 65 ≠ 260) first
  · exact rational_natCast_ne (by decide : 65 ≠ 260) first
  · exact rational_natCast_ne (by decide : 65 ≠ 52) first
  · exact rational_natCast_ne (by decide : 65 ≠ 52) first

/-- Exercise 10.8, with both halves retained. -/
theorem exercise_10_8 : triangleA.Similar triangleB ∧
    ¬ triangleA.Congruent triangleB :=
  ⟨triangles_similar, triangles_not_congruent⟩

end ExerciseTenEight

namespace ExampleTenOne

/-- The source's Cross-law equation after clearing its literal denominator is
exactly the displayed factorization. -/
theorem cross_law_factorization
    {K : Type*} [RFAP.ExplicitField K] (q₂ : K) :
    13 * (q₂ - 12) ^ 2 = 98 * q₂ ↔
      (13 * q₂ - 72) * (q₂ - 26) = 0 := by
  constructor
  · intro cleared
    calc
      (13 * q₂ - 72) * (q₂ - 26) =
          13 * (q₂ - 12) ^ 2 - 98 * q₂ := by ring1
      _ = 0 := by rw [cleared]; ring1
  · intro factored
    have differenceZero :
        13 * (q₂ - 12) ^ 2 - 98 * q₂ = 0 := by
      calc
        13 * (q₂ - 12) ^ 2 - 98 * q₂ =
            (13 * q₂ - 72) * (q₂ - 26) := by ring1
        _ = 0 := factored
    exact sub_eq_zero.mp differenceZero

/-- Example 10.1's two and only two candidates for `Q₂`, obtained by the
book's finite factorization. -/
theorem quadrance_alternatives
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    (q₂ : K) (thirteenNonzero : (13 : K) ≠ 0)
    (crossLaw : (q₂ - 12) ^ 2 = (98 / 13) * q₂) :
    q₂ = 72 / 13 ∨ q₂ = 26 := by
  have cleared : 13 * (q₂ - 12) ^ 2 = 98 * q₂ := by
    calc
      13 * (q₂ - 12) ^ 2 = (q₂ - 12) ^ 2 * 13 := by ring1
      _ = ((98 / 13) * q₂) * 13 := by rw [crossLaw]
      _ = ((98 / 13) * 13) * q₂ := by ring1
      _ = 98 * q₂ := by
        rw [RFAP.ExplicitField.div_mul_cancel 98 thirteenNonzero]
  have factored := (cross_law_factorization q₂).1 cleared
  by_cases secondFactorZero : q₂ - 26 = 0
  · exact Or.inr (sub_eq_zero.mp secondFactorZero)
  · have firstFactorZero : 13 * q₂ - 72 = 0 := by
      by_cases firstZero : 13 * q₂ - 72 = 0
      · exact firstZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstZero secondFactorZero)
            factored)
    left
    apply eq_of_mul_eq_mul_left thirteenNonzero
    calc
      13 * q₂ = 72 := sub_eq_zero.mp firstFactorZero
      _ = (72 / 13) * 13 :=
        (RFAP.ExplicitField.div_mul_cancel 72 thirteenNonzero).symm
      _ = 13 * (72 / 13) := by ring1

theorem rational_quadrance_alternatives (q₂ : Rational)
    (crossLaw : (q₂ - 12) ^ 2 = (98 / 13) * q₂) :
    q₂ = 72 / 13 ∨ q₂ = 26 :=
  quadrance_alternatives q₂
    (rational_natCast_nonzero (by decide : 13 ≠ 0)) crossLaw

private theorem cross_law_of_cleared
    {K : Type*} [RFAP.ExplicitField K]
    (q₂ : K) (thirteenNonzero : (13 : K) ≠ 0)
    (cleared : 13 * (q₂ - 12) ^ 2 = 98 * q₂) :
    (q₂ - 12) ^ 2 = (98 / 13) * q₂ := by
  apply eq_of_mul_eq_mul_left thirteenNonzero
  calc
    13 * (q₂ - 12) ^ 2 = 98 * q₂ := cleared
    _ = ((98 / 13) * 13) * q₂ := by
      rw [RFAP.ExplicitField.div_mul_cancel 98 thirteenNonzero]
    _ = 13 * ((98 / 13) * q₂) := by ring1

/-- Both displayed candidates satisfy the Cross-law equation used to obtain
them. -/
theorem quadrance_candidates_satisfy :
    (((72 : Rational) / 13 - 12) ^ 2 =
        (98 / 13) * ((72 : Rational) / 13)) ∧
      ((26 : Rational) - 12) ^ 2 = (98 / 13) * 26 := by
  have thirteenNonzero : (13 : Rational) ≠ 0 :=
    rational_natCast_nonzero (by decide)
  constructor
  · apply cross_law_of_cleared ((72 : Rational) / 13) thirteenNonzero
    apply (cross_law_factorization ((72 : Rational) / 13)).2
    have firstFactorZero :
        13 * ((72 : Rational) / 13) - 72 = 0 := by
      calc
        13 * ((72 : Rational) / 13) - 72 =
            ((72 : Rational) / 13) * 13 - 72 := by ring1
        _ = 72 - 72 := by
          rw [RFAP.ExplicitField.div_mul_cancel 72 thirteenNonzero]
        _ = 0 := by ring1
    rw [firstFactorZero]
    ring1
  · apply cross_law_of_cleared (26 : Rational) thirteenNonzero
    apply (cross_law_factorization (26 : Rational)).2
    ring1

private theorem case_one_first_cross :
    ((81 : Rational) / 442) * ((72 : Rational) / 13) =
      ((2916 : Rational) / 14365) * 5 := by
  calc
    ((81 : Rational) / 442) * ((72 : Rational) / 13) =
        ((2916 : Rational) / 14365) * ((5 : Rational) / 1) :=
      rational_fraction_product_eq 81 442 72 13 2916 14365 5 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((2916 : Rational) / 14365) * 5 := by
      rw [rational_div_one]

private theorem case_one_second_cross :
    ((2916 : Rational) / 14365) * 17 =
      ((81 : Rational) / 130) * ((72 : Rational) / 13) := by
  calc
    ((2916 : Rational) / 14365) * 17 =
        ((2916 : Rational) / 14365) * ((17 : Rational) / 1) := by
      rw [rational_div_one]
    _ = ((81 : Rational) / 130) * ((72 : Rational) / 13) :=
      rational_fraction_product_eq 2916 14365 17 1 81 130 72 13
        (by decide) (by decide) (by decide) (by decide) (by ring1)

/-- The complete Spread-law quotient chain for the first candidate. -/
theorem first_spread_solution :
    ((81 : Rational) / 442) / 5 =
        ((2916 : Rational) / 14365) / ((72 : Rational) / 13) ∧
      ((2916 : Rational) / 14365) / ((72 : Rational) / 13) =
        ((81 : Rational) / 130) / 17 := by
  have seventyTwoNonzero : (72 : Rational) ≠ 0 :=
    rational_natCast_nonzero (by decide)
  have thirteenNonzero : (13 : Rational) ≠ 0 :=
    rational_natCast_nonzero (by decide)
  have q₂Nonzero : (72 : Rational) / 13 ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero seventyTwoNonzero thirteenNonzero
  exact ⟨
    ratio_eq_of_cross_product
      (rational_natCast_nonzero (by decide : 5 ≠ 0)) q₂Nonzero
      case_one_first_cross,
    ratio_eq_of_cross_product q₂Nonzero
      (rational_natCast_nonzero (by decide : 17 ≠ 0))
      case_one_second_cross⟩

private theorem case_two_first_cross :
    ((81 : Rational) / 442) * 26 =
      ((81 : Rational) / 85) * 5 := by
  calc
    ((81 : Rational) / 442) * 26 =
        ((81 : Rational) / 442) * ((26 : Rational) / 1) := by
      rw [rational_div_one]
    _ = ((81 : Rational) / 85) * ((5 : Rational) / 1) :=
      rational_fraction_product_eq 81 442 26 1 81 85 5 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((81 : Rational) / 85) * 5 := by rw [rational_div_one]

private theorem case_two_second_cross :
    ((81 : Rational) / 85) * 17 =
      ((81 : Rational) / 130) * 26 := by
  calc
    ((81 : Rational) / 85) * 17 =
        ((81 : Rational) / 85) * ((17 : Rational) / 1) := by
      rw [rational_div_one]
    _ = ((81 : Rational) / 130) * ((26 : Rational) / 1) :=
      rational_fraction_product_eq 81 85 17 1 81 130 26 1
        (by decide) (by decide) (by decide) (by decide) (by ring1)
    _ = ((81 : Rational) / 130) * 26 := by rw [rational_div_one]

/-- The complete Spread-law quotient chain for the second candidate. -/
theorem second_spread_solution :
    ((81 : Rational) / 442) / 5 =
        ((81 : Rational) / 85) / 26 ∧
      ((81 : Rational) / 85) / 26 =
        ((81 : Rational) / 130) / 17 := by
  exact ⟨
    ratio_eq_of_cross_product
      (rational_natCast_nonzero (by decide : 5 ≠ 0))
      (rational_natCast_nonzero (by decide : 26 ≠ 0))
      case_two_first_cross,
    ratio_eq_of_cross_product
      (rational_natCast_nonzero (by decide : 26 ≠ 0))
      (rational_natCast_nonzero (by decide : 17 ≠ 0))
      case_two_second_cross⟩

/-- Example 10.1, collecting both Cross-law candidates and both displayed
Spread-law solutions. -/
theorem example_10_1 :
    ((((72 : Rational) / 13 - 12) ^ 2 =
        (98 / 13) * ((72 : Rational) / 13)) ∧
      ((26 : Rational) - 12) ^ 2 = (98 / 13) * 26) ∧
      (((81 : Rational) / 442) / 5 =
          ((2916 : Rational) / 14365) / ((72 : Rational) / 13) ∧
        ((2916 : Rational) / 14365) / ((72 : Rational) / 13) =
          ((81 : Rational) / 130) / 17) ∧
      (((81 : Rational) / 442) / 5 = ((81 : Rational) / 85) / 26 ∧
        ((81 : Rational) / 85) / 26 = ((81 : Rational) / 130) / 17) :=
  ⟨quadrance_candidates_satisfy, first_spread_solution,
    second_spread_solution⟩

end ExampleTenOne

namespace ExerciseTenTen

def first : Point FieldThree.Element := ⟨0, 0⟩
def second : Point FieldThree.Element := ⟨1, 0⟩
def third : Point FieldThree.Element := ⟨0, 1⟩

private theorem notCollinear : ¬ Collinear first second third := by
  intro collinear
  have determinantZero := pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : pointDeterminant first second third ≠ 0)
    determinantZero

def triangle : NonNullTriangle FieldThree.Element :=
  FieldThree.nonNullTriangle first second third notCollinear

/-- A literal representative of Exercise 10.10: its quadrances are
`(2,1,1)`, its spreads are `(1,2,2)`, and the first vertex is right
isosceles. -/
theorem representative :
    triangle.quadrances = ⟨2, 1, 1⟩ ∧
      triangle.spreads = ⟨1, 2, 2⟩ ∧
      triangle.RightIsoscelesAtFirst := by
  constructor
  · apply ScalarTriple.ext <;> decide
  constructor
  · apply ScalarTriple.ext <;> decide
  · unfold NonNullTriangle.RightIsoscelesAtFirst
    constructor
    · decide
    · unfold Line.Perpendicular
      decide

end ExerciseTenTen

namespace ExerciseTenEleven

namespace SpreadThree

def first : Point FieldFive.Element := ⟨0, 1⟩
def second : Point FieldFive.Element := ⟨1, 2⟩
def third : Point FieldFive.Element := ⟨0, 0⟩

private theorem notCollinear : ¬ Collinear first second third := by
  intro collinear
  have determinantZero := pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : pointDeterminant first second third ≠ 0)
    determinantZero

def triangle : FieldFive.SinglyNullAtFirst where
  first := first
  second := second
  third := third
  notCollinear := notCollinear
  firstQuadranceZero := by decide
  secondQuadranceNonzero := by decide
  thirdQuadranceNonzero := by decide

theorem quadrances_and_spread :
    quadrance second third = 0 ∧
      quadrance first third = 1 ∧
      quadrance first second = 2 ∧
      triangle.oppositeSpread = 3 := by
  decide

end SpreadThree

namespace SpreadOne

def first : Point FieldFive.Element := ⟨0, 1⟩
def second : Point FieldFive.Element := ⟨2, 1⟩
def third : Point FieldFive.Element := ⟨0, 0⟩

private theorem notCollinear : ¬ Collinear first second third := by
  intro collinear
  have determinantZero := pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : pointDeterminant first second third ≠ 0)
    determinantZero

def triangle : FieldFive.SinglyNullAtFirst where
  first := first
  second := second
  third := third
  notCollinear := notCollinear
  firstQuadranceZero := by decide
  secondQuadranceNonzero := by decide
  thirdQuadranceNonzero := by decide

theorem quadrances_and_spread :
    quadrance second third = 0 ∧
      quadrance first third = 1 ∧
      quadrance first second = 4 ∧
      triangle.oppositeSpread = 1 := by
  decide

end SpreadOne

namespace TwoNullSides

def first : Point FieldFive.Element := ⟨0, 1⟩
def second : Point FieldFive.Element := ⟨1, 3⟩
def third : Point FieldFive.Element := ⟨0, 0⟩

private theorem firstSecondDistinct : first ≠ second := by decide
private theorem firstThirdDistinct : first ≠ third := by decide
private theorem secondThirdDistinct : second ≠ third := by decide

private theorem notCollinear : ¬ Collinear first second third := by
  intro collinear
  have determinantZero := pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : pointDeterminant first second third ≠ 0)
    determinantZero

/-- A noncollinear `F₅` triangle with two null sides.  Every vertex contains
at least one of those sides, so no vertex meets the two non-null premises
required by the book's definition of spread. -/
theorem separate_degenerate_regime :
    ¬ Collinear first second third ∧
      (lineThrough first second firstSecondDistinct).IsNull ∧
      ¬ (lineThrough first third firstThirdDistinct).IsNull ∧
      (lineThrough second third secondThirdDistinct).IsNull := by
  refine ⟨notCollinear, ?_, ?_, ?_⟩
  · unfold Line.IsNull
    decide
  · unfold Line.IsNull
    decide
  · unfold Line.IsNull
    decide

end TwoNullSides

/-- Both singly-null similarity values occur, while the two-null-side case is
a separate regime outside spread-based similarity. -/
theorem exercise_10_11_null_examples :
    SpreadThree.triangle.oppositeSpread = 3 ∧
      SpreadOne.triangle.oppositeSpread = 1 ∧
      ¬ Collinear TwoNullSides.first TwoNullSides.second TwoNullSides.third :=
  ⟨SpreadThree.quadrances_and_spread.2.2.2,
    SpreadOne.quadrances_and_spread.2.2.2,
    TwoNullSides.separate_degenerate_regime.1⟩

end ExerciseTenEleven

end ChapterTenExamples

end DivineProportions
