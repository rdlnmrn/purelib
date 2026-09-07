import DivineProportions.Proportions.ChapterElevenExercises
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 11 examples

The source's factored Two-struts example and its two failed converses are
recorded over constructive rational coordinates.  The counterexamples use
integer points, so every incidence, quadrance, and determinant is a finite
kernel computation.
-/

namespace DivineProportions

namespace ChapterElevenExamples

abbrev Rational := RFAP.ConstructiveFraction.Rational

private theorem rationalNatCastNonzero {value : Nat}
    (valuePositive : 0 < value) : (value : Rational) ≠ 0 := by
  intro castZero
  have castPositive : (0 : Rational) < (value : Rational) :=
    RFAP.ConstructiveFraction.natCast_pos_direct valuePositive
  rw [castZero] at castPositive
  exact (lt_irrefl 0) castPositive

namespace ExampleElevenOne

def p : Rational := 1 / 4
def r : Rational := 9 / 64

/-- Example 11.1 at the source's literal rational parameters. -/
theorem example_11_1 (m n : Rational)
    (strutTriples :
      QuadTriple r (r * p) (m * p) ∧
        QuadTriple p (r * p) (n * r)) :
    (64 * m - 9) * (64 * m - 81) = 0 ∧
      (36 * n - 25) * (36 * n - 121) = 0 := by
  apply DivineProportions.example_11_1 p r m n
  · calc
      4 * p = p * 4 := by ring1
      _ = 1 := RFAP.ExplicitField.div_mul_cancel 1
        (rationalNatCastNonzero (by decide))
  · calc
      64 * r = r * 64 := by ring1
      _ = 9 := RFAP.ExplicitField.div_mul_cancel 9
        (rationalNatCastNonzero (by decide))
  · exact strutTriples

end ExampleElevenOne

namespace ExerciseElevenFour

def p : Rational := 1
def r : Rational := 1
def m : Rational := 4
def n : Rational := 4
def s₁ : Rational := 3 / 4
def s₂ : Rational := 3 / 4
def s₃ : Rational := 3 / 4

private theorem thirdSpreadNonzero : s₃ ≠ 0 := by decide

private theorem strutTriples :
    QuadTriple r (r * p) (m * p) ∧
      QuadTriple p (r * p) (n * r) := by
  constructor <;> unfold QuadTriple archimedesFunction <;> decide

/-- The corrected equations hold for the equilateral-spread specialization
`p=r=1`, `m=n=4`. -/
theorem corrected_equations :
    (m * s₂ + s₁ + s₃) ^ 2 =
        2 * ((m * s₂) ^ 2 + s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 =
        2 * ((n * s₁) ^ 2 + s₂ ^ 2 + s₃ ^ 2) := by
  apply exercise_11_4_corrected p r m n s₁ s₂ s₃ thirdSpreadNonzero
  · decide
  · decide
  · exact strutTriples

/-- The two equations printed in Exercise 11.4 omit the `m²` and `n²`
terms.  This exact specialization refutes both omissions. -/
theorem printed_equations_counterexample :
    ¬ ((m * s₂ + s₁ + s₃) ^ 2 = 2 * (s₁ ^ 2 + s₃ ^ 2) ∧
      (n * s₁ + s₂ + s₃) ^ 2 = 2 * (s₂ ^ 2 + s₃ ^ 2)) := by
  decide

end ExerciseElevenFour

namespace ExerciseElevenEight

def first : Point Rational := ⟨0, 0⟩
def second : Point Rational := ⟨2, 0⟩
def third : Point Rational := ⟨0, 2⟩

/-- The midpoint of `A₂A₃`. -/
def B₁ : Point Rational := ⟨1, 1⟩
/-- The midpoint of `A₃A₁`. -/
def B₂ : Point Rational := ⟨0, 1⟩
/-- The midpoint of `A₁A₂`. -/
def B₃ : Point Rational := ⟨1, 0⟩

private theorem firstSide : Collinear second third B₁ := by
  let distinct : second ≠ third := by decide
  exact ⟨lineThrough second third distinct,
    lineThrough_contains_first second third distinct,
    lineThrough_contains_second second third distinct, by
      unfold Line.Contains lineThrough second third B₁
      ring1⟩

private theorem secondSide : Collinear third first B₂ := by
  let distinct : third ≠ first := by decide
  exact ⟨lineThrough third first distinct,
    lineThrough_contains_first third first distinct,
    lineThrough_contains_second third first distinct, by
      unfold Line.Contains lineThrough third first B₂
      ring1⟩

private theorem thirdSide : Collinear first second B₃ := by
  let distinct : first ≠ second := by decide
  exact ⟨lineThrough first second distinct,
    lineThrough_contains_first first second distinct,
    lineThrough_contains_second first second distinct, by
      unfold Line.Contains lineThrough first second B₃
      ring1⟩

/-- The six quadrances are `(2,2)`, `(1,1)`, and `(1,1)`. -/
theorem quadrance_values :
    quadrance second B₁ = 2 ∧ quadrance B₁ third = 2 ∧
      quadrance third B₂ = 1 ∧ quadrance B₂ first = 1 ∧
      quadrance first B₃ = 1 ∧ quadrance B₃ second = 1 := by
  decide

/-- Exercise 11.8.  The three side midpoints satisfy the Menelaus product
but form a nondegenerate medial triangle rather than a line. -/
theorem exercise_11_8 :
    Collinear second third B₁ ∧
      Collinear third first B₂ ∧
      Collinear first second B₃ ∧
      quadrance second B₁ * quadrance third B₂ * quadrance first B₃ =
        quadrance B₁ third * quadrance B₂ first * quadrance B₃ second ∧
      ¬ Collinear B₁ B₂ B₃ := by
  refine ⟨firstSide, secondSide, thirdSide, by decide, ?_⟩
  intro collinear
  have determinantZero := pointDeterminant_eq_zero_of_collinear collinear
  exact (by decide : pointDeterminant B₁ B₂ B₃ ≠ 0) determinantZero

end ExerciseElevenEight

namespace ExerciseElevenTen

def first : Point Rational := ⟨0, 0⟩
def second : Point Rational := ⟨6, 0⟩
def third : Point Rational := ⟨0, 6⟩

/-- The one-third point of `A₂A₃`. -/
def B₁ : Point Rational := ⟨4, 2⟩
/-- The midpoint of `A₃A₁`. -/
def B₂ : Point Rational := ⟨0, 3⟩
/-- An external point of `A₁A₂`, beyond `A₂`. -/
def B₃ : Point Rational := ⟨12, 0⟩

private theorem firstSide : Collinear second third B₁ := by
  let distinct : second ≠ third := by decide
  exact ⟨lineThrough second third distinct,
    lineThrough_contains_first second third distinct,
    lineThrough_contains_second second third distinct, by
      unfold Line.Contains lineThrough second third B₁
      ring1⟩

private theorem secondSide : Collinear third first B₂ := by
  let distinct : third ≠ first := by decide
  exact ⟨lineThrough third first distinct,
    lineThrough_contains_first third first distinct,
    lineThrough_contains_second third first distinct, by
      unfold Line.Contains lineThrough third first B₂
      ring1⟩

private theorem thirdSide : Collinear first second B₃ := by
  let distinct : first ≠ second := by decide
  exact ⟨lineThrough first second distinct,
    lineThrough_contains_first first second distinct,
    lineThrough_contains_second first second distinct, by
      unfold Line.Contains lineThrough first second B₃
      ring1⟩

private theorem firstB₁Distinct : first ≠ B₁ := by decide
private theorem secondB₂Distinct : second ≠ B₂ := by decide
private theorem thirdB₃Distinct : third ≠ B₃ := by decide

def firstCevian : Line Rational := lineThrough first B₁ firstB₁Distinct
def secondCevian : Line Rational := lineThrough second B₂ secondB₂Distinct
def thirdCevian : Line Rational := lineThrough third B₃ thirdB₃Distinct

/-- The six quadrances are `(8,32)`, `(9,9)`, and `(144,36)`. -/
theorem quadrance_values :
    quadrance second B₁ = 8 ∧ quadrance B₁ third = 32 ∧
      quadrance third B₂ = 9 ∧ quadrance B₂ first = 9 ∧
      quadrance first B₃ = 144 ∧ quadrance B₃ second = 36 := by
  constructor
  · unfold quadrance second B₁
    ring1
  constructor
  · unfold quadrance B₁ third
    ring1
  constructor
  · unfold quadrance third B₂
    ring1
  constructor
  · unfold quadrance B₂ first
    ring1
  constructor
  · unfold quadrance first B₃
    ring1
  · unfold quadrance B₃ second
    ring1

/-- The three displayed cevians have no common point. -/
theorem cevians_not_concurrent :
    ¬ ∃ point : Point Rational,
      firstCevian.Contains point ∧ secondCevian.Contains point ∧
        thirdCevian.Contains point := by
  rintro ⟨point, firstContains, secondContains, thirdContains⟩
  have determinantZero := lineDeterminant_eq_zero_of_concurrent
    firstCevian secondCevian thirdCevian point firstContains secondContains
      thirdContains
  exact (by decide :
    lineDeterminant firstCevian secondCevian thirdCevian ≠ 0)
      determinantZero

/-- Exercise 11.10.  Squared side ratios lose the sign detected by affine
Ceva: the quadrance products agree, but the three cevians are not
concurrent. -/
theorem exercise_11_10 :
    Collinear second third B₁ ∧
      Collinear third first B₂ ∧
      Collinear first second B₃ ∧
      quadrance second B₁ * quadrance third B₂ * quadrance first B₃ =
        quadrance B₁ third * quadrance B₂ first * quadrance B₃ second ∧
      ¬ ∃ point : Point Rational,
        firstCevian.Contains point ∧ secondCevian.Contains point ∧
          thirdCevian.Contains point := by
  refine ⟨firstSide, secondSide, thirdSide, ?_, cevians_not_concurrent⟩
  rw [quadrance_values.1, quadrance_values.2.1,
    quadrance_values.2.2.1, quadrance_values.2.2.2.1,
    quadrance_values.2.2.2.2.1, quadrance_values.2.2.2.2.2]
  ring1

end ExerciseElevenTen

namespace ExerciseElevenEleven

/-- When the common spread product is null, all three cleared Menelaus
relations may hold while the quadrance products differ.  This is the precise
cancellation failure described by Exercise 11.11. -/
theorem null_factor_counterexample :
    ∃ r₁ r₂ r₃ R₁ R₂ R₃ P₁ P₂ P₃ : Rational,
      r₁ * P₁ = R₂ * r₂ ∧
      r₂ * P₂ = R₃ * r₃ ∧
      r₃ * P₃ = R₁ * r₁ ∧
      (R₁ * R₂ * R₃ - P₁ * P₂ * P₃) * (r₁ * r₂ * r₃) = 0 ∧
      R₁ * R₂ * R₃ ≠ P₁ * P₂ * P₃ := by
  refine ⟨0, 0, 0, 1, 1, 1, 0, 1, 1, ?_⟩
  decide

end ExerciseElevenEleven

end ChapterElevenExamples

end DivineProportions
