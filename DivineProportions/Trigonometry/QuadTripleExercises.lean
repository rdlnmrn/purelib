import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Chapter 5 quad-triple exercises

The exercises below are direct finite polynomial consequences of
Archimedes' function.  Exercise 5.11 exposes the same distinct-centre premise
missing from the source's earlier quadratic-compatibility claim; no root is
selected in the degenerate case.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The two-by-two determinant displayed in Exercise 5.7. -/
def archimedesDeterminantTwo (a b c : K) : K :=
  2 * a * (2 * b) - (a + b - c) * (a + b - c)

/-- A direct three-by-three determinant expansion used only to retain the
source's finite four-by-four determinant literally. -/
def scalarDeterminantThree
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : K) : K :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₃₂) -
    a₁₂ * (a₂₁ * a₃₃ - a₂₃ * a₃₁) +
    a₁₃ * (a₂₁ * a₃₂ - a₂₂ * a₃₁)

/-- The determinant of the exact symmetric four-by-four matrix printed in
Exercise 5.7, expanded along its first row. -/
def archimedesDeterminantFour (a b c : K) : K :=
  -a * scalarDeterminantThree a c 1 b 0 1 1 1 0 +
    b * scalarDeterminantThree a 0 1 b c 1 1 1 0 -
    scalarDeterminantThree a 0 c b c 0 1 1 1

/-- Exercise 5.7: all five displayed forms of Archimedes' function,
including both literal finite determinants. -/
theorem exercise_5_7 (a b c : K) :
    archimedesFunction a b c = 4 * a * b - (a + b - c) ^ 2 ∧
      archimedesFunction a b c =
        2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2) ∧
      archimedesFunction a b c =
        4 * (a * b + b * c + c * a) - (a + b + c) ^ 2 ∧
      archimedesFunction a b c = archimedesDeterminantTwo a b c ∧
      archimedesFunction a b c = -archimedesDeterminantFour a b c := by
  unfold archimedesFunction archimedesDeterminantTwo
    archimedesDeterminantFour scalarDeterminantThree
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Exercise 5.8: every one of the four relations `a ± b = ±c` makes the
three squares a quad triple. -/
theorem exercise_5_8 (a b c : K)
    (signedRelation :
      a + b = c ∨ a - b = c ∨ a + b = -c ∨ a - b = -c) :
    QuadTriple (a ^ 2) (b ^ 2) (c ^ 2) := by
  unfold QuadTriple archimedesFunction
  rcases signedRelation with sumEquals | differenceEquals |
      sumEqualsNegative | differenceEqualsNegative
  · rw [← sumEquals]
    ring1
  · rw [← differenceEquals]
    ring1
  · have cValue : c = -(a + b) := by
      calc
        c = -(-c) := by ring1
        _ = -(a + b) := by rw [sumEqualsNegative]
    rw [cValue]
    ring1
  · have cValue : c = -(a - b) := by
      calc
        c = -(-c) := by ring1
        _ = -(a - b) := by rw [differenceEqualsNegative]
    rw [cValue]
    ring1

/-- Exercise 5.10: Archimedes' relation written as the displayed quadratic
equation in its third entry. -/
theorem exercise_5_10 (q₁ q₂ q₃ : K) :
    QuadTriple q₁ q₂ q₃ ↔
      q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2 = 0 := by
  unfold QuadTriple
  constructor
  · intro triple
    calc
      q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2 =
          -archimedesFunction q₁ q₂ q₃ := by
            unfold archimedesFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  · intro quadratic
    calc
      archimedesFunction q₁ q₂ q₃ =
          -(q₃ ^ 2 - 2 * (q₁ + q₂) * q₃ + (q₁ - q₂) ^ 2) := by
            unfold archimedesFunction
            ring1
      _ = 0 := by rw [quadratic]; ring1

/-- Exercise 5.11, with the necessary distinct-centre premise made explicit:
the two displayed quadratic equations have a common solution exactly when
their two right sides and squared centre separation form a quad triple. -/
theorem exercise_5_11
    (p₁ q₁ p₂ q₂ : K)
    (twoNonzero : (2 : K) ≠ 0) (centresDistinct : p₁ ≠ p₂) :
    QuadraticsCompatible p₁ q₁ p₂ q₂ ↔
      QuadTriple q₁ q₂ ((p₁ - p₂) ^ 2) := by
  rw [quadraticCompatibility_of_distinct_centres
    twoNonzero centresDistinct]
  unfold quadraticCompatibilityIdentity
  exact (quadTriple_iff_centered_square q₁ q₂ ((p₁ - p₂) ^ 2)).symm

/-- Exercise 5.12: the two quadrances adjacent to the right vertex of a
noncollinear triangle are necessarily nonzero. -/
theorem exercise_5_12 [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second third secondThirdDistinct)) :
    quadrance second third ≠ 0 ∧ quadrance first third ≠ 0 := by
  have areaNonzero : quadrea first second third ≠ 0 :=
    (quadrea_ne_zero_iff_not_collinear first second third twoNonzero).2
      notCollinear
  have rightArea := right_triangle_quadrea first second third
    firstThirdDistinct secondThirdDistinct twoNonzero rightAtThird
  constructor
  · intro firstQuadranceZero
    apply areaNonzero
    rw [rightArea, firstQuadranceZero]
    ring1
  · intro secondQuadranceZero
    apply areaNonzero
    rw [rightArea, secondQuadranceZero]
    ring1

namespace ExerciseFiveTwelveExample

abbrev Element := FieldFive.Element

def first : Point Element := ⟨1, 0⟩
def second : Point Element := ⟨0, 2⟩
def third : Point Element := ⟨0, 0⟩

/-- Exercise 5.12's requested example: this noncollinear `F₅` triangle is
right at `third`, while the opposite side has quadrance zero. -/
theorem opposite_quadrance_can_vanish :
    quadrance first second = 0 ∧
      (lineThrough first third (by decide)).Perpendicular
        (lineThrough second third (by decide)) ∧
      ¬ Collinear first second third := by
  constructor
  · decide
  constructor
  · unfold Line.Perpendicular lineThrough first second third
    decide
  · intro collinear
    have determinantZero :=
      (collinear_iff_pointDeterminant_eq_zero first second third).1
        collinear
    have determinantNonzero :
        pointDeterminant first second third ≠ 0 := by
      unfold pointDeterminant first second third
      decide
    exact determinantNonzero determinantZero

end ExerciseFiveTwelveExample

/-- Exercise 5.14: the cyclic linear-factor expansion of the quadrea. -/
theorem exercise_5_14 (q₁ q₂ q₃ : K) :
    archimedesFunction q₁ q₂ q₃ =
      q₁ * (q₂ + q₃ - q₁) +
        q₂ * (q₃ + q₁ - q₂) +
        q₃ * (q₁ + q₂ - q₃) := by
  unfold archimedesFunction
  ring1

/-- Exercise 5.15: the three-product expansion of the quadrea. -/
theorem exercise_5_15 (q₁ q₂ q₃ : K) :
    archimedesFunction q₁ q₂ q₃ =
      (q₃ + q₁ - q₂) * (q₁ + q₂ - q₃) +
        (q₁ + q₂ - q₃) * (q₂ + q₃ - q₁) +
        (q₂ + q₃ - q₁) * (q₃ + q₁ - q₂) := by
  unfold archimedesFunction
  ring1

/-- Exercise 5.18: two quad triples `{a,b,x}` and `{b,c,x}` with distinct
outer entries determine their common value as `(a+c-2b)/2`. -/
theorem exercise_5_18 [DecidableEq K]
    (a b c x : K) (twoNonzero : (2 : K) ≠ 0)
    (outerDistinct : a ≠ c)
    (firstTriple : QuadTriple a b x)
    (secondTriple : QuadTriple b c x) :
    x = (a + c - 2 * b) / 2 := by
  have differenceNonzero : a - c ≠ 0 := by
    intro differenceZero
    apply outerDistinct
    exact sub_eq_zero.mp differenceZero
  have productZero :
      (a - c) * (2 * x - (a + c - 2 * b)) = 0 := by
    unfold QuadTriple at firstTriple secondTriple
    calc
      (a - c) * (2 * x - (a + c - 2 * b)) =
          archimedesFunction a b x -
            archimedesFunction b c x := by
              unfold archimedesFunction
              ring1
      _ = 0 := by rw [firstTriple, secondTriple]; ring1
  have cleared : 2 * x = a + c - 2 * b := by
    have secondFactorZero : 2 * x - (a + c - 2 * b) = 0 := by
      by_cases factorZero : 2 * x - (a + c - 2 * b) = 0
      · exact factorZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero differenceNonzero factorZero)
            productZero)
    exact sub_eq_zero.mp secondFactorZero
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    x = x * (2 * (2 : K)⁻¹) := by rw [twoCancel, mul_one]
    _ = (2 * x) * (2 : K)⁻¹ := by ring1
    _ = (a + c - 2 * b) * (2 : K)⁻¹ := by rw [cleared]

end DivineProportions
