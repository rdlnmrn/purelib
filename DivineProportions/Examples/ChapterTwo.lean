import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Chapter 2 finite-field examples

The source's characteristic-seven arithmetic and characteristic-nineteen
polynomial data are recorded by exact finite calculations.  The `S₅` table is
a literal list evaluation, not a claim that a list enumerates an ambient
carrier.  The characteristic-nineteen factorization is proved as a direct
polynomial identity; no carrier enumeration or root search is used.
-/

namespace DivineProportions

namespace ChapterTwoExamples

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K]

/-- Example 2.1: the three displayed calculations in characteristic seven,
including the fraction sum with both denominator certificates explicit. -/
theorem example_2_1 (sevenZero : (7 : K) = 0) :
    (3 : K) + 5 = 1 ∧
      (3 : K) * 6 = 4 ∧
      (34 : K) / 53 + 19 / 17 = 2 := by
  have fiftyThreeNonzero : (53 : K) ≠ 0 := by
    intro fiftyThreeZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 53 - 15 * 7 := by ring1
      _ = 0 := by rw [fiftyThreeZero, sevenZero]; ring1
  have seventeenNonzero : (17 : K) ≠ 0 := by
    intro seventeenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 5 * 7 - 2 * 17 := by ring1
      _ = 0 := by rw [seventeenZero, sevenZero]; ring1
  have fiftyThreeCancel : (53 : K) * (53 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 53 fiftyThreeNonzero
  have seventeenCancel : (17 : K) * (17 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 17 seventeenNonzero
  have numeratorEquation :
      (34 : K) * 17 + 19 * 53 = 2 * (53 * 17) := by
    calc
      (34 : K) * 17 + 19 * 53 =
          2 * (53 * 17) - 31 * 7 := by ring1
      _ = 2 * (53 * 17) := by rw [sevenZero]; ring1
  constructor
  · calc
      (3 : K) + 5 = 1 + 7 := by ring1
      _ = 1 := by rw [sevenZero]; ring1
  constructor
  · calc
      (3 : K) * 6 = 4 + 2 * 7 := by ring1
      _ = 4 := by rw [sevenZero]; ring1
  · simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (34 : K) * (53 : K)⁻¹ + 19 * (17 : K)⁻¹ =
          34 * (53 : K)⁻¹ * (17 * (17 : K)⁻¹) +
            19 * (17 : K)⁻¹ * (53 * (53 : K)⁻¹) := by
              rw [fiftyThreeCancel, seventeenCancel]
              ring1
      _ = (34 * 17 + 19 * 53) *
          ((53 : K)⁻¹ * (17 : K)⁻¹) := by ring1
      _ = 2 * (53 * 17) * ((53 : K)⁻¹ * (17 : K)⁻¹) := by
        rw [numeratorEquation]
      _ = 2 * (53 * (53 : K)⁻¹) * (17 * (17 : K)⁻¹) := by ring1
      _ = 2 := by rw [fiftyThreeCancel, seventeenCancel]; ring1

/-- The finite expression plotted in Example 2.16. -/
def spreadFiveExpression {R : Type*} [CommRing R] (value : R) : R :=
  value * (16 * value ^ 2 - 20 * value + 5) ^ 2

omit [Nontrivial K] in
/-- Example 2.16: the fifth spread polynomial is exactly the displayed finite
quintic expression; the source's decimal plot adds no further algebraic
claim. -/
theorem example_2_16 (value : K) :
    spreadPolynomial 5 value = spreadFiveExpression value := by
  simp only [spreadPolynomial]
  unfold spreadFiveExpression
  ring1

namespace ExampleTwoSeventeen

/-- Residue labels used in the literal value table from Example 2.17. -/
abbrev Element := Fin 19

instance instNeZeroNineteen : NeZero 19 := ⟨by decide⟩

/-- The nineteen input labels printed in the source table. -/
def inputs : List Element :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The nineteen output labels printed below those inputs. -/
def outputs : List Element :=
  [0, 1, 10, 13, 1, 5, 17, 6, 10, 0, 10, 1, 10, 14, 3, 15, 0, 7, 10]

/-- The same literal quintic expression, specialized to the kernel's modular
operations on the nineteen displayed residue labels. -/
def tableExpression (value : Element) : Element :=
  value * (16 * value ^ 2 - 20 * value + 5) ^ 2

/-- Example 2.17: direct kernel evaluation of the source's literal `S₅`
table.  This theorem checks exactly the displayed labels and makes no claim
that `inputs` is a global enumeration of a carrier. -/
theorem example_2_17 :
    List.map tableExpression inputs = outputs := by
  decide

end ExampleTwoSeventeen

private theorem nine_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (9 : K) ≠ 0 := by
  intro nineZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 19 - 2 * 9 := by ring1
    _ = 0 := by rw [nineteenZero, nineZero]; ring1

private theorem sixteen_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (16 : K) ≠ 0 := by
  intro sixteenZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 6 * 16 - 5 * 19 := by ring1
    _ = 0 := by rw [nineteenZero, sixteenZero]; ring1

private theorem seven_ne_zero_of_nineteen_eq_zero
    (nineteenZero : (19 : K) = 0) : (7 : K) ≠ 0 := by
  intro sevenZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 11 * 7 - 4 * 19 := by ring1
    _ = 0 := by rw [nineteenZero, sevenZero]; ring1

omit [Nontrivial K] in
private theorem square_ne_zero {value : K} (valueNonzero : value ≠ 0) :
    value ^ 2 ≠ 0 := by
  rw [pow_two]
  exact RFAP.ExplicitField.mul_ne_zero valueNonzero valueNonzero

omit [Nontrivial K] in
/-- Example 2.18: the displayed factorization of `S₅` in characteristic
nineteen. -/
theorem example_2_18 (nineteenZero : (19 : K) = 0) (value : K) :
    spreadPolynomial 5 value =
      9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 := by
  have quadraticFactor :
      5 - 20 * value + 16 * value ^ 2 =
        -3 * (value - 9) * (value - 16) := by
    calc
      5 - 20 * value + 16 * value ^ 2 =
          -3 * (value - 9) * (value - 16) +
            19 * (value ^ 2 - 5 * value + 23) := by ring1
      _ = -3 * (value - 9) * (value - 16) := by
        rw [nineteenZero]
        ring1
  calc
    spreadPolynomial 5 value =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
      simp only [spreadPolynomial]
      ring1
    _ = 9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 := by
      rw [quadraticFactor]
      ring1

/-- Example 2.18's complete zero classification.  The proof branches only on
the three displayed candidates; it never enumerates the coefficient field. -/
theorem example_2_18_zeroes [DecidableEq K]
    (nineteenZero : (19 : K) = 0) (value : K) :
    spreadPolynomial 5 value = 0 ↔
      value = 0 ∨ value = 9 ∨ value = 16 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    by_cases valueNine : value = 9
    · exact Or.inr (Or.inl valueNine)
    by_cases valueSixteen : value = 16
    · exact Or.inr (Or.inr valueSixteen)
    · have valueMinusNineNonzero : value - 9 ≠ 0 := by
        intro differenceZero
        exact valueNine (sub_eq_zero.mp differenceZero)
      have valueMinusSixteenNonzero : value - 16 ≠ 0 := by
        intro differenceZero
        exact valueSixteen (sub_eq_zero.mp differenceZero)
      have factoredNonzero :
          9 * value * (value - 9) ^ 2 * (value - 16) ^ 2 ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero
            (RFAP.ExplicitField.mul_ne_zero nineNonzero valueZero)
            (square_ne_zero valueMinusNineNonzero))
          (square_ne_zero valueMinusSixteenNonzero)
      exact False.elim (factoredNonzero
        ((example_2_18 nineteenZero value).symm.trans polynomialZero))
  · intro alternatives
    rcases alternatives with valueZero | valueNine | valueSixteen
    · rw [example_2_18 nineteenZero value, valueZero]
      ring1
    · rw [example_2_18 nineteenZero value, valueNine]
      ring1
    · rw [example_2_18 nineteenZero value, valueSixteen]
      ring1

/-- The explicit nonvanishing cofactor certificate showing that zero has
multiplicity exactly one in Example 2.18. -/
theorem example_2_18_zero_multiplicity_one
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      spreadPolynomial 5 value =
        (value - 0) ^ 1 *
          (9 * (value - 9) ^ 2 * (value - 16) ^ 2)) ∧
      9 * ((0 : K) - 9) ^ 2 * ((0 : K) - 16) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sixteenNonzero := sixteen_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero nineNonzero
        (square_ne_zero (by
          rw [zero_sub]
          exact neg_ne_zero.mpr nineNonzero)))
      (square_ne_zero (by
        rw [zero_sub]
        exact neg_ne_zero.mpr sixteenNonzero))

/-- The explicit nonvanishing cofactor certificate showing that nine has
multiplicity exactly two in Example 2.18. -/
theorem example_2_18_nine_multiplicity_two
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      spreadPolynomial 5 value =
        (value - 9) ^ 2 *
          (9 * value * (value - 16) ^ 2)) ∧
      (9 : K) * 9 * (9 - 16) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sevenNonzero := seven_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · have differenceNonzero : (9 : K) - 16 ≠ 0 := by
      intro differenceZero
      apply sevenNonzero
      calc
        (7 : K) = -(9 - 16) := by ring1
        _ = 0 := by rw [differenceZero]; ring1
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero nineNonzero nineNonzero)
      (square_ne_zero differenceNonzero)

/-- The explicit nonvanishing cofactor certificate showing that sixteen has
multiplicity exactly two in Example 2.18. -/
theorem example_2_18_sixteen_multiplicity_two
    (nineteenZero : (19 : K) = 0) :
    (∀ value : K,
      spreadPolynomial 5 value =
        (value - 16) ^ 2 *
          (9 * value * (value - 9) ^ 2)) ∧
      (9 : K) * 16 * (16 - 9) ^ 2 ≠ 0 := by
  have nineNonzero := nine_ne_zero_of_nineteen_eq_zero nineteenZero
  have sixteenNonzero := sixteen_ne_zero_of_nineteen_eq_zero nineteenZero
  have sevenNonzero := seven_ne_zero_of_nineteen_eq_zero nineteenZero
  constructor
  · intro value
    rw [example_2_18 nineteenZero value]
    ring1
  · have differenceNonzero : (16 : K) - 9 ≠ 0 := by
      intro differenceZero
      apply sevenNonzero
      calc
        (7 : K) = 16 - 9 := by ring1
        _ = 0 := differenceZero
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero nineNonzero sixteenNonzero)
      (square_ne_zero differenceNonzero)

end ChapterTwoExamples

end DivineProportions
