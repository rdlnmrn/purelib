import DivineProportions.Stars.OrderSeven
import DivineProportions.Algebra.FieldThirteen
import DivineProportions.Algebra.FieldNineteen
import mathlib.RFAP.ConstructiveFraction
import mathlib.RFAP.IntegerPolynomialCertificate

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace DivineProportions

namespace ChapterFourteenExamples

/-- A finite Euler obstruction: if every displayed scalar satisfies the
degree-`2e+1` Frobenius equation and `a^e=-1`, then `a` cannot be the square
of a nonzero scalar. -/
theorem not_nonzeroSquare_of_frobenius_neg
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    (value : K) (exponent : Nat) (twoNonzero : (2 : K) ≠ 0)
    (valuePower : value ^ exponent = -1)
    (frobenius : ∀ root : K, root ^ (2 * exponent + 1) = root) :
    ¬ IsNonzeroSquare value := by
  rintro ⟨root, rootNonzero, valueSquare⟩
  have oddPower : root ^ (2 * exponent + 1) = -root := by
    calc
      root ^ (2 * exponent + 1) = root ^ (2 * exponent) * root := by
        rw [pow_add, pow_one]
      _ = (root ^ 2) ^ exponent * root := by rw [pow_mul]
      _ = value ^ exponent * root := by rw [← valueSquare]
      _ = -root := by rw [valuePower]; ring1
  have rootEqNegative : root = -root :=
    (frobenius root).symm.trans oddPower
  have addRoot := congrArg (fun value : K => value + root) rootEqNegative
  have twiceRootZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root + root := by ring1
      _ = -root + root := addRoot
      _ = 0 := by ring1
  exact (RFAP.ExplicitField.mul_ne_zero twoNonzero rootNonzero)
    twiceRootZero

namespace ExampleFourteenOne

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

private theorem no_star_of_not_square
    (twoNonzero : (2 : K) ≠ 0) (notSquare : ¬ IsNonzeroSquare (3 : K)) :
    ¬ Nonempty (RegularThreeStar K) := by
  intro star
  exact notSquare ((order_three_star twoNonzero).1 star)

/-- The `F₃` clause: here the scalar `3` itself vanishes. -/
theorem field_three
    (threeZero : (3 : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    ¬ Nonempty (RegularThreeStar K) := by
  apply no_star_of_not_square twoNonzero
  rintro ⟨root, rootNonzero, threeSquare⟩
  have squareZero : root ^ 2 = 0 := threeSquare.symm.trans threeZero
  have squareNonzero : root ^ 2 ≠ 0 := by
    simpa [pow_two] using
      RFAP.ExplicitField.mul_ne_zero rootNonzero rootNonzero
  exact squareNonzero squareZero

/-- The `F₅` clause, using `3²=-1` and `x⁵=x`. -/
theorem field_five
    (fiveZero : (5 : K) = 0) (frobenius : ∀ value : K, value ^ 5 = value) :
    ¬ Nonempty (RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 3 * 2 - 5 := by ring1
      _ = 0 := by rw [twoZero, fiveZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply not_nonzeroSquare_of_frobenius_neg 3 2 twoNonzero
  · calc
      (3 : K) ^ 2 = -1 + 2 * 5 := by ring1
      _ = -1 := by rw [fiveZero]; ring1
  · simpa only using frobenius

/-- The `F₇` clause, using `3³=-1` and `x⁷=x`. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (frobenius : ∀ value : K, value ^ 7 = value) :
    ¬ Nonempty (RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 4 * 2 - 7 := by ring1
      _ = 0 := by rw [twoZero, sevenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply not_nonzeroSquare_of_frobenius_neg 3 3 twoNonzero
  · calc
      (3 : K) ^ 3 = -1 + 4 * 7 := by ring1
      _ = -1 := by rw [sevenZero]; ring1
  · simpa only using frobenius

/-- The `F₁₇` clause, using `3⁸=-1` and `x¹⁷=x`. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value) :
    ¬ Nonempty (RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 9 * 2 - 17 := by ring1
      _ = 0 := by rw [twoZero, seventeenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply not_nonzeroSquare_of_frobenius_neg 3 8 twoNonzero
  · calc
      (3 : K) ^ 8 = -1 + 386 * 17 := by ring1
      _ = -1 := by rw [seventeenZero]; ring1
  · simpa only using frobenius

/-- The `F₁₉` clause, using `3⁹=-1` and `x¹⁹=x`. -/
theorem field_nineteen
    (nineteenZero : (19 : K) = 0)
    (frobenius : ∀ value : K, value ^ 19 = value) :
    ¬ Nonempty (RegularThreeStar K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 10 * 2 - 19 := by ring1
      _ = 0 := by rw [twoZero, nineteenZero]; ring1
  apply no_star_of_not_square twoNonzero
  apply not_nonzeroSquare_of_frobenius_neg 3 9 twoNonzero
  · calc
      (3 : K) ^ 9 = -1 + 1036 * 19 := by ring1
      _ = -1 := by rw [nineteenZero]; ring1
  · simpa only using frobenius

end ExampleFourteenOne

namespace ExampleFourteenThree

abbrev F₁₃ := FieldThirteen.Element

/-- The source's literal `F₁₃` star from the square root `4²=3`. -/
def star : RegularThreeStar F₁₃ :=
  orderThreeStar 4 (by decide) (by decide) (by decide)

theorem example_14_3 :
    star.line₀.a = 0 ∧ star.line₀.b = 1 ∧
      star.line₁.a = 4 ∧ star.line₁.b = 1 ∧
      star.line₂.a = 9 ∧ star.line₂.b = 1 := by
  decide

end ExampleFourteenThree

namespace ExampleFourteenFour

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The rational clause of Example 14.4: the exact reduced-fraction
certificate excludes a square root of three and hence an order-three star. -/
theorem example_14_4 : ¬ Nonempty (RegularThreeStar Rational) := by
  intro star
  have twoNonzero : (2 : Rational) ≠ 0 := by decide
  have rationalNontrivial : Nontrivial Rational := by
    constructor
    refine ⟨0, 1, ?_⟩
    intro zeroOne
    apply twoNonzero
    calc
      (2 : Rational) = 1 + 1 := by ring1
      _ = 0 + 0 := by rw [← zeroOne]
      _ = 0 := by ring1
  rcases (order_three_star (K := Rational) twoNonzero).1 star with
    ⟨root, _rootNonzero, threeSquare⟩
  exact RFAP.ConstructiveFraction.square_ne_three root threeSquare.symm

end ExampleFourteenFour

private theorem square_eq_zero
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    {value : K} (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact False.elim (squareNonzero squareZero)

/-- Every nonzero root of `S₅` displays a square root `8s-5` of five.
This is the finite complete-square calculation used by Examples 14.5–14.7. -/
theorem nonzero_spreadPolynomial_five_root_gives_square_five
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    (value : K) (valueNonzero : value ≠ 0)
    (polynomialZero : spreadPolynomial 5 value = 0)
    (fiveNonzero : (5 : K) ≠ 0) : IsNonzeroSquare (5 : K) := by
  rw [spreadPolynomial_five_formula] at polynomialZero
  have factorSquareZero :
      (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
    by_cases factorZero :
        (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
    · exact factorZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero valueNonzero factorZero)
          polynomialZero)
  have factorZero := square_eq_zero factorSquareZero
  let root := 8 * value - 5
  have rootSquare : root ^ 2 = (5 : K) := by
    calc
      root ^ 2 = 5 + 4 * (5 - 20 * value + 16 * value ^ 2) := by
        unfold root
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply fiveNonzero
    calc
      (5 : K) = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  exact ⟨root, rootNonzero, rootSquare.symm⟩

namespace ExampleFourteenFive

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] in
private theorem only_zero_of_five_nonsquare
    (fiveNonzero : (5 : K) ≠ 0)
    (fiveNotSquare : ¬ IsNonzeroSquare (5 : K))
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · exact False.elim (fiveNotSquare
      (nonzero_spreadPolynomial_five_root_gives_square_five value
        valueZero polynomialZero fiveNonzero))

/-- The `F₃` order-five polynomial has no nonzero root. -/
theorem field_three
    (threeZero : (3 : K) = 0)
    (frobenius : ∀ value : K, value ^ 3 = value)
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 2 - 3 := by ring1
      _ = 0 := by rw [twoZero, threeZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 5 - 3 := by ring1
      _ = 0 := by rw [fiveZero, threeZero]; ring1
  apply only_zero_of_five_nonsquare fiveNonzero
  apply not_nonzeroSquare_of_frobenius_neg 5 1 twoNonzero
  · calc
      (5 : K) ^ 1 = -1 + 2 * 3 := by ring1
      _ = -1 := by rw [threeZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

omit [Nontrivial K] in
/-- In characteristic five the displayed polynomial is exactly `s⁵`, so
again its only root is zero. -/
theorem field_five
    (fiveZero : (5 : K) = 0)
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  have factorAsSquare :
      5 - 20 * value + 16 * value ^ 2 = value ^ 2 := by
    calc
      5 - 20 * value + 16 * value ^ 2 =
          value ^ 2 + (1 - 4 * value + 3 * value ^ 2) * 5 := by ring1
      _ = value ^ 2 := by rw [fiveZero]; ring1
  rw [spreadPolynomial_five_formula, factorAsSquare] at polynomialZero
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero
        valueZero valueZero
    have fourthNonzero := RFAP.ExplicitField.mul_ne_zero
      squareNonzero squareNonzero
    apply False.elim
    exact (RFAP.ExplicitField.mul_ne_zero valueZero (by
      simpa [pow_two] using fourthNonzero)) polynomialZero

/-- The `F₇` order-five polynomial has no nonzero root. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (frobenius : ∀ value : K, value ^ 7 = value)
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 4 * 2 - 7 := by ring1
      _ = 0 := by rw [twoZero, sevenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 7 - 5 := by ring1
      _ = 0 := by rw [sevenZero, fiveZero]; ring1
  apply only_zero_of_five_nonsquare fiveNonzero
  apply not_nonzeroSquare_of_frobenius_neg 5 3 twoNonzero
  · calc
      (5 : K) ^ 3 = -1 + 18 * 7 := by ring1
      _ = -1 := by rw [sevenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

/-- The `F₁₃` order-five polynomial has no nonzero root. -/
theorem field_thirteen
    (thirteenZero : (13 : K) = 0)
    (frobenius : ∀ value : K, value ^ 13 = value)
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 7 * 2 - 13 := by ring1
      _ = 0 := by rw [twoZero, thirteenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 13 - 5 * 5 := by ring1
      _ = 0 := by rw [thirteenZero, fiveZero]; ring1
  apply only_zero_of_five_nonsquare fiveNonzero
  apply not_nonzeroSquare_of_frobenius_neg 5 6 twoNonzero
  · calc
      (5 : K) ^ 6 = -1 + 1202 * 13 := by ring1
      _ = -1 := by rw [thirteenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

/-- The `F₁₇` order-five polynomial has no nonzero root. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value)
    (value : K) (polynomialZero : spreadPolynomial 5 value = 0) :
    value = 0 := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 9 * 2 - 17 := by ring1
      _ = 0 := by rw [twoZero, seventeenZero]; ring1
  have fiveNonzero : (5 : K) ≠ 0 := by
    intro fiveZero
    apply twoNonzero
    calc
      (2 : K) = 17 - 3 * 5 := by ring1
      _ = 0 := by rw [seventeenZero, fiveZero]; ring1
  apply only_zero_of_five_nonsquare fiveNonzero
  apply not_nonzeroSquare_of_frobenius_neg 5 8 twoNonzero
  · calc
      (5 : K) ^ 8 = -1 + 22978 * 17 := by ring1
      _ = -1 := by rw [seventeenZero]; ring1
  · simpa only using frobenius
  · exact polynomialZero

end ExampleFourteenFive

namespace ExampleFourteenSix

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- Over the prime-field arithmetic of characteristic eleven, the only
roots of `S₅` are the printed values `0`, `7`, and `8`. -/
theorem root_classification
    (elevenZero : (11 : K) = 0) (value : K) :
    spreadPolynomial 5 value = 0 ↔
      value = 0 ∨ value = 7 ∨ value = 8 := by
  rw [spreadPolynomial_five_formula]
  constructor
  · intro productZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have factorSquareZero :
          (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
        by_cases zero : (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
        · exact zero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero valueZero zero) productZero)
      have factorZero := square_eq_zero factorSquareZero
      have factored : (5 : K) * (value - 7) * (value - 8) = 0 := by
        calc
          (5 : K) * (value - 7) * (value - 8) =
              (5 - 20 * value + 16 * value ^ 2) +
                (25 - 5 * value - value ^ 2) * 11 := by ring1
          _ = 0 := by rw [factorZero, elevenZero]; ring1
      have fiveNonzero : (5 : K) ≠ 0 := by
        intro fiveZero
        apply (one_ne_zero : (1 : K) ≠ 0)
        calc
          (1 : K) = 11 - 2 * 5 := by ring1
          _ = 0 := by rw [elevenZero, fiveZero]; ring1
      by_cases firstZero : value - 7 = 0
      · exact Or.inl (sub_eq_zero.mp firstZero)
      · right
        apply sub_eq_zero.mp
        by_cases secondZero : value - 8 = 0
        · exact secondZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero fiveNonzero firstZero)
              secondZero) factored)
  · intro alternatives
    rcases alternatives with valueZero | valueSeven | valueEight
    · rw [valueZero]; ring1
    · rw [valueSeven]
      calc
        (7 : K) * (5 - 20 * 7 + 16 * 7 ^ 2) ^ 2 =
            7 * (59 * 11) ^ 2 := by ring1
        _ = 0 := by rw [elevenZero]; ring1
    · rw [valueEight]
      calc
        (8 : K) * (5 - 20 * 8 + 16 * 8 ^ 2) ^ 2 =
            8 * (79 * 11) ^ 2 := by ring1
        _ = 0 := by rw [elevenZero]; ring1

/-- The two nonzero roots `7` and `8` are not spread numbers in `F₁₁`;
the finite obstructions are respectively that `2` and `-1` are nonsquares. -/
theorem nonzero_roots_not_spread
    (elevenZero : (11 : K) = 0)
    (frobenius : ∀ value : K, value ^ 11 = value) :
    ¬ IsSpreadNumber (7 : K) ∧ ¬ IsSpreadNumber (8 : K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 6 * 2 - 11 := by ring1
      _ = 0 := by rw [twoZero, elevenZero]; ring1
  have twoNotSquare :=
    not_nonzeroSquare_of_frobenius_neg (2 : K) 5 twoNonzero (by
      calc
        (2 : K) ^ 5 = -1 + 3 * 11 := by ring1
        _ = -1 := by rw [elevenZero]; ring1) (by simpa only using frobenius)
  have negativeOneNotSquare :=
    not_nonzeroSquare_of_frobenius_neg (-1 : K) 5 twoNonzero (by
      ring1) (by simpa only using frobenius)
  constructor
  · rintro ⟨root, rootSquare⟩
    apply twoNotSquare
    have radicand : (7 : K) * (1 - 7) = 2 := by
      calc
        (7 : K) * (1 - 7) = 2 - 4 * 11 := by ring1
        _ = 2 := by rw [elevenZero]; ring1
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply twoNonzero
      calc
        (2 : K) = 7 * (1 - 7) := radicand.symm
        _ = root ^ 2 := rootSquare
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨root, rootNonzero, radicand.symm.trans rootSquare⟩
  · rintro ⟨root, rootSquare⟩
    apply negativeOneNotSquare
    have radicand : (8 : K) * (1 - 8) = -1 := by
      calc
        (8 : K) * (1 - 8) = -1 - 5 * 11 := by ring1
        _ = -1 := by rw [elevenZero]; ring1
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply (one_ne_zero : (1 : K) ≠ 0)
      calc
        (1 : K) = -((8 : K) * (1 - 8)) := by rw [radicand]; ring1
        _ = -(root ^ 2) := by rw [rootSquare]
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨root, rootNonzero, radicand.symm.trans rootSquare⟩

end ExampleFourteenSix

namespace ExampleFourteenSeven

abbrev F₁₉ := FieldNineteen.Element

/-- The source's literal `F₁₉` star is the order-five construction
with `r=9` and `v=7`, normalized to slopes `0,2,5,-5,-2`. -/
def star : RegularFiveStar F₁₉ :=
  orderFiveStar 9 7 (by decide) (by decide) (by decide) (by decide)

private def printedLine (slope : F₁₉) : Line F₁₉ where
  a := slope
  b := 1
  c := 0
  direction_nonzero := Or.inr (by decide)

theorem example_14_7_lines :
    star.line₀.Equivalent (printedLine 0) ∧
      star.line₁.Equivalent (printedLine 2) ∧
      star.line₂.Equivalent (printedLine 5) ∧
      star.line₃.Equivalent (printedLine (-5)) ∧
      star.line₄.Equivalent (printedLine (-2)) := by
  unfold Line.Equivalent star orderFiveStar printedLine orderFiveLine₀
    orderFiveLine₁ orderFiveLine₂ orderFiveLine₃ orderFiveLine₄
  decide

/-- The two printed nonzero roots and their spread-number witnesses. -/
theorem example_14_7_values :
    spreadPolynomial 5 (9 : F₁₉) = 0 ∧
      spreadPolynomial 5 (16 : F₁₉) = 0 ∧
      IsSpreadNumber (9 : F₁₉) ∧ IsSpreadNumber (16 : F₁₉) := by
  refine ⟨by decide, by decide, ⟨2, by decide⟩, ⟨8, by decide⟩⟩

end ExampleFourteenSeven

namespace ExampleFourteenEight

namespace Certificate

open RFAP.IntegerPolynomialCertificate

/-- Ascending integer coefficients of the cubic factor in `S₇`. -/
private def cubic : List Int := [7, -56, 112, -64]

private theorem eval_cubic
    {K : Type*} [RFAP.ExplicitField K] (value : K) :
    eval cubic value =
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 := by
  simp only [cubic, eval_cons, eval_nil]
  ring1

/-- Literal finite Bezout certificate modulo three. -/
private def three : BezoutCertificate 3 cubic where
  left := [1, 0, 1]
  right := [1, -1, 1]
  correction := [2, -19, 40, -40, 37, -21]
  identity := by decide

/-- Literal finite Bezout certificate modulo five. -/
private def five : BezoutCertificate 5 cubic where
  left := [-2, -1, 2, 1, -1]
  right := [0, 1, 1]
  correction := [-3, 21, -31, -18, 45, 8, -35, 13]
  identity := by decide

/-- Literal finite Bezout certificate modulo eleven. -/
private def eleven : BezoutCertificate 11 cubic where
  left := [-3, -3, -5, 5, 3, 2, -2, 3, 2, 0, -3]
  right := [4, -5, -5]
  correction :=
    [-2, 13, -18, 16, -57, 66, -10, 15, -46, 32, 1, 4, -31, 17]
  identity := by decide

/-- Literal finite Bezout certificate modulo seventeen. -/
private def seventeen : BezoutCertificate 17 cubic where
  left := [5, -8, -3, 6, 1, 6, -3, -4, -2, 6, 7, 0, 6, -7, 1, 0, 5]
  right := [4, 1, -3]
  correction :=
    [2, -20, 58, -59, -9, 50, -37, 44, -30, -6,
      -15, 24, 26, -49, 63, -72, 35, -20, 33, -19]
  identity := by decide

/-- Literal finite Bezout certificate modulo nineteen. -/
private def nineteen : BezoutCertificate 19 cubic where
  left :=
    [-8, -7, 1, -5, -6, -5, -6, 7, -5, -6, 1, 4, -9, -2, -1,
      -4, 1, -5, -3]
  right := [0, -3, -2]
  correction :=
    [-3, 21, -26, -19, 42, -17, -6, 11, -41, 74, -35,
      -20, 11, 46, -61, 20, 13, -25, 33, -24, -1, 10]
  identity := by decide

/-- Literal finite Bezout certificate modulo twenty-three. -/
private def twentyThree : BezoutCertificate 23 cubic where
  left :=
    [10, 11, -4, -7, 10, 1, -9, 10, -10, 3, 6, -6, 5, -3, -11,
      9, 7, 2, 6, 11, 7, -6, 3]
  right := [0, -7, 8]
  correction :=
    [3, -21, 21, 33, -30, -47, 63, 2, -74, 99, -82, 26, 37,
      -59, 45, 1, -65, 58, 6, -21, -1, 18, 19, -56, 31, -8]
  identity := by decide

private theorem only_zero_of_certificate
    {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]
    {modulus : Nat} (certificate : BezoutCertificate modulus cubic)
    (modulusZero : (modulus : K) = 0)
    (frobeniusLaw : ∀ value : K, value ^ modulus = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have cubicNonzero :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
      intro cubicZero
      apply no_common_root certificate modulusZero value
      · rw [eval_cubic]
        exact cubicZero
      · exact frobeniusLaw value
    have cubicSquareNonzero :
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 ≠ 0 := by
      simpa [pow_two] using
        RFAP.ExplicitField.mul_ne_zero cubicNonzero cubicNonzero
    rw [spreadPolynomial_seven_formula] at polynomialZero
    exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero valueZero cubicSquareNonzero)
        polynomialZero)

end Certificate

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- The characteristic-three clause of Example 14.8. -/
theorem field_three
    (threeZero : (3 : K) = 0)
    (frobenius : ∀ value : K, value ^ 3 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.three threeZero
    frobenius value polynomialZero

/-- The characteristic-five clause of Example 14.8. -/
theorem field_five
    (fiveZero : (5 : K) = 0)
    (frobenius : ∀ value : K, value ^ 5 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.five fiveZero
    frobenius value polynomialZero

omit [Nontrivial K] in
/-- In characteristic seven the cubic factor is `-s³`, so the seventh
spread polynomial again has only its zero root. -/
theorem field_seven
    (sevenZero : (7 : K) = 0)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have valueSquareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    have valueCubeNonzero : value ^ 3 ≠ 0 := by
      simpa [pow_succ] using
        RFAP.ExplicitField.mul_ne_zero valueSquareNonzero valueZero
    have cubicEq :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          -(value ^ 3) := by
      calc
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
            -(value ^ 3) +
              (1 - 8 * value + 16 * value ^ 2 - 9 * value ^ 3) * 7 := by
          ring1
        _ = -(value ^ 3) := by rw [sevenZero]; ring1
    have cubicNonzero :
        7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
      rw [cubicEq]
      exact neg_ne_zero.mpr valueCubeNonzero
    have cubicSquareNonzero :
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 ≠ 0 := by
      simpa [pow_two] using
        RFAP.ExplicitField.mul_ne_zero cubicNonzero cubicNonzero
    rw [spreadPolynomial_seven_formula] at polynomialZero
    exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero valueZero cubicSquareNonzero)
        polynomialZero)

/-- The characteristic-eleven clause of Example 14.8. -/
theorem field_eleven
    (elevenZero : (11 : K) = 0)
    (frobenius : ∀ value : K, value ^ 11 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.eleven elevenZero
    frobenius value polynomialZero

/-- The characteristic-seventeen clause of Example 14.8. -/
theorem field_seventeen
    (seventeenZero : (17 : K) = 0)
    (frobenius : ∀ value : K, value ^ 17 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.seventeen seventeenZero
    frobenius value polynomialZero

/-- The characteristic-nineteen clause of Example 14.8. -/
theorem field_nineteen
    (nineteenZero : (19 : K) = 0)
    (frobenius : ∀ value : K, value ^ 19 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.nineteen nineteenZero
    frobenius value polynomialZero

/-- The characteristic-twenty-three clause of Example 14.8. -/
theorem field_twentyThree
    (twentyThreeZero : (23 : K) = 0)
    (frobenius : ∀ value : K, value ^ 23 = value)
    (value : K) (polynomialZero : spreadPolynomial 7 value = 0) :
    value = 0 :=
  Certificate.only_zero_of_certificate Certificate.twentyThree
    twentyThreeZero frobenius value polynomialZero

omit [Nontrivial K] in
/-- In characteristic thirteen the cubic factor has exactly the three
printed roots. -/
theorem cubic_root_classification
    (thirteenZero : (13 : K) = 0) (value : K) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ↔
      value = 2 ∨ value = 5 ∨ value = 11 := by
  have factored :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
        (value - 2) * (value - 5) * (value - 11) := by
    calc
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          (value - 2) * (value - 5) * (value - 11) +
            (9 - 11 * value + 10 * value ^ 2 - 5 * value ^ 3) * 13 := by
        ring1
      _ = (value - 2) * (value - 5) * (value - 11) := by
        rw [thirteenZero]
        ring1
  rw [factored]
  constructor
  · intro productZero
    by_cases firstZero : value - 2 = 0
    · exact Or.inl (sub_eq_zero.mp firstZero)
    · right
      by_cases secondZero : value - 5 = 0
      · exact Or.inl (sub_eq_zero.mp secondZero)
      · right
        apply sub_eq_zero.mp
        by_cases thirdZero : value - 11 = 0
        · exact thirdZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) productZero)
  · rintro (valueTwo | valueFive | valueEleven)
    · rw [valueTwo]
      ring1
    · rw [valueFive]
      ring1
    · rw [valueEleven]
      ring1

omit [Nontrivial K] in
/-- The complete `S₇` root classification in characteristic thirteen. -/
theorem field_thirteen_roots
    (thirteenZero : (13 : K) = 0) (value : K) :
    spreadPolynomial 7 value = 0 ↔
      value = 0 ∨ value = 2 ∨ value = 5 ∨ value = 11 := by
  constructor
  · intro polynomialZero
    rw [spreadPolynomial_seven_formula] at polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have cubicSquareZero :
          (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0 := by
        by_cases squareZero :
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero valueZero squareZero)
              polynomialZero)
      exact (cubic_root_classification thirteenZero value).1
        (square_eq_zero cubicSquareZero)
  · rintro (valueZero | valueTwo | valueFive | valueEleven)
    · rw [valueZero, spreadPolynomial_seven_formula]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2 (Or.inl valueTwo)]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2
          (Or.inr (Or.inl valueFive))]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification thirteenZero value).2
          (Or.inr (Or.inr valueEleven))]
      ring1

omit [Nontrivial K] [DecidableEq K] in
private theorem not_spread_of_radicand_nonsquare
    (value : K)
    (radicandNonzero : value * (1 - value) ≠ 0)
    (radicandNotSquare : ¬ IsNonzeroSquare (value * (1 - value))) :
    ¬ IsSpreadNumber value := by
  rintro ⟨root, rootSquare⟩
  apply radicandNotSquare
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply radicandNonzero
    calc
      value * (1 - value) = root ^ 2 := rootSquare
      _ = 0 := by rw [rootZero]; ring1
  exact ⟨root, rootNonzero, rootSquare⟩

/-- The three nonzero `S₇` roots in characteristic thirteen are not spread
numbers, exactly as asserted in Example 14.8. -/
theorem field_thirteen_roots_not_spread
    (thirteenZero : (13 : K) = 0)
    (frobenius : ∀ value : K, value ^ 13 = value) :
    ¬ IsSpreadNumber (2 : K) ∧
      ¬ IsSpreadNumber (5 : K) ∧ ¬ IsSpreadNumber (11 : K) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 7 * 2 - 13 := by ring1
      _ = 0 := by rw [twoZero, thirteenZero]; ring1
  have elevenNonzero : (11 : K) ≠ 0 := by
    intro elevenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 6 * 13 - 7 * 11 := by ring1
      _ = 0 := by rw [thirteenZero, elevenZero]; ring1
  have sixNonzero : (6 : K) ≠ 0 := by
    intro sixZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 13 - 2 * 6 := by ring1
      _ = 0 := by rw [thirteenZero, sixZero]; ring1
  have sevenNonzero : (7 : K) ≠ 0 := by
    intro sevenZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 2 * 7 - 13 := by ring1
      _ = 0 := by rw [sevenZero, thirteenZero]; ring1
  have elevenNotSquare :=
    not_nonzeroSquare_of_frobenius_neg (11 : K) 6 twoNonzero (by
      calc
        (11 : K) ^ 6 = -1 + 136274 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have sixNotSquare :=
    not_nonzeroSquare_of_frobenius_neg (6 : K) 6 twoNonzero (by
      calc
        (6 : K) ^ 6 = -1 + 3589 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have sevenNotSquare :=
    not_nonzeroSquare_of_frobenius_neg (7 : K) 6 twoNonzero (by
      calc
        (7 : K) ^ 6 = -1 + 9050 * 13 := by ring1
        _ = -1 := by rw [thirteenZero]; ring1)
      (by simpa only using frobenius)
  have radicandTwo : (2 : K) * (1 - 2) = 11 := by
    calc
      (2 : K) * (1 - 2) = 11 - 13 := by ring1
      _ = 11 := by rw [thirteenZero]; ring1
  have radicandFive : (5 : K) * (1 - 5) = 6 := by
    calc
      (5 : K) * (1 - 5) = 6 - 2 * 13 := by ring1
      _ = 6 := by rw [thirteenZero]; ring1
  have radicandEleven : (11 : K) * (1 - 11) = 7 := by
    calc
      (11 : K) * (1 - 11) = 7 - 9 * 13 := by ring1
      _ = 7 := by rw [thirteenZero]; ring1
  refine ⟨not_spread_of_radicand_nonsquare 2 ?_ ?_,
    not_spread_of_radicand_nonsquare 5 ?_ ?_,
    not_spread_of_radicand_nonsquare 11 ?_ ?_⟩
  · rw [radicandTwo]
    exact elevenNonzero
  · rw [radicandTwo]
    exact elevenNotSquare
  · rw [radicandFive]
    exact sixNonzero
  · rw [radicandFive]
    exact sixNotSquare
  · rw [radicandEleven]
    exact sevenNonzero
  · rw [radicandEleven]
    exact sevenNotSquare

end ExampleFourteenEight

namespace ExampleFourteenNine

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [DecidableEq K] in
private theorem twoNonzero (twentyNineZero : (29 : K) = 0) :
    (2 : K) ≠ 0 := by
  intro twoZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 15 * 2 - 29 := by ring1
    _ = 0 := by rw [twoZero, twentyNineZero]; ring1

omit [DecidableEq K] in
private theorem sixNonzero (twentyNineZero : (29 : K) = 0) :
    (6 : K) ≠ 0 := by
  intro sixZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = 5 * 6 - 29 := by ring1
    _ = 0 := by rw [sixZero, twentyNineZero]; ring1

omit [Nontrivial K] [DecidableEq K] in
private theorem cubicSixZero (twentyNineZero : (29 : K) = 0) :
    7 - 56 * (6 : K) + 112 * (6 : K) ^ 2 - 64 * (6 : K) ^ 3 = 0 := by
  calc
    7 - 56 * (6 : K) + 112 * (6 : K) ^ 2 - 64 * (6 : K) ^ 3 =
        -349 * 29 := by ring1
    _ = 0 := by rw [twentyNineZero]; ring1

omit [Nontrivial K] [DecidableEq K] in
private theorem twelveSpreadSquare (twentyNineZero : (29 : K) = 0) :
    (12 : K) ^ 2 = 6 * (1 - 6) := by
  calc
    (12 : K) ^ 2 = 6 * (1 - 6) + 6 * 29 := by ring1
    _ = 6 * (1 - 6) := by rw [twentyNineZero]; ring1

/-- The source's characteristic-twenty-nine star, constructed from the
spread `6` and the finite square witness `12²=6(1-6)`. -/
def star (twentyNineZero : (29 : K) = 0) : RegularSevenStar K :=
  orderSevenStar 6 12 (sixNonzero twentyNineZero)
    (cubicSixZero twentyNineZero) (twelveSpreadSquare twentyNineZero)
    (twoNonzero twentyNineZero)

private theorem star_initial (twentyNineZero : (29 : K) = 0) :
    (star twentyNineZero).initial =
      orderSevenInitialPair 6 12 (sixNonzero twentyNineZero)
        (twelveSpreadSquare twentyNineZero) := rfl

/-- The characteristic-twenty-nine cubic factor has exactly the three
printed roots `6`, `7`, and `25`. -/
theorem cubic_root_classification
    (twentyNineZero : (29 : K) = 0) (value : K) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ↔
      value = 6 ∨ value = 7 ∨ value = 25 := by
  have negativeSixNonzero : (-6 : K) ≠ 0 :=
    neg_ne_zero.mpr (sixNonzero twentyNineZero)
  have factored :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
        -6 * ((value - 6) * (value - 7) * (value - 25)) := by
    calc
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 =
          -6 * ((value - 6) * (value - 7) * (value - 25)) +
            (-217 + 74 * value - 4 * value ^ 2 - 2 * value ^ 3) * 29 := by
        ring1
      _ = -6 * ((value - 6) * (value - 7) * (value - 25)) := by
        rw [twentyNineZero]
        ring1
  rw [factored]
  constructor
  · intro scaledProductZero
    have productZero : (value - 6) * (value - 7) * (value - 25) = 0 := by
      by_cases productZero :
          (value - 6) * (value - 7) * (value - 25) = 0
      · exact productZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero negativeSixNonzero productZero)
            scaledProductZero)
    by_cases firstZero : value - 6 = 0
    · exact Or.inl (sub_eq_zero.mp firstZero)
    · right
      by_cases secondZero : value - 7 = 0
      · exact Or.inl (sub_eq_zero.mp secondZero)
      · right
        apply sub_eq_zero.mp
        by_cases thirdZero : value - 25 = 0
        · exact thirdZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero firstZero secondZero)
              thirdZero) productZero)
  · rintro (valueSix | valueSeven | valueTwentyFive)
    · rw [valueSix]
      ring1
    · rw [valueSeven]
      ring1
    · rw [valueTwentyFive]
      ring1

/-- The complete root classification of `S₇` in characteristic twenty-nine. -/
theorem roots
    (twentyNineZero : (29 : K) = 0) (value : K) :
    spreadPolynomial 7 value = 0 ↔
      value = 0 ∨ value = 6 ∨ value = 7 ∨ value = 25 := by
  constructor
  · intro polynomialZero
    rw [spreadPolynomial_seven_formula] at polynomialZero
    by_cases valueZero : value = 0
    · exact Or.inl valueZero
    · right
      have cubicSquareZero :
          (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0 := by
        by_cases squareZero :
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero valueZero squareZero)
              polynomialZero)
      exact (cubic_root_classification twentyNineZero value).1
        (square_eq_zero cubicSquareZero)
  · rintro (valueZero | valueSix | valueSeven | valueTwentyFive)
    · rw [valueZero, spreadPolynomial_seven_formula]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2 (Or.inl valueSix)]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2
          (Or.inr (Or.inl valueSeven))]
      ring1
    · rw [spreadPolynomial_seven_formula,
        (cubic_root_classification twentyNineZero value).2
          (Or.inr (Or.inr valueTwentyFive))]
      ring1

omit [Nontrivial K] [DecidableEq K] in
/-- All three nonzero roots are spread numbers, with the literal finite
square witnesses `12`, `4`, and `3`. -/
theorem values_are_spread (twentyNineZero : (29 : K) = 0) :
    IsSpreadNumber (6 : K) ∧ IsSpreadNumber (7 : K) ∧
      IsSpreadNumber (25 : K) := by
  refine ⟨⟨12, ?_⟩, ⟨4, ?_⟩, ⟨3, ?_⟩⟩
  · exact (twelveSpreadSquare twentyNineZero).symm
  · calc
      (7 : K) * (1 - 7) = 4 ^ 2 - 2 * 29 := by ring1
      _ = 4 ^ 2 := by rw [twentyNineZero]; ring1
  · calc
      (25 : K) * (1 - 25) = 3 ^ 2 - 21 * 29 := by ring1
      _ = 3 ^ 2 := by rw [twentyNineZero]; ring1

private def printedLine (slope : K) : Line K where
  a := slope
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

omit [Nontrivial K] in
/-- Transfer non-nullness across one quotient-free line equivalence without
choosing a projective representative. -/
private theorem printedLine_nonNull_of_equivalent
    (actual printed : Line K) (equivalent : actual.Equivalent printed)
    (actualNonNull : ¬ actual.IsNull) : ¬ printed.IsNull := by
  rcases line_coefficient_scale_of_equivalent actual printed equivalent with
    ⟨scale, printedA, printedB, _printedC⟩
  intro printedNull
  have scaledNormZero :
      scale ^ 2 * (actual.a ^ 2 + actual.b ^ 2) = 0 := by
    calc
      scale ^ 2 * (actual.a ^ 2 + actual.b ^ 2) =
          printed.a ^ 2 + printed.b ^ 2 := by
        rw [printedA, printedB]
        ring1
      _ = 0 := printedNull
  have actualNormNonzero : actual.a ^ 2 + actual.b ^ 2 ≠ 0 :=
    actualNonNull
  have scaleSquareZero : scale ^ 2 = 0 := by
    by_cases scaleSquareZero : scale ^ 2 = 0
    · exact scaleSquareZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero scaleSquareZero actualNormNonzero)
          scaledNormZero)
  have scaleZero := square_eq_zero scaleSquareZero
  have printedAZero : printed.a = 0 := by
    rw [printedA, scaleZero]
    ring1
  have printedBZero : printed.b = 0 := by
    rw [printedB, scaleZero]
    ring1
  exact printed.direction_nonzero.elim
    (fun nonzero => nonzero printedAZero)
    (fun nonzero => nonzero printedBZero)

/-- One literal slope calculation certifies a reflection step between the
printed origin lines. -/
private theorem reflect_printedLine
    (mirrorSlope targetSlope resultSlope : K)
    (mirrorNonNull : ¬ (printedLine mirrorSlope).IsNull)
    (slopeEquation :
      (mirrorSlope ^ 2 - 1) * targetSlope + 2 * mirrorSlope =
        resultSlope *
          (2 * mirrorSlope * targetSlope - (mirrorSlope ^ 2 - 1))) :
    (reflectLine (printedLine mirrorSlope) (printedLine targetSlope)
      mirrorNonNull).Equivalent (printedLine resultSlope) := by
  unfold Line.Equivalent reflectLine printedLine reflectedLineA
    reflectedLineB reflectedLineC lineNorm
  constructor
  · simpa only [one_pow, mul_one, one_mul, mul_zero, add_zero, sub_zero]
      using slopeEquation
  · constructor <;> ring1

omit [Nontrivial K] in
/-- Propagate two finite line equivalences through one executable reflection
step. -/
private theorem next_equivalent
    (initial : ReflectionPair K) (index : Nat)
    (previous current next : Line K)
    (previousEquivalent :
      (reflectionLineAt initial index).Equivalent previous)
    (currentEquivalent :
      (reflectionLineAt initial (index + 1)).Equivalent current)
    (currentNonNull : ¬ current.IsNull)
    (printedStep : (reflectLine current previous currentNonNull).Equivalent next) :
    (reflectionLineAt initial (index + 2)).Equivalent next := by
  rw [reflectionLineAt_succ_succ]
  exact line_equivalent_trans
    (reflectLine_equivalent_of_equivalent
      (reflectionLineAt initial (index + 1)) current
      (reflectionLineAt initial index) previous
      (reflectionLineAt_nonNull initial (index + 1)) currentNonNull
      currentEquivalent previousEquivalent)
    printedStep

/-- The seven lines of the constructed star normalize to the literal source
slopes `0,15,11,20,9,18,14`. -/
theorem lines (twentyNineZero : (29 : K) = 0) :
    (reflectionLineAt (star twentyNineZero).initial 0).Equivalent
        (printedLine 0) ∧
      (reflectionLineAt (star twentyNineZero).initial 1).Equivalent
        (printedLine 15) ∧
      (reflectionLineAt (star twentyNineZero).initial 2).Equivalent
        (printedLine 11) ∧
      (reflectionLineAt (star twentyNineZero).initial 3).Equivalent
        (printedLine 20) ∧
      (reflectionLineAt (star twentyNineZero).initial 4).Equivalent
        (printedLine 9) ∧
      (reflectionLineAt (star twentyNineZero).initial 5).Equivalent
        (printedLine 18) ∧
      (reflectionLineAt (star twentyNineZero).initial 6).Equivalent
        (printedLine 14) := by
  let initial := (star twentyNineZero).initial
  have initialEq :
      initial = orderSevenInitialPair 6 12 (sixNonzero twentyNineZero)
        (twelveSpreadSquare twentyNineZero) := by
    unfold initial
    exact star_initial twentyNineZero
  have lineZero :
      (reflectionLineAt initial 0).Equivalent (printedLine 0) := by
    rw [initialEq]
    change (orderSevenLine₀ (K := K)).Equivalent (printedLine 0)
    unfold Line.Equivalent orderSevenLine₀ printedLine
    exact ⟨by ring1, by ring1, by ring1⟩
  have lineOne :
      (reflectionLineAt initial 1).Equivalent (printedLine 15) := by
    rw [initialEq]
    change (orderSevenLine₁ (K := K) 6 12
      (sixNonzero twentyNineZero)).Equivalent (printedLine 15)
    unfold Line.Equivalent orderSevenLine₁ printedLine
    constructor
    · calc
        (6 : K) * 1 = 15 * 12 - 6 * 29 := by ring1
        _ = 15 * 12 := by rw [twentyNineZero]; ring1
    · constructor <;> ring1
  have printedFifteenNonNull : ¬ (printedLine (15 : K)).IsNull :=
    printedLine_nonNull_of_equivalent
      (reflectionLineAt initial 1) (printedLine 15) lineOne
      (reflectionLineAt_nonNull initial 1)
  have stepEleven :
      (reflectLine (printedLine (15 : K)) (printedLine 0)
        printedFifteenNonNull).Equivalent (printedLine 11) := by
    apply reflect_printedLine
    calc
      ((15 : K) ^ 2 - 1) * 0 + 2 * 15 =
          11 * (2 * 15 * 0 - ((15 : K) ^ 2 - 1)) + 86 * 29 := by ring1
      _ = 11 * (2 * 15 * 0 - ((15 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineTwo :
      (reflectionLineAt initial 2).Equivalent (printedLine 11) :=
    next_equivalent initial 0 (printedLine 0) (printedLine 15)
      (printedLine 11) lineZero lineOne printedFifteenNonNull stepEleven
  have printedElevenNonNull : ¬ (printedLine (11 : K)).IsNull :=
    printedLine_nonNull_of_equivalent
      (reflectionLineAt initial 2) (printedLine 11) lineTwo
      (reflectionLineAt_nonNull initial 2)
  have stepTwenty :
      (reflectLine (printedLine (11 : K)) (printedLine 15)
        printedElevenNonNull).Equivalent (printedLine 20) := by
    apply reflect_printedLine
    calc
      ((11 : K) ^ 2 - 1) * 15 + 2 * 11 =
          20 * (2 * 11 * 15 - ((11 : K) ^ 2 - 1)) - 82 * 29 := by ring1
      _ = 20 * (2 * 11 * 15 - ((11 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineThree :
      (reflectionLineAt initial 3).Equivalent (printedLine 20) :=
    next_equivalent initial 1 (printedLine 15) (printedLine 11)
      (printedLine 20) lineOne lineTwo printedElevenNonNull stepTwenty
  have printedTwentyNonNull : ¬ (printedLine (20 : K)).IsNull :=
    printedLine_nonNull_of_equivalent
      (reflectionLineAt initial 3) (printedLine 20) lineThree
      (reflectionLineAt_nonNull initial 3)
  have stepNine :
      (reflectLine (printedLine (20 : K)) (printedLine 11)
        printedTwentyNonNull).Equivalent (printedLine 9) := by
    apply reflect_printedLine
    calc
      ((20 : K) ^ 2 - 1) * 11 + 2 * 20 =
          9 * (2 * 20 * 11 - ((20 : K) ^ 2 - 1)) + 140 * 29 := by ring1
      _ = 9 * (2 * 20 * 11 - ((20 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineFour :
      (reflectionLineAt initial 4).Equivalent (printedLine 9) :=
    next_equivalent initial 2 (printedLine 11) (printedLine 20)
      (printedLine 9) lineTwo lineThree printedTwentyNonNull stepNine
  have printedNineNonNull : ¬ (printedLine (9 : K)).IsNull :=
    printedLine_nonNull_of_equivalent
      (reflectionLineAt initial 4) (printedLine 9) lineFour
      (reflectionLineAt_nonNull initial 4)
  have stepEighteen :
      (reflectLine (printedLine (9 : K)) (printedLine 20)
        printedNineNonNull).Equivalent (printedLine 18) := by
    apply reflect_printedLine
    calc
      ((9 : K) ^ 2 - 1) * 20 + 2 * 9 =
          18 * (2 * 9 * 20 - ((9 : K) ^ 2 - 1)) - 118 * 29 := by ring1
      _ = 18 * (2 * 9 * 20 - ((9 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineFive :
      (reflectionLineAt initial 5).Equivalent (printedLine 18) :=
    next_equivalent initial 3 (printedLine 20) (printedLine 9)
      (printedLine 18) lineThree lineFour printedNineNonNull stepEighteen
  have printedEighteenNonNull : ¬ (printedLine (18 : K)).IsNull :=
    printedLine_nonNull_of_equivalent
      (reflectionLineAt initial 5) (printedLine 18) lineFive
      (reflectionLineAt_nonNull initial 5)
  have stepFourteen :
      (reflectLine (printedLine (18 : K)) (printedLine 9)
        printedEighteenNonNull).Equivalent (printedLine 14) := by
    apply reflect_printedLine
    calc
      ((18 : K) ^ 2 - 1) * 9 + 2 * 18 =
          14 * (2 * 18 * 9 - ((18 : K) ^ 2 - 1)) + 101 * 29 := by ring1
      _ = 14 * (2 * 18 * 9 - ((18 : K) ^ 2 - 1)) := by
        rw [twentyNineZero]
        ring1
  have lineSix :
      (reflectionLineAt initial 6).Equivalent (printedLine 14) :=
    next_equivalent initial 4 (printedLine 9) (printedLine 18)
      (printedLine 14) lineFour lineFive printedEighteenNonNull stepFourteen
  exact ⟨lineZero, lineOne, lineTwo, lineThree, lineFour, lineFive, lineSix⟩

end ExampleFourteenNine

end ChapterFourteenExamples

end DivineProportions
