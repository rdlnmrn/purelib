import DivineProportions.Trigonometry.CrossPolynomial
import DivineProportions.Trigonometry.SpreadCoefficient

/-!
# Divine Proportions, Chapter 8: scaled cross coefficients

Exercise 8.20 asks how the coefficients of `Cₙ*(r)=4Cₙ(r/4)` are read
from the spread array.  Odd rows are copied with alternating signs.  Even rows
are subtracted from the constant `4`.  The scaling calculation is first proved
without division for an arbitrary commutative ring.
-/

namespace DivineProportions

/-- The alternating polynomial read directly from row `row` of the spread
array. -/
def scaledSpreadCoefficientExpansion
    {R : Type*} [CommRing R] (row : Nat) (value : R) : R :=
  RFAP.finitePrefixSum row (fun index =>
    (spreadArrayCoefficient row (index + 1) : R) *
      (-1) ^ index * value ^ (index + 1))

/-- Division-free scaling law for the spread-array coefficients. -/
theorem scaledSpreadCoefficientExpansion_cleared
    {R : Type*} [CommRing R] (row : Nat) (quarter : R) :
    4 * spreadPolynomial row quarter =
      scaledSpreadCoefficientExpansion row (4 * quarter) := by
  rw [exercise_8_9_integer_coefficients]
  unfold spreadCoefficientExpansion scaledSpreadCoefficientExpansion
  rw [← RFAP.finitePrefixSum_mul_left]
  apply RFAP.finitePrefixSum_congr
  intro index indexBound
  rw [show -4 * quarter = (-1) * (4 * quarter) by ring1,
    mul_pow, pow_succ]
  ring1

/-- The source's scaled spread polynomial, under the one denominator premise
used by its notation. -/
theorem scaledSpreadCoefficientExpansion_source
    {K : Type*} [RFAP.ExplicitField K]
    (row : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * spreadPolynomial row (value / 4) =
      scaledSpreadCoefficientExpansion row value := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (RFAP.ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change 4 * spreadPolynomial row quarter =
    scaledSpreadCoefficientExpansion row value
  rw [recoverValue]
  exact scaledSpreadCoefficientExpansion_cleared row quarter

/-- Exercise 8.20 for an even row: prepend the constant `4`, then subtract
the alternating coefficients read from that spread-array row. -/
theorem exercise_8_20_even
    {K : Type*} [RFAP.ExplicitField K]
    (half : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * crossPolynomial (half + half) (value / 4) =
      4 - scaledSpreadCoefficientExpansion (half + half) value := by
  rw [(crossPolynomial_even_and_odd half (value / 4)).1]
  calc
    4 * (1 - spreadPolynomial (half + half) (value / 4)) =
        4 - 4 * spreadPolynomial (half + half) (value / 4) := by ring1
    _ = 4 - scaledSpreadCoefficientExpansion (half + half) value := by
      rw [scaledSpreadCoefficientExpansion_source
        (half + half) value fourNonzero]

/-- Exercise 8.20 for an odd row: copy the spread-array row with alternating
signs, beginning with a positive linear coefficient. -/
theorem exercise_8_20_odd
    {K : Type*} [RFAP.ExplicitField K]
    (half : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * crossPolynomial (half + half + 1) (value / 4) =
      scaledSpreadCoefficientExpansion (half + half + 1) value := by
  rw [(crossPolynomial_even_and_odd half (value / 4)).2]
  exact scaledSpreadCoefficientExpansion_source
    (half + half + 1) value fourNonzero

/-- The first four scaled cross polynomials illustrate the two rules exactly:
`r`, `4-4r+r²`, `9r-6r²+r³`, and
`4-16r+20r²-8r³+r⁴`. -/
theorem scaledCrossPolynomial_first_four
    {K : Type*} [RFAP.ExplicitField K]
    (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * crossPolynomial 1 (value / 4) = value ∧
      4 * crossPolynomial 2 (value / 4) =
        4 - 4 * value + value ^ 2 ∧
      4 * crossPolynomial 3 (value / 4) =
        9 * value - 6 * value ^ 2 + value ^ 3 ∧
      4 * crossPolynomial 4 (value / 4) =
        4 - 16 * value + 20 * value ^ 2 - 8 * value ^ 3 + value ^ 4 := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (RFAP.ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change
    4 * crossPolynomial 1 quarter = value ∧
      4 * crossPolynomial 2 quarter =
        4 - 4 * value + value ^ 2 ∧
      4 * crossPolynomial 3 quarter =
        9 * value - 6 * value ^ 2 + value ^ 3 ∧
      4 * crossPolynomial 4 quarter =
        4 - 16 * value + 20 * value ^ 2 - 8 * value ^ 3 + value ^ 4
  rw [recoverValue]
  constructor
  · simp only [crossPolynomial]
  constructor
  · simp only [crossPolynomial]
    ring1
  constructor
  · simp only [crossPolynomial]
    ring1
  · simp only [crossPolynomial]
    ring1

end DivineProportions
