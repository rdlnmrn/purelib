import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadChebyshev
import mathlib.RFAP.FiniteTotient
import mathlib.RFAP.IntegerPolynomialCertificate

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `mathlib.RFAP.FiniteTotient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace ExerciseEightThirteen

/-- Lucas polynomial evaluation by its two-step integer recurrence. -/
def finiteLucas : Nat → K → K
  | 0, _ => 2
  | 1, value => value
  | index + 2, value =>
      value * finiteLucas (index + 1) value - finiteLucas index value

@[simp] theorem finiteLucas_zero (value : K) :
    finiteLucas 0 value = 2 := rfl

@[simp] theorem finiteLucas_one (value : K) :
    finiteLucas 1 value = value := rfl

@[simp] theorem finiteLucas_succ_succ (index : Nat) (value : K) :
    finiteLucas (index + 2) value =
      value * finiteLucas (index + 1) value - finiteLucas index value := rfl

namespace IntegerPolynomial

open RFAP.IntegerPolynomialCertificate

/-- Integer coefficient lists for the Lucas recurrence, in ascending degree
order.  This is the coefficient-level object needed for a constructive
cyclotomic factor algorithm. -/
def finiteLucasCoefficients : Nat → List Int
  | 0 => [2]
  | 1 => [0, 1]
  | index + 2 =>
      sub (shift (finiteLucasCoefficients (index + 1)))
        (finiteLucasCoefficients index)

@[simp] theorem finiteLucasCoefficients_zero :
    finiteLucasCoefficients 0 = [2] := rfl

@[simp] theorem finiteLucasCoefficients_one :
    finiteLucasCoefficients 1 = [0, 1] := rfl

@[simp] theorem finiteLucasCoefficients_succ_succ (index : Nat) :
    finiteLucasCoefficients (index + 2) =
      sub (shift (finiteLucasCoefficients (index + 1)))
        (finiteLucasCoefficients index) := rfl

/-- The coefficient recurrence evaluates to the Lucas recurrence in every
constructive explicit field. -/
theorem eval_finiteLucasCoefficients : ∀ index : Nat, ∀ value : K,
    eval (finiteLucasCoefficients index) value = finiteLucas index value
  | 0, value => by
      simp only [finiteLucasCoefficients_zero, eval_cons, eval_nil,
        Int.cast_ofNat, mul_zero, add_zero, finiteLucas_zero]
  | 1, value => by
      simp only [finiteLucasCoefficients_one, eval_cons, eval_nil,
        Int.cast_zero, Int.cast_one, mul_zero, add_zero, zero_add, mul_one,
        finiteLucas_one]
  | index + 2, value => by
      rw [finiteLucasCoefficients_succ_succ, eval_sub, eval_shift,
        eval_finiteLucasCoefficients (index + 1) value,
        eval_finiteLucasCoefficients index value,
        finiteLucas_succ_succ]

/-- The coefficient list has the exact expected slot count. -/
theorem finiteLucasCoefficients_length : ∀ index : Nat,
    (finiteLucasCoefficients index).length = index + 1
  | 0 => rfl
  | 1 => rfl
  | index + 2 => by
      rw [finiteLucasCoefficients_succ_succ, length_sub]
      simp only [shift, List.length_cons,
        finiteLucasCoefficients_length (index + 1),
        finiteLucasCoefficients_length index]
      omega0

/-- Every positive-index Lucas coefficient list is monic.  Together with the
slot-count theorem, this gives exact degree `n` without appealing to a
completed polynomial type. -/
theorem finiteLucasCoefficients_monic : ∀ index : Nat,
    (finiteLucasCoefficients (index + 1)).getLast? = some 1
  | 0 => rfl
  | index + 1 => by
      rw [show index + 1 + 1 = index + 2 by omega0,
        finiteLucasCoefficients_succ_succ]
      have shorter :
          (finiteLucasCoefficients index).length <
            (shift (finiteLucasCoefficients (index + 1))).length := by
        rw [finiteLucasCoefficients_length,
          show (shift (finiteLucasCoefficients (index + 1))).length =
              (finiteLucasCoefficients (index + 1)).length + 1 by rfl,
          finiteLucasCoefficients_length]
        omega0
      rw [getLast?_sub_of_length_lt _ _ shorter,
        getLast?_shift_of_ne_nil]
      · exact finiteLucasCoefficients_monic index
      · intro empty
        have lengthEquation := finiteLucasCoefficients_length (index + 1)
        rw [empty] at lengthEquation
        simp only [List.length_nil] at lengthEquation
        omega0

/-- The affine substitution from a real-cyclotomic trace variable to the
spread variable. -/
def centeredSpreadSubstitution : List Int := [2, -4]

theorem eval_centeredSpreadSubstitution (value : K) :
    eval centeredSpreadSubstitution value = 2 - 4 * value := by
  unfold centeredSpreadSubstitution
  simp only [eval_cons, eval_nil, Int.cast_ofNat, Int.cast_neg, mul_zero,
    add_zero]
  ring1

/-- Substitute `2-4s` into an integer real-cyclotomic factor. -/
def spreadRealFactorCoefficients (coefficients : List Int) : List Int :=
  compose coefficients centeredSpreadSubstitution

theorem eval_spreadRealFactorCoefficients
    (coefficients : List Int) (value : K) :
    eval (spreadRealFactorCoefficients coefficients) value =
      eval coefficients (2 - 4 * value) := by
  rw [spreadRealFactorCoefficients, eval_compose,
    eval_centeredSpreadSubstitution]

/-- Every non-endpoint spread-cyclotomic factor is the square of the
corresponding real-cyclotomic factor after the affine substitution. -/
def spreadCyclotomicCoefficients (coefficients : List Int) : List Int :=
  power (spreadRealFactorCoefficients coefficients) 2

theorem eval_spreadCyclotomicCoefficients
    (coefficients : List Int) (value : K) :
    eval (spreadCyclotomicCoefficients coefficients) value =
      eval coefficients (2 - 4 * value) ^ 2 := by
  rw [spreadCyclotomicCoefficients, eval_power,
    eval_spreadRealFactorCoefficients]

end IntegerPolynomial

/-- On a doubled argument, the Lucas recurrence is exactly twice the
first-kind Chebyshev recurrence. -/
theorem finiteLucas_at_double : ∀ index : Nat, ∀ value : K,
    finiteLucas index (2 * value) = 2 * chebyshevFirst index value
  | 0, value => by
      rw [finiteLucas_zero, chebyshevFirst_zero]
      ring1
  | 1, value => by
      rw [finiteLucas_one, chebyshevFirst_one]
  | index + 2, value => by
      rw [finiteLucas_succ_succ, chebyshevFirst_succ_succ,
        finiteLucas_at_double (index + 1) value,
        finiteLucas_at_double index value]
      ring1

/-- The source's spread/Lucas formula in denominator-free form. -/
theorem spread_lucas_cleared (index : Nat) (value : K) :
    4 * spreadPolynomial index value =
      2 - finiteLucas index (2 - 4 * value) := by
  have centered := exercise_8_4_cleared index value
  rw [show 2 - 4 * value = 2 * (1 - 2 * value) by ring1,
    finiteLucas_at_double]
  calc
    4 * spreadPolynomial index value =
        2 * (2 * spreadPolynomial index value) := by ring1
    _ = 2 * (1 - chebyshevFirst index (1 - 2 * value)) := by
      rw [centered]
    _ = 2 - 2 * chebyshevFirst index (1 - 2 * value) := by ring1

/-- Lucas product-to-sum on the doubled arguments needed by the spread
substitution. -/
theorem finiteLucas_product_add_sub_doubled
    (offset step : Nat) (value : K) :
    finiteLucas (offset + step) (2 * value) *
        finiteLucas step (2 * value) =
      finiteLucas (offset + step + step) (2 * value) +
        finiteLucas offset (2 * value) := by
  have product := chebyshevFirst_product_add_sub
    (K := K) offset step value
  rw [finiteLucas_at_double, finiteLucas_at_double,
    finiteLucas_at_double, finiteLucas_at_double]
  calc
    (2 * chebyshevFirst (offset + step) value) *
        (2 * chebyshevFirst step value) =
      2 * (2 * chebyshevFirst (offset + step) value *
        chebyshevFirst step value) := by ring1
    _ = 2 * (chebyshevFirst (offset + step + step) value +
        chebyshevFirst offset value) := by rw [product]
    _ = 2 * chebyshevFirst (offset + step + step) value +
        2 * chebyshevFirst offset value := by ring1

/-- Odd Lucas indices have one simple endpoint factor and a square remaining
factor.  This is equation (13) in the finite algebraic reduction of the
Goh--Wildberger conjecture. -/
theorem finiteLucas_odd_square_identity
    (half : Nat) (value : K) :
    (finiteLucas (half + half + 1) (2 * value) - 2) *
        (2 * value - 2) =
      (finiteLucas (half + 1) (2 * value) -
        finiteLucas half (2 * value)) ^ 2 := by
  have upperSquare := finiteLucas_product_add_sub_doubled
    (K := K) 0 (half + 1) value
  have lowerSquare := finiteLucas_product_add_sub_doubled
    (K := K) 0 half value
  have adjacentProduct := finiteLucas_product_add_sub_doubled
    (K := K) 1 half value
  have neighborSum := finiteLucas_product_add_sub_doubled
    (K := K) (half + half) 1 value
  rw [show 0 + (half + 1) = half + 1 by omega0] at upperSquare
  rw [show half + 1 + (half + 1) = half + half + 2 by omega0,
    finiteLucas_zero] at upperSquare
  rw [show 0 + half = half by omega0, finiteLucas_zero] at lowerSquare
  rw [show 1 + half = half + 1 by omega0] at adjacentProduct
  rw [show half + 1 + half = half + half + 1 by omega0,
    finiteLucas_one] at adjacentProduct
  rw [show half + half + 1 + 1 = half + half + 2 by omega0,
    finiteLucas_one] at neighborSum
  calc
    (finiteLucas (half + half + 1) (2 * value) - 2) *
        (2 * value - 2) =
      finiteLucas (half + half + 1) (2 * value) *
          (2 * value) -
        2 * finiteLucas (half + half + 1) (2 * value) -
          4 * value + 4 := by ring1
    _ = finiteLucas (half + half + 2) (2 * value) +
          finiteLucas (half + half) (2 * value) -
        2 * finiteLucas (half + half + 1) (2 * value) -
          4 * value + 4 := by rw [neighborSum]
    _ = (finiteLucas (half + 1) (2 * value) -
        finiteLucas half (2 * value)) ^ 2 := by
          calc
            finiteLucas (half + half + 2) (2 * value) +
                  finiteLucas (half + half) (2 * value) -
                2 * finiteLucas (half + half + 1) (2 * value) -
                  4 * value + 4 =
              finiteLucas (half + 1) (2 * value) *
                  finiteLucas (half + 1) (2 * value) +
                finiteLucas half (2 * value) *
                  finiteLucas half (2 * value) -
                2 * (finiteLucas (half + 1) (2 * value) *
                  finiteLucas half (2 * value)) := by
                    rw [upperSquare, lowerSquare, adjacentProduct]
                    ring1
            _ = (finiteLucas (half + 1) (2 * value) -
                finiteLucas half (2 * value)) ^ 2 := by
                  rw [pow_two]
                  ring1

/-- Even Lucas indices have the two simple endpoint factors and a square
remaining factor.  This is equation (14) in the same finite reduction. -/
theorem finiteLucas_even_square_identity
    (half : Nat) (halfPositive : 1 ≤ half) (value : K) :
    (finiteLucas (half + half) (2 * value) - 2) *
        ((2 * value - 2) * (2 * value + 2)) =
      (finiteLucas (half + 1) (2 * value) -
        finiteLucas (half - 1) (2 * value)) ^ 2 := by
  have upperSquare := finiteLucas_product_add_sub_doubled
    (K := K) 0 (half + 1) value
  have lowerSquare := finiteLucas_product_add_sub_doubled
    (K := K) 0 (half - 1) value
  have separatedProduct := finiteLucas_product_add_sub_doubled
    (K := K) 2 (half - 1) value
  have twoTimesMiddle := finiteLucas_product_add_sub_doubled
    (K := K) (half + half - 2) 2 value
  have lucasTwo : finiteLucas 2 (2 * value) = 4 * value ^ 2 - 2 := by
    rw [finiteLucas_succ_succ, finiteLucas_one, finiteLucas_zero]
    ring1
  rw [show 0 + (half + 1) = half + 1 by omega0] at upperSquare
  rw [show half + 1 + (half + 1) = half + half + 2 by omega0,
    finiteLucas_zero] at upperSquare
  rw [show 0 + (half - 1) = half - 1 by omega0] at lowerSquare
  rw [show half - 1 + (half - 1) = half + half - 2 by omega0,
    finiteLucas_zero] at lowerSquare
  rw [show 2 + (half - 1) = half + 1 by omega0] at separatedProduct
  rw [show half + 1 + (half - 1) = half + half by omega0]
    at separatedProduct
  rw [show half + half - 2 + 2 = half + half by omega0]
    at twoTimesMiddle
  calc
    (finiteLucas (half + half) (2 * value) - 2) *
        ((2 * value - 2) * (2 * value + 2)) =
      (finiteLucas (half + half) (2 * value) - 2) *
        (4 * value ^ 2 - 4) := by ring1
    _ = (finiteLucas (half + half) (2 * value) - 2) *
        (finiteLucas 2 (2 * value) - 2) := by
          rw [lucasTwo]
          ring1
    _ = finiteLucas (half + half + 2) (2 * value) +
          finiteLucas (half + half - 2) (2 * value) -
        2 * finiteLucas (half + half) (2 * value) -
          2 * finiteLucas 2 (2 * value) + 4 := by
            rw [mul_sub, sub_mul, twoTimesMiddle]
            ring1
    _ = (finiteLucas (half + 1) (2 * value) -
        finiteLucas (half - 1) (2 * value)) ^ 2 := by
          calc
            finiteLucas (half + half + 2) (2 * value) +
                  finiteLucas (half + half - 2) (2 * value) -
                2 * finiteLucas (half + half) (2 * value) -
                  2 * finiteLucas 2 (2 * value) + 4 =
              finiteLucas (half + 1) (2 * value) *
                  finiteLucas (half + 1) (2 * value) +
                finiteLucas (half - 1) (2 * value) *
                  finiteLucas (half - 1) (2 * value) -
                2 * (finiteLucas (half + 1) (2 * value) *
                  finiteLucas (half - 1) (2 * value)) := by
                    rw [upperSquare, lowerSquare, separatedProduct]
                    ring1
            _ = (finiteLucas (half + 1) (2 * value) -
                finiteLucas (half - 1) (2 * value)) ^ 2 := by
                  rw [pow_two]
                  ring1

/-- Odd spread polynomials inherit the Lucas square factorization, with all
factors cleared in the coefficient field. -/
theorem spread_odd_lucas_square_cleared
    (half : Nat) (value : K) :
    16 * value * spreadPolynomial (half + half + 1) value =
      (finiteLucas (half + 1) (2 - 4 * value) -
        finiteLucas half (2 - 4 * value)) ^ 2 := by
  have lucasSquare := finiteLucas_odd_square_identity
    (K := K) half (1 - 2 * value)
  rw [show 2 * (1 - 2 * value) = 2 - 4 * value by ring1]
    at lucasSquare
  have spreadIdentity := spread_lucas_cleared
    (K := K) (half + half + 1) value
  have lucasDifference :
      finiteLucas (half + half + 1) (2 - 4 * value) - 2 =
        -4 * spreadPolynomial (half + half + 1) value := by
    calc
      finiteLucas (half + half + 1) (2 - 4 * value) - 2 =
          -(2 - finiteLucas (half + half + 1) (2 - 4 * value)) := by
            ring1
      _ = -(4 * spreadPolynomial (half + half + 1) value) := by
        rw [← spreadIdentity]
      _ = -4 * spreadPolynomial (half + half + 1) value := by ring1
  calc
    16 * value * spreadPolynomial (half + half + 1) value =
      (finiteLucas (half + half + 1) (2 - 4 * value) - 2) *
        ((2 - 4 * value) - 2) := by
          rw [lucasDifference]
          ring1
    _ = (finiteLucas (half + 1) (2 - 4 * value) -
        finiteLucas half (2 - 4 * value)) ^ 2 := lucasSquare

/-- Even spread polynomials likewise carry the two simple endpoint factors
and a square remainder, again without division. -/
theorem spread_even_lucas_square_cleared
    (half : Nat) (halfPositive : 1 ≤ half) (value : K) :
    64 * value * (1 - value) *
        spreadPolynomial (half + half) value =
      (finiteLucas (half + 1) (2 - 4 * value) -
        finiteLucas (half - 1) (2 - 4 * value)) ^ 2 := by
  have lucasSquare := finiteLucas_even_square_identity
    (K := K) half halfPositive (1 - 2 * value)
  rw [show 2 * (1 - 2 * value) = 2 - 4 * value by ring1]
    at lucasSquare
  have spreadIdentity := spread_lucas_cleared
    (K := K) (half + half) value
  have lucasDifference :
      finiteLucas (half + half) (2 - 4 * value) - 2 =
        -4 * spreadPolynomial (half + half) value := by
    calc
      finiteLucas (half + half) (2 - 4 * value) - 2 =
          -(2 - finiteLucas (half + half) (2 - 4 * value)) := by ring1
      _ = -(4 * spreadPolynomial (half + half) value) := by
        rw [← spreadIdentity]
      _ = -4 * spreadPolynomial (half + half) value := by ring1
  calc
    64 * value * (1 - value) *
        spreadPolynomial (half + half) value =
      (finiteLucas (half + half) (2 - 4 * value) - 2) *
        (((2 - 4 * value) - 2) * ((2 - 4 * value) + 2)) := by
          rw [lucasDifference]
          ring1
    _ = (finiteLucas (half + 1) (2 - 4 * value) -
        finiteLucas (half - 1) (2 - 4 * value)) ^ 2 := lucasSquare

end ExerciseEightThirteen

end DivineProportions
