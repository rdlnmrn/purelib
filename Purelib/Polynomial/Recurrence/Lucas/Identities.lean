module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Lucas.Basic
import Purelib.Polynomial.Recurrence.Lucas.Chebyshev

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `Purelib.NumberTheory.Totient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace Purelib.Polynomial.Recurrence.Lucas.Identities.ExerciseEightThirteen

variable {K : Type*} [ExplicitField K]

section

/-- Lucas product-to-sum on the doubled arguments needed by the spread
substitution. -/
theorem lucas_product_add_sub_doubled
    (offset step : Nat) (value : K) :
    Recurrence.Lucas.Basic.lucas (offset + step) (2 * value) *
        Recurrence.Lucas.Basic.lucas step (2 * value) =
      Recurrence.Lucas.Basic.lucas (offset + step + step) (2 * value) +
        Recurrence.Lucas.Basic.lucas offset (2 * value) := by
  have product := Recurrence.Chebyshev.First.Basic.chebyshevFirst_product_add_sub
    (K := K) offset step value
  rw [Recurrence.Lucas.Chebyshev.ExerciseEightThirteen.lucas_at_double,
    Recurrence.Lucas.Chebyshev.ExerciseEightThirteen.lucas_at_double,
    Recurrence.Lucas.Chebyshev.ExerciseEightThirteen.lucas_at_double,
      Recurrence.Lucas.Chebyshev.ExerciseEightThirteen.lucas_at_double]
  calc
    (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (offset + step) value) *
        (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst step value) =
      2 * (2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (offset + step) value *
        Recurrence.Chebyshev.First.Basic.chebyshevFirst step value) := by ring1
    _ = 2 * (Recurrence.Chebyshev.First.Basic.chebyshevFirst (offset + step + step) value +
        Recurrence.Chebyshev.First.Basic.chebyshevFirst offset value) := by rw [product]
    _ = 2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst (offset + step + step) value +
        2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst offset value := by ring1

/-- Odd Lucas indices have one simple endpoint factor and a square remaining
factor.  This is equation (13) in the finite algebraic reduction of the
Goh--Wildberger conjecture. -/
theorem lucas_odd_square_identity
    (half : Nat) (value : K) :
    (Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) - 2) *
        (2 * value - 2) =
      (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
        Recurrence.Lucas.Basic.lucas half (2 * value)) ^ 2 := by
  have upperSquare := lucas_product_add_sub_doubled
    (K := K) 0 (half + 1) value
  have lowerSquare := lucas_product_add_sub_doubled
    (K := K) 0 half value
  have adjacentProduct := lucas_product_add_sub_doubled
    (K := K) 1 half value
  have neighborSum := lucas_product_add_sub_doubled
    (K := K) (half + half) 1 value
  rw [show 0 + (half + 1) = half + 1 by omega0] at upperSquare
  rw [show half + 1 + (half + 1) = half + half + 2 by omega0,
    Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero] at upperSquare
  rw [show 0 + half = half by omega0, Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero] at lowerSquare
  rw [show 1 + half = half + 1 by omega0] at adjacentProduct
  rw [show half + 1 + half = half + half + 1 by omega0,
    Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_one] at adjacentProduct
  rw [show half + half + 1 + 1 = half + half + 2 by omega0,
    Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_one] at neighborSum
  calc
    (Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) - 2) *
        (2 * value - 2) =
      Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) *
          (2 * value) -
        2 * Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) -
          4 * value + 4 := by ring1
    _ = Recurrence.Lucas.Basic.lucas (half + half + 2) (2 * value) +
          Recurrence.Lucas.Basic.lucas (half + half) (2 * value) -
        2 * Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) -
          4 * value + 4 := by rw [neighborSum]
    _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
        Recurrence.Lucas.Basic.lucas half (2 * value)) ^ 2 := by
          calc
            Recurrence.Lucas.Basic.lucas (half + half + 2) (2 * value) +
                  Recurrence.Lucas.Basic.lucas (half + half) (2 * value) -
                2 * Recurrence.Lucas.Basic.lucas (half + half + 1) (2 * value) -
                  4 * value + 4 =
              Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) *
                  Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) +
                Recurrence.Lucas.Basic.lucas half (2 * value) *
                  Recurrence.Lucas.Basic.lucas half (2 * value) -
                2 * (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) *
                  Recurrence.Lucas.Basic.lucas half (2 * value)) := by
                    rw [upperSquare, lowerSquare, adjacentProduct]
                    ring1
            _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
                Recurrence.Lucas.Basic.lucas half (2 * value)) ^ 2 := by
                  rw [pow_two]
                  ring1

/-- Even Lucas indices have the two simple endpoint factors and a square
remaining factor.  This is equation (14) in the same finite reduction. -/
theorem lucas_even_square_identity
    (half : Nat) (halfPositive : 1 ≤ half) (value : K) :
    (Recurrence.Lucas.Basic.lucas (half + half) (2 * value) - 2) *
        ((2 * value - 2) * (2 * value + 2)) =
      (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
        Recurrence.Lucas.Basic.lucas (half - 1) (2 * value)) ^ 2 := by
  have upperSquare := lucas_product_add_sub_doubled
    (K := K) 0 (half + 1) value
  have lowerSquare := lucas_product_add_sub_doubled
    (K := K) 0 (half - 1) value
  have separatedProduct := lucas_product_add_sub_doubled
    (K := K) 2 (half - 1) value
  have twoTimesMiddle := lucas_product_add_sub_doubled
    (K := K) (half + half - 2) 2 value
  have lucasTwo : Recurrence.Lucas.Basic.lucas 2 (2 * value) = 4 * value ^ 2 - 2 := by
    rw [Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_succ_succ,
      Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_one, Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero]
    ring1
  rw [show 0 + (half + 1) = half + 1 by omega0] at upperSquare
  rw [show half + 1 + (half + 1) = half + half + 2 by omega0,
    Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero] at upperSquare
  rw [show 0 + (half - 1) = half - 1 by omega0] at lowerSquare
  rw [show half - 1 + (half - 1) = half + half - 2 by omega0,
    Recurrence.Lucas.Basic.ExerciseEightThirteen.lucas_zero] at lowerSquare
  rw [show 2 + (half - 1) = half + 1 by omega0] at separatedProduct
  rw [show half + 1 + (half - 1) = half + half by omega0]
    at separatedProduct
  rw [show half + half - 2 + 2 = half + half by omega0]
    at twoTimesMiddle
  calc
    (Recurrence.Lucas.Basic.lucas (half + half) (2 * value) - 2) *
        ((2 * value - 2) * (2 * value + 2)) =
      (Recurrence.Lucas.Basic.lucas (half + half) (2 * value) - 2) *
        (4 * value ^ 2 - 4) := by ring1
    _ = (Recurrence.Lucas.Basic.lucas (half + half) (2 * value) - 2) *
        (Recurrence.Lucas.Basic.lucas 2 (2 * value) - 2) := by
          rw [lucasTwo]
          ring1
    _ = Recurrence.Lucas.Basic.lucas (half + half + 2) (2 * value) +
          Recurrence.Lucas.Basic.lucas (half + half - 2) (2 * value) -
        2 * Recurrence.Lucas.Basic.lucas (half + half) (2 * value) -
          2 * Recurrence.Lucas.Basic.lucas 2 (2 * value) + 4 := by
            rw [mul_sub, sub_mul, twoTimesMiddle]
            ring1
    _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
        Recurrence.Lucas.Basic.lucas (half - 1) (2 * value)) ^ 2 := by
          calc
            Recurrence.Lucas.Basic.lucas (half + half + 2) (2 * value) +
                  Recurrence.Lucas.Basic.lucas (half + half - 2) (2 * value) -
                2 * Recurrence.Lucas.Basic.lucas (half + half) (2 * value) -
                  2 * Recurrence.Lucas.Basic.lucas 2 (2 * value) + 4 =
              Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) *
                  Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) +
                Recurrence.Lucas.Basic.lucas (half - 1) (2 * value) *
                  Recurrence.Lucas.Basic.lucas (half - 1) (2 * value) -
                2 * (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) *
                  Recurrence.Lucas.Basic.lucas (half - 1) (2 * value)) := by
                    rw [upperSquare, lowerSquare, separatedProduct]
                    ring1
            _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 * value) -
                Recurrence.Lucas.Basic.lucas (half - 1) (2 * value)) ^ 2 := by
                  rw [pow_two]
                  ring1
end

end Purelib.Polynomial.Recurrence.Lucas.Identities.ExerciseEightThirteen

end
