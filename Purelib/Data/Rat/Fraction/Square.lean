module
import Purelib.Data.Int.Arithmetic
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Nat.Coprime.Arithmetic

open Purelib.Data.Nat

/-!
# Squaring an already reduced finite fraction

The retained reducedness certificate proves that the squared numerator and
denominator are coprime.  Execution needs only two integer multiplications,
not the two cross-cancellation gcds used by general multiplication.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Int

/-- Square a canonical rational by directly squaring its retained numerator and denominator.

The original coprimality certificate proves the coordinate products are already reduced, including zero. No additional
gcd normalization is computed. -/
@[expose] public def square (value : Rational) : Rational where
  num := value.num * value.num
  den := value.den * value.den
  den_pos := Nat.mul_pos value.den_pos value.den_pos
  reduced := by
    rcases value.reduced with ⟨certificate⟩
    rw [Arithmetic.natAbs_mul]
    exact ⟨Coprime.Arithmetic.mul_mul
      certificate certificate certificate certificate⟩

/-- Direct coordinate squaring equals the original canonical multiplication result.

Both computations retain the same squared integer numerator and positive
natural denominator. Their displayed cross-product equation identifies the
original canonical fraction without another normalization algorithm. -/
public theorem square_eq_mul (value : Rational) : square value = value * value := by
  apply eq_of_cross
  exact (mul_equivalent value value).symm

/-- Direct squaring computes the canonical squares of zero, one, negative one and negative two thirds.

The four literal original fraction records retain their supplied reducedness
certificates. Kernel computation checks both squared coordinates and their
same canonical outputs. -/
public theorem square_regressions :
    square 0 = 0 ∧ square 1 = 1 ∧ square (-1) = 1 ∧
      square (⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) =
        (⟨4, 9, by decide, ⟨⟨-2, 1, by decide⟩⟩⟩ : Rational) := by
  decide +kernel

end Purelib.Data.Rat.Fraction
