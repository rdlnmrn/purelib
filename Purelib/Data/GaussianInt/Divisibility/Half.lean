module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Division
public import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic

/-!
# Coordinate division by a quadrance-two Gaussian integer

Total halving of the retained integer coordinates recovers an explicitly
multiplied quotient after multiplication by the divisor's conjugate.
-/

public section

namespace Purelib.Data.GaussianInt.Divisibility.Half

open Purelib.Data
open Purelib.Data.GaussianInt

/-- Divide each integral coordinate by two, using total integer division.

The operation is defined for every Gaussian integer; exact recovery requires the
later hypotheses ensuring divisibility of the retained coordinates. -/
@[expose] def halfGaussianInt (value : GaussianInt) : GaussianInt :=
  ⟨value.re / 2, value.im / 2⟩

open Purelib.Data.GaussianInt.Divisibility
/-- Multiply by the displayed divisor's conjugate and halve both integral coordinates.

When the divisor has quadrance two, this total executable operation recovers an
explicitly divisible quotient. -/
@[expose] def divideByNormTwo (divisor value : GaussianInt) : GaussianInt :=
  Half.halfGaussianInt (conj divisor * value)

/-- Quadrance-two coordinate division recovers a quotient explicitly multiplied by its
divisor. -/
theorem divideByNormTwo_mul
    (divisor quotient : GaussianInt) (divisorNorm : normNat divisor = 2) :
    Half.divideByNormTwo divisor (divisor * quotient) = quotient := by
  have conjugateProduct : conj divisor * divisor = ofNat 2 := by
    rw [GaussianInt.mul_comm, mul_conj,
      divisorNorm]
  apply GaussianInt.ext
  · dsimp only [Half.divideByNormTwo, Half.halfGaussianInt]
    rw [← GaussianInt.mul_assoc,
      conjugateProduct]
    simp only [ofNat,
      GaussianInt.mul_re]
    rw [Int.Arithmetic.zero_mul, Int.Arithmetic.sub_zero]
    change ((2 : Int) * quotient.re) / 2 = quotient.re
    exact Int.Division.mul_ediv_cancel_left quotient.re (by decide)
  · dsimp only [Half.divideByNormTwo, Half.halfGaussianInt]
    rw [← GaussianInt.mul_assoc,
      conjugateProduct]
    simp only [ofNat,
      GaussianInt.mul_im]
    rw [Int.Arithmetic.zero_mul, Int.add_zero]
    change ((2 : Int) * quotient.im) / 2 = quotient.im
    exact Int.Division.mul_ediv_cancel_left quotient.im (by decide)
end Purelib.Data.GaussianInt.Divisibility.Half
