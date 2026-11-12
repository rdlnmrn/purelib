module

public import Purelib.Data.Gaussian.Norm.Weight
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Gaussian readings with finite rational multiplication bounds

A reading preserves the additive operations and the displayed original
Gaussian scalar action exactly. Its retained gain and multiplication-error
constants bound the same original scalar weight without asserting an exact
multiplicative homomorphism.
-/

public section

namespace Purelib.Algebra.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {K : Type*} [CommRing K]

set_option genInjectivity false in
/-- An additive Gaussian reading with exact original scalar action and certified finite norm bounds.

The original weight and Gaussian embedding remain indices. The actual
reading, gain and multiplication error are executable retained data; a
positive error records precisely the allowed failure of multiplication.
-/
structure GaussianReading (weight : Weight K) (scalar : Canonical → K) where
  /-- The actual scalar-reading operation. -/
  read : K → Canonical
  /-- The original zero reads as zero. -/
  mapZero : read 0 = 0
  /-- The original unit reads as one. -/
  mapOne : read 1 = 1
  /-- Addition of the original payloads is preserved. -/
  mapAdd : ∀ left right, read (left + right) = read left + read right
  /-- Negation of the original payload is preserved. -/
  mapNeg : ∀ value, read (-value) = -read value
  /-- The same original embedded Gaussian acts by its actual scalar value. -/
  mapScalarMul : ∀ coefficient value, read (scalar coefficient * value) = coefficient * read value
  /-- The retained nonnegative gain for individual original scalar readings. -/
  gain : Rational
  /-- The original gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- Every original scalar reading satisfies the retained gain bound. -/
  gainBound : ∀ value, Norm.Basic.normSq (read value) ≤ gain * weight.value value
  /-- The retained nonnegative original multiplication-error constant. -/
  error : Rational
  /-- The original multiplication-error constant is nonnegative. -/
  errorNonnegative : 0 ≤ error
  /-- Every original product discrepancy satisfies the retained uniform error bound. -/
  productBound : ∀ left right, Norm.Basic.normSq (read (left * right) - read left * read right) ≤
    error * weight.value left * weight.value right

constructive_injectivity GaussianReading

namespace GaussianReading

/-- The original identity Gaussian reading has gain one and multiplication error zero. -/
@[expose] def identity : GaussianReading Norm.weight id where
  read := id
  mapZero := rfl
  mapOne := rfl
  mapAdd := fun _ _ => rfl
  mapNeg := fun _ => rfl
  mapScalarMul := fun _ _ => rfl
  gain := 1
  gainNonnegative := by decide
  gainBound value := by
    change Norm.Basic.normSq value ≤ 1 * Norm.Basic.normSq value
    rewrite [one_mul]
    exact le_rfl
  error := 0
  errorNonnegative := by decide
  productBound left right := by
    change Norm.Basic.normSq (left * right - left * right) ≤ 0 * Norm.weight.value left * Norm.weight.value right
    rewrite [sub_self, Norm.Basic.normSq_zero, zero_mul, zero_mul]
    exact le_rfl

/-- An original embedded Gaussian reads as that same Gaussian coefficient. -/
theorem read_scalar {weight : Weight K} {scalar : Canonical → K}
    (reading : GaussianReading weight scalar) (coefficient : Canonical) :
    reading.read (scalar coefficient) = coefficient := by
  have retained := reading.mapScalarMul coefficient 1
  rewrite [mul_one, reading.mapOne, mul_one] at retained
  exact retained

end GaussianReading

end Purelib.Algebra.Ring

end
