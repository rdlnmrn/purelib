module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact integration and finite reading bounds for exponential polynomials

`polynomial n` has degree `n+1`, matching the existing finite Horner sample
at index `n`.  Its integral has the next sample index.  All statements concern
displayed coefficient lists and rational points, not a completed exponential.
-/

namespace Purelib.Data.Gaussian.RationalEmbedding.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A nonnegative rational at most one has real-axis Gaussian squared norm at most one. -/
theorem unit_parameter {parameter : Fraction.Rational}
  (nonnegative : 0 ≤ parameter)
    (bounded : parameter ≤ 1) : Basic.Canonical.normSq (⟨parameter, 0⟩ : Basic.Canonical) ≤ 1 := by
  have squareBound := Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative bounded 2
  have norm : Basic.Canonical.normSq (⟨parameter, 0⟩ : Basic.Canonical) = parameter ^ 2 := by
    unfold Basic.Canonical.normSq
    ring1
  rw [norm]
  simpa only [one_pow] using squareBound
end Purelib.Data.Gaussian.RationalEmbedding.Bounds

end
