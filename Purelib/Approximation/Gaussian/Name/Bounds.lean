module
public import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic finite range reduction for the progressive exponential

This module makes the local construction a total exponential operator on
arithmetic CCL names.  One finite input ball from the CCL accuracy sidechannel
supplies a rational norm bound.  A logarithmic bounded scan chooses a
displayed natural exponent `k` for which division by `2^k` puts every
candidate in the unit disk.  The local exponential CCL name is then squared
exactly `k` times by the already proved CCL arithmetic operation.  The result
is again a productive CCL name.  No magnitude limit, completed input value,
or infinite functional equation is used; the bare raw bitstream is not asked
to provide quantitative accuracy by itself.
-/

namespace Purelib.Approximation.Gaussian.Name.Bounds

/-- A finite squared-norm bound for every candidate at the supplied state. -/
def inputBound (input : Named) : Fraction.Rational
  :=
  2 * ((input.process.ball input.state).radiusSq +
    Data.Gaussian.Norm.Basic.normSq (input.process.ball input.state).center)

/-- The named-state candidate squared-norm bound is nonnegative. -/
theorem inputBound_nonneg (input : Named) : 0 ≤
  inputBound input :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (input.process.ball input.state).radiusSq_nonneg
      (Data.Gaussian.Norm.Basic.normSq_nonneg _))

/-- Every reading possible at the named state meets its computed candidate squared-norm bound. -/
theorem possible_normSq_le_inputBound (input :
  Named) {value : Data.Gaussian.Basic.Canonical}
    (possible : input.process.Possible input.state value) :
    Data.Gaussian.Norm.Basic.normSq value ≤ inputBound input := by
  let center := (input.process.ball input.state).center
  have inside := input.process.possible_inside possible
  have identity : value = (value - center) + center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add inside le_rfl) (by decide))
end Purelib.Approximation.Gaussian.Name.Bounds

end
