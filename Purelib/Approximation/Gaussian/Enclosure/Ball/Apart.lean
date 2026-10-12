module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball
section Ball

set_option genInjectivity false in
/-- A finite apartness sidecar for a denominator enclosure. -/
structure Apart (ball : Ball) where
  /-- The retained positive rational lower bound on candidate squared norms. -/ lowerSq : Fraction.Rational
  /-- The retained lower quadrance is strictly positive. -/ positive : 0 < lowerSq
  /-- Every reading admitted by the original ball has squared norm at least the retained lower bound. -/ lower : ∀
    {value : Data.Gaussian.Basic.Canonical}, ball.Contains value →
    lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value

constructive_injectivity Apart

namespace Apart.mk

end Apart.mk

namespace Apart

/-- A ball with an apartness certificate has nonzero centre. -/
theorem center_nonzero {ball : Ball}
  (apart : Apart ball) :
    ball.center ≠ 0 := by
  intro centerZero
  have lower := apart.lower ball.contains_center
  rw [centerZero, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt apart.positive) lower

end Apart
end Ball

end Purelib.Approximation.Gaussian.Enclosure.Ball

end
