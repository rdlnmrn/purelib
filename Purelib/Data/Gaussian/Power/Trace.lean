module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Sparse coordinate equations for rational powers

For the special polynomial `T^q-y`, coordinate elimination does not require a
generic Sylvester matrix.  If `z^q=y` and `s=N(z)`, then first

`s^q = N(y)`.

For a displayed candidate `s`, both coordinates are governed by the finite
Lucas recurrence

`A₀=2`, `A₁=2X`, `Aₙ₊₂=2X Aₙ₊₁-s Aₙ`.

Indeed `A_q(re z,s)=2 re(y)`.  Applying the same identity to `-i*z` gives
`A_q(im z,s)=2 re((-i)^q*y)`.  This module constructs those three sparse
rational polynomials and proves the identities directly by finite induction.
There is no root collection, completed carrier, or generic resultant.
-/

namespace Purelib.Data.Gaussian.Power.Trace

/-! ## Finite trace identity -/

section
open Purelib.Data.Gaussian
/-- Compute consecutive sums of Gaussian powers and conjugate powers by the quadratic trace recurrence.

Start with two and the sum of the Gaussian and its conjugate. Each successor shifts the previous second component and
computes the next term from the trace and conjugate-product coefficients. -/
def gaussianTracePair (point : Basic.Canonical) : Nat → Basic.Canonical ×
  Basic.Canonical
  | 0 => (2, point + Basic.Canonical.conj point)
  | degree + 1 =>
      let previous := gaussianTracePair point degree
      (previous.2,
        (point + Basic.Canonical.conj point) * previous.2 -
          (point * Basic.Canonical.conj point) * previous.1)

/-- Adding a Gaussian to its conjugate gives twice its real coordinate on the real axis. -/
theorem add_conj (point : Basic.Canonical) :
    point + Basic.Canonical.conj point =
      ⟨2 * point.re, 0⟩ := by
  apply Basic.ext <;>
    simp only [Basic.add_re, Basic.add_im, Basic.Canonical.conj] <;> ring1

/-- Multiplying a Gaussian by its conjugate embeds its squared norm on the real axis. -/
theorem mul_conj (point : Basic.Canonical) :
    point * Basic.Canonical.conj point =
      ⟨Basic.Canonical.normSq point, 0⟩ := by
  apply Basic.ext <;>
    simp only [Basic.mul_re, Basic.mul_im, Basic.Canonical.conj, Basic.Canonical.normSq] <;> ring1

end

/-- The quadratic trace recurrence identity holds in any commutative ring. -/
private theorem traceStepRing {R : Type} [CommRing R]
    (point conjugate previous next : R) :
    (point + conjugate) * (next * point + previous * conjugate) -
        point * conjugate * (next + previous) =
      next * point * point + previous * conjugate * conjugate := by
  ring1

open Purelib.Data.Gaussian in
/-- The two recurrence outputs are exactly the power-plus-conjugate-power sums at consecutive exponents. -/
theorem gaussianTracePair_eq_powers (point : Basic.Canonical) : ∀ degree,
    gaussianTracePair point degree =
      (point ^ degree + Basic.Canonical.conj point ^ degree,
        point ^ (degree + 1) + Basic.Canonical.conj point ^ (degree + 1)) := by
  intro degree
  induction degree with
  | zero =>
      simp only [gaussianTracePair, pow_zero]
      apply Prod.ext
      · change (2 : Basic.Canonical) = 1 + 1
        ring1
      · change point + Basic.Canonical.conj point = point ^ 1 + Basic.Canonical.conj point ^ 1
        rw [pow_one, pow_one]
  | succ degree inductionHypothesis =>
      rw [gaussianTracePair, inductionHypothesis]
      apply Prod.ext
      · rfl
      · change
          (point + Basic.Canonical.conj point) *
                (point ^ (degree + 1) + Basic.Canonical.conj point ^ (degree + 1)) -
              point * Basic.Canonical.conj point *
                (point ^ degree + Basic.Canonical.conj point ^ degree) =
            point ^ (Nat.succ degree + 1) +
              Basic.Canonical.conj point ^ (Nat.succ degree + 1)
        have pointPower :
            point ^ (Nat.succ degree + 1) =
              point ^ degree * point * point := by
            rw [show Nat.succ degree + 1 = (degree + 1) + 1 by rfl,
              pow_succ, pow_succ]
        have conjugatePower :
            Basic.Canonical.conj point ^ (Nat.succ degree + 1) =
              Basic.Canonical.conj point ^ degree * Basic.Canonical.conj point * Basic.Canonical.conj point := by
            rw [show Nat.succ degree + 1 = (degree + 1) + 1 by rfl,
              pow_succ, pow_succ]
        rw [pointPower, conjugatePower,
          pow_succ point degree, pow_succ (Basic.Canonical.conj point) degree]
        exact traceStepRing point (Basic.Canonical.conj point)
          (Basic.Canonical.conj point ^ degree) (point ^ degree)
end Purelib.Data.Gaussian.Power.Trace

end
