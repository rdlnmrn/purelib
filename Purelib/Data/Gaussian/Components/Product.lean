module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Rat.Fraction.Field

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

namespace Purelib.Data.Gaussian.Components.Product

/-- The displayed coordinate formula for a product of two nonzero rational pairs is
nonzero.

Each original pair must have at least one nonzero coordinate, and the retained real
and imaginary identities identify the product pair exactly. -/
theorem complexProductPair_ne_zero
    (A B C D E H : Rational)
    (left : A ≠ 0 ∨ B ≠ 0) (right : C ≠ 0 ∨ D ≠ 0)
    (realIdentity : E = A * C - B * D)
    (imagIdentity : H = A * D + B * C) :
    E ≠ 0 ∨ H ≠ 0 := by
  let z : Canonical := ⟨A, B⟩
  let w : Canonical := ⟨C, D⟩
  have zNonzero : z ≠ 0 := by
    intro zero
    have realZero := congrArg Gaussian.Basic.re zero
    have imagZero := congrArg Gaussian.Basic.im zero
    simp only [z, Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im] at realZero imagZero
    exact left.elim (fun nonzero => nonzero realZero)
      (fun nonzero => nonzero imagZero)
  have wNonzero : w ≠ 0 := by
    intro zero
    have realZero := congrArg Gaussian.Basic.re zero
    have imagZero := congrArg Gaussian.Basic.im zero
    simp only [w, Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im] at realZero imagZero
    exact right.elim (fun nonzero => nonzero realZero)
      (fun nonzero => nonzero imagZero)
  have productNonzero :=
    Field.mul_ne_zero_direct zNonzero wNonzero
  by_cases realZero : E = 0
  · apply Or.inr
    intro imagZero
    apply productNonzero
    apply Gaussian.Basic.ext
    · simp only [Gaussian.Basic.mul_re]
      dsimp only [z, w]
      rw [← realIdentity]
      exact realZero.trans zero_re.symm
    · simp only [Gaussian.Basic.mul_im]
      dsimp only [z, w]
      rw [← imagIdentity, imagZero]
      exact zero_im.symm
  · exact Or.inl realZero
end Purelib.Data.Gaussian.Components.Product

end
