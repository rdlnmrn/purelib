module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Order
import Purelib.Data.Gaussian.Basic

public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring

public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Gaussian Purelib.Data.Gaussian.Basic

/-- Conjugate a Gaussian integer by negating its imaginary coordinate.

The real coordinate remains unchanged and the imaginary coordinate uses the
original integer negation operation. -/
@[expose] def conj (z : GaussianInt) : GaussianInt := ⟨z.re, -z.im⟩

/-- Coordinatewise embedding commutes with Gaussian-integer conjugation.

The owned integer cast law identifies the negated imaginary coordinate; both
real-coordinate readbacks are definitionally equal. -/
@[simp] theorem toGaussian_conj (z : GaussianInt) :
    toGaussian (conj z) = Basic.conj
      (toGaussian z) := by
  apply Basic.ext
  · rfl
  · simp only [-eq_self, -iff_self, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    change ((-z.im : Int) : Coordinate) = -(z.im : Coordinate)
    exact Purelib.Algebra.Ring.IntCast.neg z.im

/-- Conjugating a Gaussian integer preserves its natural squared norm. -/
@[simp] theorem normNat_conj (z : GaussianInt) :
    normNat (conj z) = normNat z := by
  apply congrArg Int.natAbs
  change z.re * z.re + (-z.im) * (-z.im) = z.re * z.re + z.im * z.im
  ring1

/-- A Gaussian integer times its conjugate is its real natural quadrance.

Nonnegativity identifies the magnitude of the original integer norm with that
norm itself. The imaginary product coordinate vanishes by scalar arithmetic. -/
theorem mul_conj (z : GaussianInt) : z * conj z = ofNat (normNat z) := by
  apply GaussianInt.ext
  · change z.re * z.re - z.im * -z.im = (normNat z : Nat)
    rw [normNat, Purelib.Data.Int.Order.natAbs_of_nonneg (normInt_nonneg z)]
    dsimp only [normInt]
    ring1
  · change z.re * -z.im + z.im * z.re = 0
    ring1

end Purelib.Data.GaussianInt
end
