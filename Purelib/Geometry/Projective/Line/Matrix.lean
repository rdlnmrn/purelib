module

public import Purelib.Geometry.Projective.Line.Basic
public import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra

@[expose] public section
namespace Purelib.Geometry.Projective.Line.Matrix
open Purelib.Geometry.Projective.Line

/-- Matrix action on a homogeneous coordinate pair. -/
def act [Add K] [Mul K] (M : Coordinates2.Matrix K) (x : Proj K) : Proj K :=
  ⟨M.a * x.p + M.b * x.q, M.c * x.p + M.d * x.q⟩

/-- Scaling matrix `S_λ`. -/
def scale [Zero K] [One K] (l : K) : Coordinates2.Matrix K := ⟨l, 0, 0, 1⟩

/-- Translation matrix `T_s`. -/
def translate [Zero K] [One K] (s : K) : Coordinates2.Matrix K := ⟨1, s, 0, 1⟩

/-- Inversion matrix `I_λ`. -/
def invert [Zero K] [One K] (l : K) : Coordinates2.Matrix K := ⟨0, 1, l, 0⟩

section CommRing
variable {K : Type*} [CommRing K]

/-- Matrix multiplication composes homogeneous actions in the same order. -/
theorem act_mul (M N : Coordinates2.Matrix K) (x : Proj K) :
    act (Coordinates2.Matrix.mul M N) x = act M (act N x) := by
  ext <;> simp only [act, Coordinates2.Matrix.mul] <;> ring1

/-- The scaling matrix sends `[z:1]` to `[l*z:1]`.

The second homogeneous coordinate remains one, while the first coordinate is multiplied by the retained scalar. -/
theorem scale_action (l z : K) :
    act (scale l) (Proj.affine z) = ⟨l * z, 1⟩ := by
  ext <;>
    (simp only [act, scale, Proj.affine, zero_mul, mul_one, add_zero, zero_add, -eq_self, -iff_self]
     rfl)

/-- The translation matrix sends `[z:1]` to `[z+s:1]`.

The retained scalar is added to the first coordinate and the affine denominator remains one. -/
theorem translate_action (s z : K) :
    act (translate s) (Proj.affine z) = ⟨z + s, 1⟩ := by
  ext <;>
    (simp only [act, translate, Proj.affine, add_comm, zero_mul, mul_one, one_mul, zero_add, -eq_self, -iff_self]
     rfl)

/-- The inversion matrix sends `[z:1]` to `[1:l*z]`.

The matrix interchanges the affine numerator and denominator and multiplies the new denominator by the retained scalar.
-/
theorem invert_action (l z : K) :
    act (invert l) (Proj.affine z) = ⟨1, l * z⟩ := by
  ext <;>
    (simp only [act, invert, Proj.affine, zero_mul, mul_one, add_zero, zero_add, -eq_self, -iff_self]
     rfl)

/-- Applying a finite decoder to `ω` returns its first column.

The zero second coordinate removes the other matrix column, preserving the original homogeneous first-column entries. -/
theorem act_omega (M : Coordinates2.Matrix K) :
    act M (Proj.omega : Proj K) = ⟨M.a, M.c⟩ := by
  ext <;>
    (simp only [act, Proj.omega, mul_zero, mul_one, add_zero, -eq_self, -iff_self]
     rfl)

/-- A matrix action respects cross-multiplication equivalence. -/
theorem act_respects_equivalent (M : Coordinates2.Matrix K) {x y : Proj K}
    (h : x.Equivalent y) : (act M x).Equivalent (act M y) := by
  dsimp [Proj.Equivalent, act] at h ⊢
  calc
    (M.a * x.p + M.b * x.q) * (M.c * y.p + M.d * y.q) =
        (M.a * y.p + M.b * y.q) * (M.c * x.p + M.d * x.q) +
          (M.a * M.d - M.b * M.c) * (x.p * y.q - y.p * x.q) := by
      ring1
    _ = (M.a * y.p + M.b * y.q) * (M.c * x.p + M.d * x.q) := by
      rw [h]
      ring1

end CommRing

end Purelib.Geometry.Projective.Line.Matrix
end
