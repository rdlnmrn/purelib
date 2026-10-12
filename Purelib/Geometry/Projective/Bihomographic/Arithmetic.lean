module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Bihomographic.Basic
import Purelib.Geometry.Projective.Line.Basic
import Init.Prelude
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Bihomographic.Basic

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Constructive bihomographic states for elementary CCL arithmetic

The arithmetic state is kept homogeneous.  This avoids dividing by an input
or output denominator merely to state substitution correctness, and it makes
zero and pole outcomes ordinary projective coordinates rather than hidden
exceptional values.
-/

namespace Purelib.Geometry.Projective.Bihomographic.Arithmetic

/-- The four elementary projective operations. -/
inductive Operation where
  /-- Addition of the two homogeneous inputs. -/ | add /-- Subtraction of the second homogeneous input from the first.
    -/ | sub /-- Multiplication of the two homogeneous inputs. -/ | mul /-- Homogeneous division of the first input by
    the second, retaining a zero denominator as a pole. -/ | div
deriving DecidableEq

derive_exposed_repr Operation

/-- Initial coefficient tuple for an elementary operation. -/
def initial :
  Operation → Bihomographic.Basic.State
  | .add => ⟨0, 1, 1, 0, 0, 0, 0, 1⟩
  | .sub => ⟨0, 1, -1, 0, 0, 0, 0, 1⟩
  | .mul => ⟨1, 0, 0, 0, 0, 0, 0, 1⟩
  | .div => ⟨0, 1, 0, 0, 0, 0, 1, 0⟩

/-- The addition state maps affine inputs to their affine sum. -/
theorem initial_add (x y : Data.Gaussian.Basic.Canonical) :
    (initial .add).affineMap x y = Proj.affine (x + y) := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.affineMap, State.map, initial, Proj.affine,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re,
          Data.Gaussian.Basic.one_im] <;>
      ring1

/-- The subtraction state maps affine inputs to their affine difference. -/
theorem initial_sub (x y : Data.Gaussian.Basic.Canonical) :
    (initial .sub).affineMap x y = Proj.affine (x - y) := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.affineMap, State.map, initial, Proj.affine,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
          Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im,
        Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re,
          Data.Gaussian.Basic.one_im] <;> ring1

/-- The multiplication state maps affine inputs to their affine product. -/
theorem initial_mul (x y : Data.Gaussian.Basic.Canonical) :
    (initial .mul).affineMap x y = Proj.affine (x * y) := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.affineMap, State.map, initial, Proj.affine,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re,
          Data.Gaussian.Basic.one_im] <;>
      ring1

/-- Division is the homogeneous pair `[x:y]`. If `y=0`, this is the pole coordinate rather than an illicit affine
quotient. -/
theorem initial_div (x y : Data.Gaussian.Basic.Canonical) :
    (initial .div).affineMap x y = ⟨x, y⟩ := by
  apply Proj.ext <;>
    apply Data.Gaussian.Basic.ext <;>
      simp only [State.affineMap, State.map, initial, Proj.affine,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
          Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im, Data.Gaussian.Basic.one_re,
          Data.Gaussian.Basic.one_im] <;>
      ring1

end Purelib.Geometry.Projective.Bihomographic.Arithmetic

end
