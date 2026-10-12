module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry.Rational

section
@[expose] public section

/-!
# Affine segments retain their finite winding under subdivision

The normalized coordinate coefficient lists identify an affine subsegment
with the corresponding affine substitution of the original line.  Cauchy
index reparameterization then relates its unit interval to the original
parameter interval, including reversed and stationary clear subsegments.
-/

namespace Purelib.Geometry.Rational.Affine.Reparameterization

/-- Composing an affine line with an affine change of parameter gives the same reparameterized point. -/
theorem line_affine (origin direction :
  Data.Gaussian.Basic.Canonical) (offset slope time : Fraction.Rational) :
    Affine.line (Affine.line origin direction offset) (Path.ofCoordinate slope * direction) time =
      Affine.line origin direction (offset + slope * time) := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Affine.line, Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im]
      <;>
    ring1
end Purelib.Geometry.Rational.Affine.Reparameterization

end
