module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast

import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

/-!
# Rational affine lines

An affine line retains its Gaussian origin and direction and uses a rational
parameter. Its distance law and endpoint identities describe that same line.
-/

public section

namespace Purelib.Geometry.Rational.Affine

open Purelib.Data.Gaussian

/-- Affine parameterization `origin + t · direction`. -/
@[expose] def line (origin direction : Data.Gaussian.Basic.Canonical) (t :
  Fraction.Rational) : Data.Gaussian.Basic.Canonical :=
  origin + Path.ofCoordinate t * direction

/-- The squared distance between affine parameters is the direction quadrance times their squared difference. -/
theorem normSq_line_sub (origin direction : Data.Gaussian.Basic.Canonical)
  (first last : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (line origin direction first -
      line origin direction last) =
      Data.Gaussian.Norm.Basic.normSq direction * (first - last) ^ 2 := by
  simp only [line, Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.add_re,
    Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
  ring1

/-- The zero parameter of an affine line is its starting point. -/
public theorem line_zero (start direction : Data.Gaussian.Basic.Canonical) :
  line start direction 0 = start := by
  change start + (0 : Data.Gaussian.Basic.Canonical) * direction = start
  rw [Data.Gaussian.Basic.zero_mul, _root_.add_zero]

/-- The unit parameter on the line from start to finish is the finish point. -/
public theorem line_one (start finish : Data.Gaussian.Basic.Canonical) :
  line start (finish - start) 1 = finish := by
  change start + (1 : Data.Gaussian.Basic.Canonical) * (finish - start) = finish
  rw [_root_.one_mul]
  ring1

end Purelib.Geometry.Rational.Affine
