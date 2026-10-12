module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Hermitian.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

section
@[expose] public section

/-!
# Finite rational geometry of CCL comparisons

Every radial or coordinate comparison made after a finite decoder homography
pulls back to a four-coefficient Hermitian form

`a * (x² + y²) + b * x + c * y + d`.

The coefficients and the evaluated point are constructive rationals.  These
identities are the algebraic input for the finite x--y curve classifier used
by the persistent next-bit controller.
-/

namespace Purelib.Geometry.Projective.Hermitian

/-- Form evaluating to the squared norm of `u * z + v`. -/
def affineNormForm (u v : Data.Gaussian.Basic.Canonical) :
  Hermitian.HermitianForm where
  radial := Data.Gaussian.Norm.Basic.normSq u
  realLinear := 2 * (u.re * v.re + u.im * v.im)
  imagLinear := 2 * (u.re * v.im - u.im * v.re)
  constant := Data.Gaussian.Norm.Basic.normSq v

/-- The affine norm form evaluates to the squared norm of `u*z+v`. -/
theorem eval_affineNormForm (u v value : Data.Gaussian.Basic.Canonical) :
    (affineNormForm u v).eval value = Data.Gaussian.Norm.Basic.normSq (u * value
      + v) := by
  simp only [HermitianForm.eval, affineNormForm, Data.Gaussian.Norm.Basic.normSq,
    Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im]
  ring1

/-- Form evaluating to the real part of `(u * z + v) * conj (s * z + t)`. -/
def realCrossForm (u v s t : Data.Gaussian.Basic.Canonical) :
  Hermitian.HermitianForm where
  radial := u.re * s.re + u.im * s.im
  realLinear :=
    u.re * t.re + u.im * t.im + v.re * s.re + v.im * s.im
  imagLinear :=
    u.re * t.im - u.im * t.re + v.im * s.re - v.re * s.im
  constant := v.re * t.re + v.im * t.im

/-- Form evaluating to the imaginary part of the same cross product. -/
def imagCrossForm (u v s t : Data.Gaussian.Basic.Canonical) :
  Hermitian.HermitianForm where
  radial := u.im * s.re - u.re * s.im
  realLinear :=
    u.im * t.re - u.re * t.im + v.im * s.re - v.re * s.im
  imagLinear :=
    u.re * t.re + u.im * t.im - v.re * s.re - v.im * s.im
  constant := v.im * t.re - v.re * t.im

/-- The real cross form evaluates to the real part of the affine conjugate product. -/
theorem eval_realCrossForm (u v s t value : Data.Gaussian.Basic.Canonical)
  :
    (realCrossForm u v s t).eval value =
      ((u * value + v) * Data.Gaussian.Basic.conj (s * value + t)).re := by
  simp only [HermitianForm.eval, realCrossForm, Data.Gaussian.Norm.Basic.normSq,
    Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.conj]
  ring1

/-- The imaginary cross form evaluates to the imaginary part of the affine conjugate product. -/
theorem eval_imagCrossForm (u v s t value : Data.Gaussian.Basic.Canonical)
  :
    (imagCrossForm u v s t).eval value =
      ((u * value + v) * Data.Gaussian.Basic.conj (s * value + t)).im := by
  simp only [HermitianForm.eval, imagCrossForm, Data.Gaussian.Norm.Basic.normSq,
    Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.conj]
  ring1
end Purelib.Geometry.Projective.Hermitian

end

public section

namespace Purelib.Geometry.Projective.Hermitian

open Purelib.Data
open Purelib.Data.Rat

/-- Retain the Hermitian form of squared Gaussian displacement from one original rational centre. -/
@[expose] def distanceSqForm (center : Gaussian.Basic.Canonical) : HermitianForm :=
  affineNormForm 1 (-center)

/-- The retained distance form evaluates to the squared displacement from its original centre. -/
theorem eval_distanceSqForm (center point : Gaussian.Basic.Canonical) :
    (distanceSqForm center).eval point = Gaussian.Norm.Basic.normSq (point - center) := by
  rewrite [distanceSqForm, eval_affineNormForm, Gaussian.Basic.one_mul, Gaussian.Basic.sub_eq_add_neg]
  rfl

/-- Every squared-distance form has nonzero radial coefficient, independently of its original centre. -/
theorem distanceSqForm_nonzero (center : Gaussian.Basic.Canonical) : ¬(distanceSqForm center).IsZero := by
  intro zero
  have radialZero := zero.1
  change Gaussian.Norm.Basic.normSq (1 : Gaussian.Basic.Canonical) = 0 at radialZero
  rewrite [Gaussian.Norm.Basic.normSq_one] at radialZero
  exact Fraction.Field.zero_ne_one radialZero.symm

end Purelib.Geometry.Projective.Hermitian
