module
public import Purelib.Data.List.Membership

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Finite descriptions of CCL atom boundaries

An unresolved Hermitian atom is useful to the equality-owner layer only when
its zero boundary retains constructive provenance.  The boundary is either a
rationally parameterized generalized circle/line, a finite explicit zero set,
or the identically-zero form.  This avoids recovering geometry from bare
coefficients by an unbounded search.
-/

namespace Purelib.Geometry.Projective.Hermitian.Boundary

set_option genInjectivity false in
/-- Constructive zero-boundary provenance. -/
inductive BoundaryDescription (reference :
  GaussianMatrix) (form : Hermitian.HermitianForm) where
  /-- Retain an explicit circle or line source for the zero boundary. -/ | curve (source : Chart.CurveSource reference
    form)
  /-- Retain a finite list containing every zero, together with global nonnegativity of the form. -/ | finite (points :
    List Data.Gaussian.Basic.Canonical)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
  /-- The Hermitian form vanishes at every Gaussian point. -/ | universal (zero : ∀ value, form.eval value = 0)

constructive_injectivity BoundaryDescription

namespace BoundaryDescription

/-- Transport a boundary description across a proved form identity. -/
@[expose] def cast {reference :
  GaussianMatrix} {left right : Hermitian.HermitianForm}
    (equal : left = right)
    (description : BoundaryDescription reference left) :
      BoundaryDescription reference right := by
  subst right
  exact description

/-- The zero set of a squared affine norm is computed by one equality test. It is empty, a singleton, or universal; no
root search is involved. -/
@[expose] def affineNorm (reference :
  GaussianMatrix) (u v : Data.Gaussian.Basic.Canonical) :
    BoundaryDescription reference (Hermitian.affineNormForm u v) := by
  if uZero : u = 0 then
    if vZero : v = 0 then
      exact .universal (by
        intro value
        rw [Hermitian.eval_affineNormForm, uZero, vZero, Data.Gaussian.Basic.zero_mul, _root_.zero_add,
          Data.Gaussian.Norm.Basic.normSq_zero])
    else
      exact .finite [] (by
          intro value evaluatesZero
          rw [Hermitian.eval_affineNormForm, uZero, Data.Gaussian.Basic.zero_mul, _root_.zero_add] at evaluatesZero
          exact (vZero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp evaluatesZero)).elim)
        (by
          intro value
          rw [Hermitian.eval_affineNormForm, uZero, Data.Gaussian.Basic.zero_mul, _root_.zero_add]
          exact Data.Gaussian.Norm.Basic.normSq_nonneg v)
  else
    let point := (-v) * u⁻¹
    exact .finite [point] (by
        intro value evaluatesZero
        have affineZero : u * value + v = 0 := by
          apply Data.Gaussian.Norm.Basic.normSq_eq_zero.mp
          simpa only [Hermitian.eval_affineNormForm, -eq_self, -iff_self] using evaluatesZero
        have product : u * value = -v := by
          apply Data.Gaussian.Basic.ext
          · have coordinate := congrArg
                Data.Gaussian.Basic.re affineZero
            simp only [Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.zero_re,
              -eq_self, -iff_self] at coordinate
            simp only [Purelib.Data.Gaussian.Basic.neg_re, -eq_self, -iff_self]
            calc
              (u * value).re = (u * value).re + v.re - v.re := by ring1
              _ = 0 - v.re := by rw [coordinate]
              _ = -v.re := by ring1
          · have coordinate := congrArg
                Data.Gaussian.Basic.im affineZero
            simp only [Purelib.Data.Gaussian.Basic.add_im, Purelib.Data.Gaussian.Basic.zero_im,
              -eq_self, -iff_self] at coordinate
            simp only [Purelib.Data.Gaussian.Basic.neg_im, -eq_self, -iff_self]
            calc
              (u * value).im = (u * value).im + v.im - v.im := by ring1
              _ = 0 - v.im := by rw [coordinate]
              _ = -v.im := by ring1
        have pointProduct : point * u = -v := by
          dsimp only [point]
          calc
            (-v) * u⁻¹ * u = (-v) * (u⁻¹ * u) :=
              Data.Gaussian.Basic.mul_assoc _ _ _
            _ = (-v) * 1 := by
              rw [Data.Gaussian.Field.inv_eq,
                Data.Gaussian.Field.inv_mul _ uZero]
            _ = -v := Data.Gaussian.Basic.mul_one _
        have equal : value = point := by
          apply Data.Gaussian.Field.mul_right_cancel_of_ne uZero
          calc
            value * u = u * value :=
              Data.Gaussian.Basic.mul_comm _ _
            _ = -v := product
            _ = point * u := pointProduct.symm
        exact Purelib.Data.List.Membership.mem_singleton.mpr equal)
      (by
        intro value
        rw [Hermitian.eval_affineNormForm]
        exact Data.Gaussian.Norm.Basic.normSq_nonneg (u * value + v))

/-- Pulling back a squared affine norm still has an explicit finite zero-set description. -/
@[expose] def pulledAffineNorm
    (matrix : GaussianMatrix) (u v : Data.Gaussian.Basic.Canonical) :
    BoundaryDescription matrix
      (Hermitian.pullbackForm matrix
        (Hermitian.affineNormForm u v)) :=
  cast
    (Hermitian.pullbackForm_affineNorm matrix u v).symm
    (affineNorm matrix (u * matrix.a + v * matrix.c)
      (u * matrix.b + v * matrix.d))

end BoundaryDescription
end Purelib.Geometry.Projective.Hermitian.Boundary

end
