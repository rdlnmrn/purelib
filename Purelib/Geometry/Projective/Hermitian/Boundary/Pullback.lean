module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Boundary.Description
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Boundary

open Purelib.LinearAlgebra

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

/-- Pullback of a rational circle comparison, retaining the composed homography rather than attempting to reconstruct a
circle from coefficients. -/
@[expose] def pulledNormComparison
    (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (base : Data.Gaussian.Basic.Canonical) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.normComparisonForm outer (Data.Gaussian.Norm.Basic.normSq base))) := by
  by_cases baseZero : base = 0
  · have sourceIdentity :
        Hermitian.normComparisonForm outer (Data.Gaussian.Norm.Basic.normSq base) =
          Hermitian.affineNormForm outer.a outer.b := by
      rw [baseZero, Data.Gaussian.Norm.Basic.normSq_zero]
      apply HermitianForm.ext <;>
        simp only [Hermitian.normComparisonForm, Hermitian.HermitianForm.sub, Hermitian.HermitianForm.add,
          Hermitian.HermitianForm.neg, Hermitian.HermitianForm.scale, Hermitian.affineNormForm, -eq_self, -iff_self] <;>
        ring1
    exact BoundaryDescription.cast
      (congrArg (Hermitian.pullbackForm inner)
        sourceIdentity).symm
      (BoundaryDescription.pulledAffineNorm inner outer.a outer.b)
  · exact .curve (.norm (Coordinates2.Matrix.mul outer inner)
      (by change Matrix2.determinant
             (Coordinates2.Matrix.mul outer inner) ≠ 0
          rw [Coordinates2.Matrix.det_mul]
          exact Data.Gaussian.Field.mul_ne_zero_direct outerNonzero innerNonzero)
      (by
        rcases outerLowerRow with ⟨lowerLeft, lowerRight⟩
        constructor <;>
          simp only [Coordinates2.Matrix.mul, lowerLeft, lowerRight,
            Data.Gaussian.Basic.zero_mul,
            Data.Gaussian.Basic.one_mul,
            _root_.zero_add, -eq_self, -iff_self] <;> rfl) base baseZero
      (Hermitian.pullbackForm_normComparison
        outer inner (Data.Gaussian.Norm.Basic.normSq base)))

/-- Pullback of a rational vertical comparison line. -/
@[expose] def pulledRealComparison
    (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (threshold : Fraction.Rational) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.realComparisonForm outer threshold)) := by
  exact .curve (.real (Coordinates2.Matrix.mul outer inner)
    (by change Matrix2.determinant
           (Coordinates2.Matrix.mul outer inner) ≠ 0
        rw [Coordinates2.Matrix.det_mul]
        exact Data.Gaussian.Field.mul_ne_zero_direct outerNonzero innerNonzero)
    (by
      rcases outerLowerRow with ⟨lowerLeft, lowerRight⟩
      constructor <;>
        simp only [Coordinates2.Matrix.mul, lowerLeft, lowerRight,
          Data.Gaussian.Basic.zero_mul,
          Data.Gaussian.Basic.one_mul,
          _root_.zero_add, -eq_self, -iff_self] <;> rfl) threshold
    (Hermitian.pullbackForm_realComparison
      outer inner threshold))

/-- Pullback of a rational horizontal comparison line. -/
@[expose] def pulledImaginaryComparison
    (outer inner : GaussianMatrix)
    (outerNonzero : Matrix2.determinant outer ≠ 0)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (outerLowerRow : outer.c = 0 ∧ outer.d = 1)
    (threshold : Fraction.Rational) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.imagComparisonForm outer threshold)) := by
  exact .curve (.imaginary (Coordinates2.Matrix.mul outer inner)
    (by change Matrix2.determinant
           (Coordinates2.Matrix.mul outer inner) ≠ 0
        rw [Coordinates2.Matrix.det_mul]
        exact Data.Gaussian.Field.mul_ne_zero_direct outerNonzero innerNonzero)
    (by
      rcases outerLowerRow with ⟨lowerLeft, lowerRight⟩
      constructor <;>
        simp only [Coordinates2.Matrix.mul, lowerLeft, lowerRight,
          Data.Gaussian.Basic.zero_mul,
          Data.Gaussian.Basic.one_mul,
          _root_.zero_add, -eq_self, -iff_self] <;> rfl) threshold
    (Hermitian.pullbackForm_imagComparison
      outer inner threshold))
end Purelib.Geometry.Projective.Hermitian.Boundary

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.Projective.Hermitian.Boundary

/-- Transport a boundary description through an inserted identity pullback.

The outer pullback and retained reference matrix are preserved; only the propositionally equal form index changes. -/
private def afterIdentityPullback
    (inner : GaussianMatrix) (form : Hermitian.HermitianForm)
    (description : Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner form)) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.pullbackForm Coordinates2.Matrix.identityMatrix form)) :=
  BoundaryDescription.cast
    (congrArg (Hermitian.pullbackForm inner)
      (Hermitian.pullbackForm_identity form)).symm description
end Purelib.Geometry.Projective.Hermitian.Boundary

end
