module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
public import Purelib.Geometry.Projective.Hermitian.Boundary.Pullback
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Ring.Nat

public section

open Purelib

open Purelib.Data.Gaussian

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

/-- Pulled-back boundary `normSq z = 2^exponent`. -/
@[expose] def pulledAffineNormDyadic
    (inner : GaussianMatrix)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (exponent : Nat) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.affineNormComparisonForm
          ((2 : Fraction.Rational) ^ exponent))) := by
  let base := Power.natPow Data.Gaussian.Basic.Canonical.gamma exponent
  have sourceIdentity :
      Hermitian.affineNormComparisonForm
          ((2 : Fraction.Rational) ^ exponent) =
        Hermitian.normComparisonForm Coordinates2.Matrix.identityMatrix
          (Data.Gaussian.Norm.Basic.normSq base) := by
    have canonicalIdentity (threshold : Fraction.Rational) :
        Hermitian.affineNormComparisonForm threshold =
          Hermitian.normComparisonForm Coordinates2.Matrix.identityMatrix
            threshold := by
      apply HermitianForm.ext <;>
        simp only [Hermitian.affineNormComparisonForm,
          Purelib.Geometry.Projective.Hermitian.constantForm, Hermitian.normComparisonForm,
          Hermitian.HermitianForm.sub, Hermitian.HermitianForm.add, Hermitian.HermitianForm.neg,
          Hermitian.HermitianForm.scale, Purelib.Geometry.Projective.Hermitian.affineNormForm,
          Coordinates2.Matrix.identityMatrix, Data.Gaussian.Norm.Basic.normSq,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im,
          Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] <;>
        ring1
    rw [canonicalIdentity, Power.normSq_natPow, Constants.normSq_gamma]
  exact BoundaryDescription.cast
    (congrArg (Hermitian.pullbackForm inner)
      sourceIdentity).symm
    (Boundary.pulledNormComparison Coordinates2.Matrix.identityMatrix inner
      (by
        intro determinantZero
        have realZero := congrArg Data.Gaussian.Basic.re determinantZero
        simp only [Matrix2.determinant,
          Coordinates2.Matrix.identityMatrix,
          Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.sub_re,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im,
          Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] at realZero
        exact Fraction.Field.zero_ne_one realZero.symm)
      innerNonzero ⟨rfl, rfl⟩ base)
end Purelib.Geometry.Projective.Hermitian.Boundary

end
