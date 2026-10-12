module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
public import Purelib.Geometry.CCL.Parser.Normalization
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
public import Purelib.Geometry.Projective.Hermitian.Boundary.Pullback
import Purelib.Geometry.Projective.Hermitian.Comparison
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding.Parser.Syntax

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.CCL

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Boundary

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Finite descriptions of CCL atom boundaries

An unresolved Hermitian atom is useful to the equality-owner layer only when
its zero boundary retains constructive provenance.  The boundary is either a
rationally parameterized generalized circle/line, a finite explicit zero set,
or the identically-zero form.  This avoids recovering geometry from bare
coefficients by an unbounded search.
-/

namespace Purelib.Geometry.CCL.Boundary.Description

/-- The scaled norm comparison form equals comparison after the initial-low normalization matrix. -/
private theorem scaledNormComparison_eq
    (exponent : Nat) (threshold : Fraction.Rational) :
    Hermitian.scaledNormComparisonForm exponent threshold =
      Hermitian.normComparisonForm
        (Parser.normalizationMatrix
          .initialLow exponent) threshold := by
  apply HermitianForm.ext
  all_goals
    simp only [Hermitian.scaledNormComparisonForm,
      Hermitian.constantForm,
      Parser.normalizationMatrix,
      Line.Matrix.scale, Hermitian.normComparisonForm, Hermitian.HermitianForm.sub,
      Hermitian.HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
      Hermitian.affineNormForm,
      Basic.one_re,
      Basic.one_im,
      Basic.zero_re,
      Basic.zero_im, Data.Gaussian.Norm.Basic.normSq_one, Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
  · rw [Power.normSq_natPow, Constants.normSq_gamma]
    ring1
  · ring1
  · ring1
  · ring1

/-- Every radial normalization matrix has denominator row zero, one. -/
private theorem normalizationMatrix_lowerRow
    (kind : Syntax.BlockKind) (exponent : Nat) :
    (Parser.normalizationMatrix kind exponent).c = 0 ∧
      (Parser.normalizationMatrix kind exponent).d = 1 := by
  cases kind <;> exact ⟨rfl, rfl⟩

/-- Pulled-back boundary `2^exponent * normSq z = 1`. -/
@[expose] def pulledScaledNormOne
    (inner : GaussianMatrix)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (exponent : Nat) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.scaledNormComparisonForm exponent 1)) := by
  let outer := Parser.normalizationMatrix
    BlockKind.initialLow exponent
  have oneNorm : Data.Gaussian.Norm.Basic.normSq (1 : Data.Gaussian.Basic.Canonical) = 1 := by decide
  have sourceIdentity :
      Hermitian.scaledNormComparisonForm exponent 1 =
        Hermitian.normComparisonForm outer (Data.Gaussian.Norm.Basic.normSq (1 :
          Data.Gaussian.Basic.Canonical)) := by
    have canonicalIdentity (threshold : Fraction.Rational) :
        Hermitian.scaledNormComparisonForm exponent threshold =
          Hermitian.normComparisonForm
            (Parser.normalizationMatrix
              .initialLow exponent) threshold := by
      apply HermitianForm.ext
      all_goals
        simp only [Hermitian.scaledNormComparisonForm,
          Hermitian.constantForm,
          Parser.normalizationMatrix,
          Purelib.Geometry.Projective.Line.Matrix.scale, Hermitian.normComparisonForm,
          Hermitian.HermitianForm.sub, Hermitian.HermitianForm.add, HermitianForm.neg,
          HermitianForm.scale, Hermitian.affineNormForm,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im,
          Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im, Data.Gaussian.Norm.Basic.normSq_one,
            Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
      · rw [Power.normSq_natPow, Constants.normSq_gamma]
        ring1
      · ring1
      · ring1
      · ring1
    rw [canonicalIdentity, oneNorm]
  exact BoundaryDescription.cast
    (congrArg (Hermitian.pullbackForm inner)
      sourceIdentity).symm
    (Boundary.pulledNormComparison outer inner
      (Parser.normalizationMatrix_det_ne
        .initialLow exponent) innerNonzero
      ⟨rfl, rfl⟩ 1)

/-- Pulled-back boundary `2^exponent * normSq z = 2`. -/
@[expose] def pulledScaledNormTwo
    (inner : GaussianMatrix)
    (innerNonzero : Matrix2.determinant inner ≠ 0)
    (exponent : Nat) :
    Boundary.BoundaryDescription inner
      (Hermitian.pullbackForm inner
        (Hermitian.scaledNormComparisonForm exponent 2)) := by
  let outer := Parser.normalizationMatrix
    BlockKind.initialLow exponent
  have sourceIdentity :
      Hermitian.scaledNormComparisonForm exponent 2 =
        Hermitian.normComparisonForm outer (Data.Gaussian.Norm.Basic.normSq
          Data.Gaussian.Basic.Canonical.gamma) := by
    have canonicalIdentity (threshold : Fraction.Rational) :
        Hermitian.scaledNormComparisonForm exponent threshold =
          Hermitian.normComparisonForm
            (Parser.normalizationMatrix
              .initialLow exponent) threshold := by
      apply HermitianForm.ext
      all_goals
        simp only [Hermitian.scaledNormComparisonForm,
          Hermitian.constantForm,
          Parser.normalizationMatrix,
          Purelib.Geometry.Projective.Line.Matrix.scale, Hermitian.normComparisonForm,
          Hermitian.HermitianForm.sub, Hermitian.HermitianForm.add, HermitianForm.neg,
          HermitianForm.scale, Hermitian.affineNormForm,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im,
          Purelib.Data.Gaussian.Basic.zero_re,
          Purelib.Data.Gaussian.Basic.zero_im, Data.Gaussian.Norm.Basic.normSq_one,
            Data.Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
      · rw [Power.normSq_natPow, Constants.normSq_gamma]
        ring1
      · ring1
      · ring1
      · ring1
    rw [canonicalIdentity, Constants.normSq_gamma]
  exact BoundaryDescription.cast
    (congrArg (Hermitian.pullbackForm inner)
      sourceIdentity).symm
    (Boundary.pulledNormComparison outer inner
      (Parser.normalizationMatrix_det_ne
        .initialLow exponent) innerNonzero
      ⟨rfl, rfl⟩ Data.Gaussian.Basic.Canonical.gamma)

end Purelib.Geometry.CCL.Boundary.Description

end
