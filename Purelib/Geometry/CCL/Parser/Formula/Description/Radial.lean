module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.CCL.Boundary.Description
public import Purelib.Geometry.CCL.Parser.Formula.Radial
import Purelib.Geometry.Projective.Hermitian.Affine
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Boundary.Description
public import Purelib.Geometry.Projective.Hermitian.Boundary.Dyadic
public import Purelib.Geometry.Projective.Hermitian.Formula.Description
import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.Geometry.Projective.Hermitian.Pullback
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Hermitian.Radial
import Purelib.Tactic.Ring

public section

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Geometry.CCL.Boundary

open Purelib.Geometry.CCL.Parser

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Boundary

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Boundary provenance for finite CCL formulas

This module follows the syntax tree of each next-bit formula.  Every atom is
paired with a constructive description of its exact zero boundary.  Formula
inspection can therefore hand an unresolved atom directly to the finite
curve-event layer without guessing its geometric origin from coefficients.
-/

namespace Purelib.Geometry.CCL.Parser.Formula.Description

/-- Boundary descriptions for a radial bracket after one input-coordinate pullback. -/
@[expose] def pulledRadial
    (kind : Syntax.BlockKind) (exponent : Nat) (inner : GaussianMatrix)
    (innerNonzero : Matrix2.determinant inner ≠ 0) :
    Formula.Descriptions inner
      ((Formula.radialFormula kind exponent Coordinates2.Matrix.identityMatrix).pullback inner) := by
  have identityPullback (form : Hermitian.HermitianForm) :
      Hermitian.pullbackForm Coordinates2.Matrix.identityMatrix form = form := by
    apply HermitianForm.ext <;>
      simp only [Hermitian.pullbackForm,
        Coordinates2.Matrix.identityMatrix, Hermitian.HermitianForm.add, Hermitian.HermitianForm.scale,
        Purelib.Geometry.Projective.Hermitian.affineNormForm, Purelib.Geometry.Projective.Hermitian.realCrossForm,
          Purelib.Geometry.Projective.Hermitian.imagCrossForm, Data.Gaussian.Norm.Basic.normSq,
        Purelib.Data.Gaussian.Basic.one_re,
        Purelib.Data.Gaussian.Basic.one_im,
        Purelib.Data.Gaussian.Basic.zero_re,
        Purelib.Data.Gaussian.Basic.zero_im, -eq_self, -iff_self] <;>
      ring1
  let afterIdentityPullback (matrix : GaussianMatrix) (form : Hermitian.HermitianForm)
      (description : Boundary.BoundaryDescription matrix
        (Hermitian.pullbackForm matrix form)) :
      Boundary.BoundaryDescription matrix
        (Hermitian.pullbackForm matrix
          (Hermitian.pullbackForm Coordinates2.Matrix.identityMatrix form)) :=
    BoundaryDescription.cast
      (congrArg (Hermitian.pullbackForm matrix)
        (identityPullback form)).symm description
  cases kind with
  | initialHigh =>
      simp only [Formula.radialFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Boundary.pulledAffineNormDyadic
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Boundary.pulledAffineNormDyadic
              inner innerNonzero (exponent + 1))))
  | initialLow =>
      simp only [Formula.radialFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Description.pulledScaledNormOne
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Description.pulledScaledNormTwo
              inner innerNonzero exponent)))
  | loop =>
      simp only [Formula.radialFormula, BoundaryFormula.pullback,
        Purelib.Geometry.Projective.Hermitian.Formula.pullbackAtom, -eq_self, -iff_self]
      exact Descriptions.and
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Boundary.pulledAffineNormDyadic
              inner innerNonzero exponent)))
        (Descriptions.atom _
          (afterIdentityPullback inner _
            (Boundary.pulledAffineNormDyadic
              inner innerNonzero (exponent + 1))))
end Purelib.Geometry.CCL.Parser.Formula.Description

end
