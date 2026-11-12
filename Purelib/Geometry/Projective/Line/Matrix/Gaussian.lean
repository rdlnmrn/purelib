module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Geometry.Projective.Line.Scale

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Line.Matrix.Gaussian.Mat2

/-- A nonzero-determinant matrix preserves finite projective validity. -/
theorem act_hasNonzeroCoordinate {matrix :
  GaussianMatrix} {point : Line.GaussianLine}
    (determinantNonzero : (Matrix2.determinant matrix) ≠ 0)
    (pointValid : (Proj.HasNonzeroCoordinate point)) :
    Proj.HasNonzeroCoordinate (Line.Matrix.act matrix point) := by
  by_cases numeratorZero : (Line.Matrix.act matrix point).p = 0
  · apply Or.inr
    intro denominatorZero
    rcases pointValid with pointNumeratorNonzero | pointDenominatorNonzero
    · have determinantProduct : (Matrix2.determinant matrix) * point.p = 0 := by
        calc
          (Matrix2.determinant matrix) * point.p =
              matrix.d * (Line.Matrix.act matrix point).p -
                matrix.b * (Line.Matrix.act matrix point).q := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Matrix2.determinant, Line.Matrix.act, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
                Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
                  Data.Gaussian.Basic.mul_im] <;>
              ring1
          _ = 0 := by
            rw [numeratorZero, denominatorZero]
            apply Data.Gaussian.Basic.ext <;>
              simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
                Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im] <;>
              ring1
      exact Data.Gaussian.Field.mul_ne_zero_direct
        determinantNonzero pointNumeratorNonzero determinantProduct
    · have determinantProduct : (Matrix2.determinant matrix) * point.q = 0 := by
        calc
          (Matrix2.determinant matrix) * point.q =
              matrix.a * (Line.Matrix.act matrix point).q -
                matrix.c * (Line.Matrix.act matrix point).p := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Matrix2.determinant, Line.Matrix.act, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
                Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
                  Data.Gaussian.Basic.mul_im] <;>
              ring1
          _ = 0 := by
            rw [denominatorZero, numeratorZero]
            apply Data.Gaussian.Basic.ext <;>
              simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
                Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im] <;>
              ring1
      exact Data.Gaussian.Field.mul_ne_zero_direct
        determinantNonzero pointDenominatorNonzero determinantProduct
  · exact Or.inl numeratorZero

end Purelib.Geometry.Projective.Line.Matrix.Gaussian.Mat2

end

public section

namespace Purelib.Geometry.Projective.Line.Matrix.Gaussian.Mat2

/-- Pull a homogeneous image back through the supplied matrix's explicit adjugate. -/
@[expose] def pullback (matrix : GaussianMatrix) (image : Line.GaussianLine) : Line.GaussianLine :=
  Line.Matrix.act (BoundaryAdjugate.adjugate matrix) image

/-- Pulling back an actual matrix image scales the original homogeneous pair by that matrix's determinant. -/
theorem pullback_act (matrix : GaussianMatrix) (point : Line.GaussianLine) :
    pullback matrix (Line.Matrix.act matrix point) =
      Line.Gaussian.Proj.scale (Matrix2.determinant matrix) point := by
  unfold pullback
  rewrite [← Line.Matrix.act_mul, BoundaryAdjugate.adjugate_mul]
  apply Line.Proj.ext <;>
    simp only [Line.Matrix.act, Line.Gaussian.Proj.scale,
      Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.add_zero, Data.Gaussian.Basic.zero_add,
      -eq_self, -iff_self] <;> rfl

/-- A nonzero determinant and a valid image give a valid explicit pullback. -/
theorem pullback_valid {matrix : GaussianMatrix} {image : Line.GaussianLine}
    (determinantNonzero : Matrix2.determinant matrix ≠ 0) (imageValid : Proj.HasNonzeroCoordinate image) :
    Proj.HasNonzeroCoordinate (pullback matrix image) := by
  have adjugateNonzero : Matrix2.determinant (BoundaryAdjugate.adjugate matrix) ≠ 0 := by
    change BoundaryAdjugate.determinant (BoundaryAdjugate.adjugate matrix) ≠ 0
    rewrite [BoundaryAdjugate.determinant_adjugate]
    exact determinantNonzero
  exact act_hasNonzeroCoordinate adjugateNonzero imageValid

/-- An image equivalent to an affine matrix image pulls back to that same affine point. -/
theorem pullback_equivalent_affine {matrix : GaussianMatrix} {image : Line.GaussianLine}
    {value : Data.Gaussian.Basic.Canonical} (determinantNonzero : Matrix2.determinant matrix ≠ 0)
    (equivalent : image.Equivalent (Line.Matrix.act matrix (Line.Proj.affine value))) :
    (pullback matrix image).Equivalent (Line.Proj.affine value) := by
  have pulled := Line.Matrix.act_respects_equivalent (BoundaryAdjugate.adjugate matrix) equivalent
  change (pullback matrix image).Equivalent (pullback matrix (Line.Matrix.act matrix (Line.Proj.affine value)))
    at pulled
  rewrite [pullback_act] at pulled
  have scaleValid : Proj.HasNonzeroCoordinate
      (Line.Gaussian.Proj.scale (Matrix2.determinant matrix) (Line.Proj.affine value)) :=
    Line.Proj.scale_nonzero determinantNonzero (Proj.affine_hasNonzeroCoordinate value)
  exact Proj.equivalent_trans pulled
    (Line.Proj.Equivalent.symm (Line.Proj.equivalent_scale (Line.Proj.affine value) (Matrix2.determinant matrix)))
    scaleValid (Proj.affine_hasNonzeroCoordinate value)

/-- Read the total affine quotient of the explicit matrix pullback.

Its affine interpretation requires the pulled denominator to be nonzero.
The supplied-image correctness laws establish that condition when the image
has a certified affine preimage under a nonsingular matrix.
-/
@[expose] def affinePullback (matrix : GaussianMatrix) (image : Line.GaussianLine) :
    Data.Gaussian.Basic.Canonical := Proj.affineReading (pullback matrix image)

/-- A valid image with an affine preimage has a nonzero pulled denominator. -/
theorem pullback_denominator_ne_zero {matrix : GaussianMatrix} {image : Line.GaussianLine}
    {value : Data.Gaussian.Basic.Canonical} (determinantNonzero : Matrix2.determinant matrix ≠ 0)
    (imageValid : Proj.HasNonzeroCoordinate image)
    (equivalent : image.Equivalent (Line.Matrix.act matrix (Line.Proj.affine value))) :
    (pullback matrix image).q ≠ 0 :=
  Proj.denominator_ne_zero_of_equivalent_affine (pullback_valid determinantNonzero imageValid)
    (pullback_equivalent_affine determinantNonzero equivalent)

/-- The computed affine pullback is the exact affine preimage named by the supplied image certificate. -/
theorem affinePullback_eq {matrix : GaussianMatrix} {image : Line.GaussianLine}
    {value : Data.Gaussian.Basic.Canonical} (determinantNonzero : Matrix2.determinant matrix ≠ 0)
    (imageValid : Proj.HasNonzeroCoordinate image)
    (equivalent : image.Equivalent (Line.Matrix.act matrix (Line.Proj.affine value))) :
    affinePullback matrix image = value :=
  Proj.affineReading_eq_of_equivalent
    (pullback_denominator_ne_zero determinantNonzero imageValid equivalent)
    (pullback_equivalent_affine determinantNonzero equivalent)

end Purelib.Geometry.Projective.Line.Matrix.Gaussian.Mat2

end
