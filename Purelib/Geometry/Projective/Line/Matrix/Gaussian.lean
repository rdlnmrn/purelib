module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

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
