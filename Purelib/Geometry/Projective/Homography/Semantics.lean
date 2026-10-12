module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Exact semantics of redundant progressive CCL blocks

The arithmetic controller is allowed to select an overlapping safe sector
outside the canonical half-open annulus table.  This file proves that doing
so does not alter the represented point.  Local safety alone gives both the
exact inverse chart and the strict lower norm needed by the following loop.

The zero-residual case is kept projective.  It maps exactly to the completed
block's `omega` tail and can therefore emit the productive unary padding of
`TerminalPadding` without deciding equality.
-/

namespace Purelib.Geometry.Projective.Homography.Semantics

/-- The affine evaluation of a matrix is projectively identical to its homographic value whenever the displayed
denominator is nonzero. -/
theorem actAffine_equivalent_homographic
    (matrix : GaussianMatrix) (tail value : Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : Homography.Basic.denominator matrix tail ≠ 0)
    (evaluates : Homography.Basic.homographic matrix tail = value) :
    Proj.Equivalent
      (Line.Matrix.act matrix (Proj.affine tail))
      (Proj.affine value) := by
  have cancellation :
      Homography.Basic.homographic matrix tail * Homography.Basic.denominator matrix tail =
        Homography.Basic.numerator matrix tail := by
    unfold Homography.Basic.homographic
    rw [Data.Gaussian.Basic.mul_assoc, Data.Gaussian.Field.inv_eq,
      Data.Gaussian.Field.inv_mul _ denominatorNonzero,
      Data.Gaussian.Basic.mul_one]
  rw [evaluates] at cancellation
  dsimp only [Proj.Equivalent, Line.Matrix.act, Proj.affine,
    Homography.Basic.numerator, Homography.Basic.denominator]
  simp only [Data.Gaussian.Basic.mul_one]
  exact cancellation.symm
end Purelib.Geometry.Projective.Homography.Semantics

end
