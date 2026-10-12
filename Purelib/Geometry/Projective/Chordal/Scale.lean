module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
public import Purelib.Geometry.Projective.Homography.Scale
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Homography

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Matrix

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
/-!
# Choice-free completed-block chordal contraction

This file proves the affine two-tail part of the companion paper's completed
CCL block contraction.  The proof is entirely cross-multiplied over explicit
fractions; no square root, limit, supremum, or inherited ordered-field
division theorem is used.
-/

@[expose] public section

namespace Purelib.Geometry.Projective.Chordal.Scale

/-- A nonzero common matrix scale preserves squared chordal quadrance of its two images. -/
theorem chordalSq_act_scaleMatrix (scalar :
  Data.Gaussian.Basic.Canonical)
    (scalarNonzero : scalar ≠ 0) (matrix : GaussianMatrix) (left right :
      GaussianLine) :
    Chordal.Basic.chordalSq (Line.Matrix.act (Scale.scaleMatrix scalar matrix) left)
        (Line.Matrix.act (Scale.scaleMatrix scalar matrix) right) =
      Chordal.Basic.chordalSq (Line.Matrix.act matrix left) (Line.Matrix.act matrix right) := by
  rw [Scale.act_scaleMatrix, Scale.act_scaleMatrix,
    Equivalence.chordalSq_scale_left scalar scalarNonzero,
    Equivalence.chordalSq_scale_right scalar scalarNonzero]
end Purelib.Geometry.Projective.Chordal.Scale

end

end

section
@[expose] public section

/-!
# Constructive invariance under decoder scale folds

Right multiplication by `S_λ` moves a nonzero scale from an affine tail into
the first decoder column.  These finite identities are the formal content of
the scale- and quarter-unit-fold invariance used by the CCL parser.
-/

namespace Purelib.Geometry.Projective.Chordal.Scale

/-- Two affine tails are transported to exactly the same displayed points before and after a common scale fold. -/
theorem chordalSq_twoTail (matrix :
  GaussianMatrix) (scale left right : Data.Gaussian.Basic.Canonical) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Scale.rightScale matrix scale) (Proj.affine left))
        (Line.Matrix.act (Scale.rightScale matrix scale) (Proj.affine right)) =
      Chordal.Basic.chordalSq
        (Line.Matrix.act matrix (Proj.affine (scale * left)))
        (Line.Matrix.act matrix (Proj.affine (scale * right))) := by
  rw [Scale.act_affine, Scale.act_affine]

/-- With the decoder matrix nonsingular and the folded scale nonzero, the one-tail truncation quadrance is also exactly
invariant. -/
theorem chordalSq_truncation (matrix :
  GaussianMatrix) (scale tail : Data.Gaussian.Basic.Canonical)
    (matrixNonzero : Matrix2.determinant matrix ≠ 0)
    (scaleNonzero : scale ≠ 0) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act (Scale.rightScale matrix scale) (Proj.affine tail))
        (Line.Matrix.act (Scale.rightScale matrix scale) Proj.omega) =
      Chordal.Basic.chordalSq
        (Line.Matrix.act matrix (Proj.affine (scale * tail)))
        (Line.Matrix.act matrix Proj.omega) := by
  rw [Scale.act_affine]
  apply Equivalence.chordalSq_eq_of_equivalent_right
  · apply Gaussian.Mat2.act_hasNonzeroCoordinate
    · rw [Scale.det_rightScale]
      exact Data.Gaussian.Field.mul_ne_zero_direct
        matrixNonzero scaleNonzero
    · exact Proj.omega_hasNonzeroCoordinate
  · exact Gaussian.Mat2.act_hasNonzeroCoordinate
      matrixNonzero Proj.omega_hasNonzeroCoordinate
  · exact Scale.act_omega_equivalent matrix scale

end Purelib.Geometry.Projective.Chordal.Scale

end
