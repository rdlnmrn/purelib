module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Safe
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Productive unary padding at a projective CCL terminal

An arithmetic transducer cannot in general decide that opaque nonterminating
inputs have combined to an exact Gaussian rational.  The canonical finite
encoder remains unchanged.  This module supplies a separate projective
continuation convention: after a completed sector, an unresolved zero
residual may remain at `omega`, and every further unary `1` fixes that formal
coordinate while strengthening the finite large-tail predicate.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder.Safe.Transport

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A nonsingular matrix transports a retained safe cylinder bound by its exact chordal transport coefficient.

The two points realize the same redundant block list through exact safe tails. The coefficient multiplies one half to
that original list length. -/
theorem chordalSq_act_realizes_le_transportCoefficient_half_pow
    (matrix : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix)
    (determinantNonzero :
      Matrix2.BoundaryAdjugate.determinant matrix ≠ 0)
    {blocks : List Data.CCL.Encoding.Block.Redundant}
    {left right : Line.GaussianLine}
    (leftRealizes :
      Cylinder.Safe.Realizes blocks left)
    (rightRealizes :
      Cylinder.Safe.Realizes blocks right) :
    Chordal.Basic.chordalSq (Line.Matrix.act matrix left) (Line.Matrix.act matrix right) ≤
      Chordal.Transport.transportCoefficient matrix *
        (1 / 2 : Fraction.Rational) ^ blocks.length := by
  calc
    Chordal.Basic.chordalSq (Line.Matrix.act matrix left) (Line.Matrix.act matrix right) ≤
        Chordal.Transport.transportCoefficient matrix * Chordal.Basic.chordalSq left right :=
      Chordal.Transport.chordalSq_act_le_transportCoefficient matrix determinantNonzero
        left right leftRealizes.valid rightRealizes.valid
    _ ≤ Chordal.Transport.transportCoefficient matrix *
        (1 / 2 : Fraction.Rational) ^ blocks.length :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Cylinder.Safe.Realizes.chordalSq_le_half_pow
          leftRealizes rightRealizes)
        (Chordal.Transport.transportCoefficient_pos matrix determinantNonzero).le
end Purelib.Data.CCL.Encoding.Cylinder.Safe.Transport

end
