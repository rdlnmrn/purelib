module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
public import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Winding.Edge.Reparameterization
import Purelib.Polynomial.Winding.Polygon.Stationary
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring

/-!
# Affine segments retain their finite winding under subdivision

The normalized coordinate coefficient lists identify an affine subsegment
with the corresponding affine substitution of the original line.  Cauchy
index reparameterization then relates its unit interval to the original
parameter interval, including reversed and stationary clear subsegments.
-/

namespace Purelib.Polynomial.Winding.Polygon.Subdivision

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

public section

/-- Replacing a clear affine segment's original parameter interval by the unit interval preserves its finite winding.

A nonstationary displacement gives an invertible affine parameter change. The
stationary case uses the supplied starting-point nonzero certificate directly. -/
theorem segmentRaw_eq_ofLine (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (origin
  direction :
  Gaussian.Basic.Canonical)
    (left right : Fraction.Rational) (nonzero : polynomial.eval (Affine.line origin direction left) ≠ 0) :
    (Dense.Gaussian.Path.Segment.segment polynomial (Affine.line origin direction left) (Affine.line origin direction
      right)).doubledWinding =
      (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine polynomial origin direction left right).doubledWinding := by
  by_cases same : right = left
  · subst right
    rw [Winding.Polygon.Stationary.segment_self_doubledWinding polynomial _ nonzero]
    exact (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  · have slopeNonzero : right - left ≠ 0 := by
      intro vanishes
      have recovered : (right - left) + left = right := by ring1
      rewrite [vanishes, Fraction.Field.zero_add] at recovered
      exact same recovered.symm
    have directionEq : Affine.line origin direction right - Affine.line origin direction left =
        Gaussian.Cast.Path.ofCoordinate (right - left) * direction := by
      apply Gaussian.Basic.ext <;>
        simp only [Affine.line, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im, Gaussian.Basic.add_re,
          Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    rw [Dense.Gaussian.Path.Segment.segment, directionEq, Winding.Edge.Reparameterization.ofLine_doubledWinding_affine
      polynomial origin direction left (right - left) 0 1 slopeNonzero]
    rw [show left + (right - left) * 0 = left from by ring1,
      show left + (right - left) * 1 = right from by ring1]

end

end Purelib.Polynomial.Winding.Polygon.Subdivision
