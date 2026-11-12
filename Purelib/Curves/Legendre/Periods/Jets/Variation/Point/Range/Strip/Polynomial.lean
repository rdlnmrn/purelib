module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
public import Purelib.Polynomial.Dense.Bivariate.Specialization.Affine
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Tactic.Ring
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # The actual finite bivariate polynomial of one retained Legendre strip

The original zero and shifted cubic restrictions are the two coefficient
tables of an affine outer Horner polynomial. The inner coordinate is the
SAME original oriented segment fraction. No polynomial in t+i*s, root
interpolation, Frame equality or replacement source is introduced.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib.Polynomial.Dense.Gaussian
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Bivariate.Basic (GaussianBivariate)

variable {parameter : Canonical} {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish) (increment : Canonical)

/-- The original clear segment point is its SAME exact affine physical coordinate. -/
private theorem segment_affine (fraction : Rational) :
    Affine.line start (finish - start) fraction = segment.pointAt fraction := by
  apply Basic.ext <;>
    simp only [Affine.line, ClearSegment.pointAt, Scale.scale_re, Scale.scale_im, Cast.Path.ofCoordinate,
      Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1

/-- The actual two-variable table with original zero/shifted composed cubic coefficient owners. -/
def radicandPolynomial (_segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (increment : Canonical) : GaussianBivariate :=
  let first := Substitution.Affine.composeLine (Paths.polynomial parameter) start (finish - start)
  let last := Substitution.Affine.composeLine (Paths.polynomial (parameter + increment))
    start (finish - start)
  ⟨[last - first, first]⟩

/-- Its two exact real arguments read the original Legendre radicand on the SAME parent at every parameter pair. -/
theorem radicandPolynomial_eval (time fraction : Rational) :
    Bivariate.Basic.eval (radicandPolynomial segment increment)
        (Cast.Path.ofCoordinate time) (Cast.Path.ofCoordinate fraction) =
      (Paths.polynomial (parameter + Cast.Path.ofCoordinate time * increment)).eval (segment.pointAt fraction) := by
  let first := Substitution.Affine.composeLine (Paths.polynomial parameter) start (finish - start)
  let last := Substitution.Affine.composeLine (Paths.polynomial (parameter + increment))
    start (finish - start)
  have firstEval := (Substitution.Affine.eval_composeLine
    (Paths.polynomial parameter) start (finish - start) fraction).trans
      (congrArg (Paths.polynomial parameter).eval (segment_affine segment fraction))
  have lastEval := (Substitution.Affine.eval_composeLine
    (Paths.polynomial (parameter + increment)) start (finish - start) fraction).trans
      (congrArg (Paths.polynomial (parameter + increment)).eval (segment_affine segment fraction))
  have complement : (⟨1 - time, 0⟩ : Canonical) = 1 - Cast.Path.ofCoordinate time := by
    apply Basic.ext <;> simp only [Cast.Path.ofCoordinate, Basic.sub_re, Basic.sub_im,
      Basic.one_re, Basic.one_im, -eq_self, -iff_self] <;> ring1
  have original := interpolated_eval_affine parameter increment (segment.pointAt fraction) time
  rewrite [complement] at original
  change (0 * Cast.Path.ofCoordinate time + (last - first).eval (Cast.Path.ofCoordinate fraction)) *
    Cast.Path.ofCoordinate time + first.eval (Cast.Path.ofCoordinate fraction) = _
  rewrite [eval_sub, firstEval, lastEval]
  calc
    _ = (1 - Cast.Path.ofCoordinate time) *
          (Paths.polynomial parameter).eval (segment.pointAt fraction) +
        Cast.Path.ofCoordinate time *
          (Paths.polynomial (parameter + increment)).eval (segment.pointAt fraction) := by ring1
    _ = _ := original.symm

/-- Restrict the SAME actual table along any two actual affine rational coordinate maps. -/
def radicandLine (time fraction timeDirection fractionDirection : Rational) :
    Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Bivariate.Specialization.Affine.composeLine (radicandPolynomial segment increment)
    (Cast.Path.ofCoordinate time) (Cast.Path.ofCoordinate timeDirection)
    (Cast.Path.ofCoordinate fraction) (Cast.Path.ofCoordinate fractionDirection)

/-- Its exact restriction reads the original two-parameter map rather than a fixed-fibre proxy. -/
theorem radicandLine_eval (time fraction timeDirection fractionDirection input : Rational) :
    (radicandLine segment increment time fraction timeDirection fractionDirection).eval
        (Cast.Path.ofCoordinate input) =
      (Paths.polynomial (parameter + Cast.Path.ofCoordinate (time + input * timeDirection) * increment)).eval
        (segment.pointAt (fraction + input * fractionDirection)) := by
  have outer : Cast.Path.ofCoordinate time + Cast.Path.ofCoordinate input * Cast.Path.ofCoordinate timeDirection =
      Cast.Path.ofCoordinate (time + input * timeDirection) := by
    apply Basic.ext <;> simp only [Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im,
      Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1
  have inner : Cast.Path.ofCoordinate fraction +
      Cast.Path.ofCoordinate input * Cast.Path.ofCoordinate fractionDirection =
      Cast.Path.ofCoordinate (fraction + input * fractionDirection) := by
    apply Basic.ext <;> simp only [Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im,
      Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1
  exact ((Bivariate.Specialization.Affine.eval_composeLine (radicandPolynomial segment increment)
    _ _ _ _ (Cast.Path.ofCoordinate input)).trans
      (congrArg₂ (Bivariate.Basic.eval (radicandPolynomial segment increment)) outer inner)).trans
        (radicandPolynomial_eval segment increment _ _)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
