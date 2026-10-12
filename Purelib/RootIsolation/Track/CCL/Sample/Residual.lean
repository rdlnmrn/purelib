module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.CCL.Sample.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.Track.CCL.Sample.Basic
namespace Request

/-- A CCL request's displayed rational sample has residual of the same
coefficient-linear order as the squared diagonal of its winding-one box. -/
theorem sampleResidual
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {track : Track.Basic.WindingOneTrack p ambient}
    {current : State.WindingOne.Basic.WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    (degreePositive : 0 < p.natDegree) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval result.sample.point) ≤
      Dense.Gaussian.Bounds.Box.residualConstant p ambient * result.next.box.diagonalSq := by
  let bound :=
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound
      p ambient result.next.box
  have anchorResidual :
      Data.Gaussian.Norm.Basic.normSq
          (p.eval result.next.box.anchor) ≤ bound :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      p degreePositive result.next.refinesAmbient result.next.proper
        result.next.raw.rawWinding_ne
  have variation :
      Data.Gaussian.Norm.Basic.normSq
          (p.eval result.sample.point - p.eval result.next.box.anchor) ≤
        bound :=
    Dense.Gaussian.Bounds.Box.Residual.normSq_eval_sub_anchor_le
      p result.next.refinesAmbient result.sample.inside
  have decomposition :
      (p.eval result.sample.point - p.eval result.next.box.anchor) +
          p.eval result.next.box.anchor = p.eval result.sample.point := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im] <;>
      ring1
  calc
    Data.Gaussian.Norm.Basic.normSq
        (p.eval result.sample.point) =
        Data.Gaussian.Norm.Basic.normSq
          ((p.eval result.sample.point - p.eval result.next.box.anchor) +
            p.eval result.next.box.anchor) := by rw [decomposition]
    _ ≤ 2 *
        (Data.Gaussian.Norm.Basic.normSq
            (p.eval result.sample.point - p.eval result.next.box.anchor) +
          Data.Gaussian.Norm.Basic.normSq
            (p.eval result.next.box.anchor)) :=
      Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (bound + bound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = Dense.Gaussian.Bounds.Box.residualConstant p ambient * result.next.box.diagonalSq := by
      simp only [bound,
        Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound,
        Dense.Gaussian.Bounds.Box.residualConstant]
      ring1

/-- The residual certificate also meets the requested squared accuracy after
scaling by the fixed coefficient-computable constant. -/
theorem sampleResidual_le_requested
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {track : Track.Basic.WindingOneTrack p ambient}
    {current : State.WindingOne.Basic.WindingOneState p ambient}
    {epsilon : Fraction.Rational} {positive : 0 < epsilon}
    (result : Track.CCL.Sample.Basic.Request track current epsilon positive)
    (degreePositive : 0 < p.natDegree) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval result.sample.point) ≤
      Dense.Gaussian.Bounds.Box.residualConstant p ambient * epsilon ^ 2 :=
  (result.sampleResidual degreePositive).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      result.accurate (Dense.Gaussian.Bounds.Box.residualConstant_nonneg p ambient))
end Request
end Purelib.RootIsolation.Track.CCL.Sample.Basic

end
