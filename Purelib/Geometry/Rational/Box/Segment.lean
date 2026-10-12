module
import Purelib.Data.Rat.Interval.ConvexCombination
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational

section
@[expose] public section

/-! Finite affine segments between two points of a rational rectangle. -/

namespace Purelib.Geometry.Rational.Box

/-- Every affine segment point with parameter between zero and one stays inside a box containing both endpoints. -/
theorem contains_line {box : Rational.Box} {start
  finish : Data.Gaussian.Basic.Canonical}
    (startInside : box.Contains start) (finishInside : box.Contains finish)
    {parameter : Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    box.Contains (Affine.line start (finish - start) parameter) := by
  have horizontal := Rational.Box.coordinate_between ⟨startInside.1, startInside.2.1⟩
    ⟨finishInside.1, finishInside.2.1⟩ inside
  have vertical := Rational.Box.coordinate_between startInside.2.2 finishInside.2.2 inside
  have realEq : (Affine.line start (finish - start) parameter).re =
      start.re + parameter * (finish.re - start.re) := by
    simp only [Affine.line, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.sub_re,
      Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    ring1
  have imagEq : (Affine.line start (finish - start) parameter).im =
      start.im + parameter * (finish.im - start.im) := by
    simp only [Affine.line, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.sub_re,
      Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    ring1
  unfold Box.Contains
  rw [realEq, imagEq]
  exact ⟨horizontal.1, horizontal.2, vertical.1, vertical.2⟩

end Purelib.Geometry.Rational.Box

end
