module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Geometry.Rational.Box.Interval
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Map.Gaussian

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Cast

open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.Taylor

/-- The existing finite Gaussian Horner scan, restricted to the real axis,
is an executable quadratic Taylor majorant for a coordinate polynomial. -/
def taylorRemainderBound
    (p : CoordinatePolynomial) (interval : Interval.Bounds) :
      Fraction.Rational :=
  Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound
    (Map.Gaussian.gaussianPolynomial p) (Box.Interval.intervalBox interval)

/-- The finite rational Taylor remainder bound is strictly positive. -/
theorem taylorRemainderBound_pos
    (p : CoordinatePolynomial) (interval : Interval.Bounds) :
    0 < taylorRemainderBound p interval :=
  Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos
    (Map.Gaussian.gaussianPolynomial p) (Box.Interval.intervalBox interval)

/-- Coordinate form of the coefficient-scanned quadratic Taylor estimate. -/
theorem taylor_error_sq_le
    (p : CoordinatePolynomial) {interval : Interval.Bounds}
    {point center : Fraction.Rational}
    (pointInside : interval.Contains point)
    (centerInside : interval.Contains center) :
    (p.eval point - p.eval center -
        (Derivative.derivative p).eval center *
          (point - center)) ^ 2 ≤
      taylorRemainderBound p interval * (point - center) ^ 4 := open Purelib.Data in by
  have gaussianBound :=
    Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
        (Map.Gaussian.gaussianPolynomial p)
        (Box.Interval.ofCoordinate_mem_intervalBox pointInside)
        (Box.Interval.ofCoordinate_mem_intervalBox centerInside)
  let error := p.eval point - p.eval center -
    (Derivative.derivative p).eval center * (point - center)
  have errorIdentity :
      (Map.Gaussian.gaussianPolynomial p).eval (CoordinateTaylor.ofCoordinate point) -
          (Map.Gaussian.gaussianPolynomial p).eval (CoordinateTaylor.ofCoordinate center) -
          (Gaussian.GCD.derivative (Map.Gaussian.gaussianPolynomial p)).eval
              (CoordinateTaylor.ofCoordinate center) *
            (CoordinateTaylor.ofCoordinate point - CoordinateTaylor.ofCoordinate center) =
        CoordinateTaylor.ofCoordinate error := by
    rw [Map.Gaussian.eval_gaussianPolynomial, Map.Gaussian.eval_gaussianPolynomial]
    change CoordinateTaylor.ofCoordinate (p.eval point) - CoordinateTaylor.ofCoordinate
      (p.eval center) -
        (Derivative.derivative (Map.Gaussian.gaussianPolynomial p)).eval
            (CoordinateTaylor.ofCoordinate center) *
          (CoordinateTaylor.ofCoordinate point - CoordinateTaylor.ofCoordinate center) =
            CoordinateTaylor.ofCoordinate error
    rw [← Gaussian.Cast.ofCoordinate_sub (p.eval point) (p.eval center),
      Map.Gaussian.eval_derivative_gaussianPolynomial,
      ← Gaussian.Cast.ofCoordinate_sub point center, ← Gaussian.Cast.ofCoordinate_mul,
      ← Gaussian.Cast.ofCoordinate_sub]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at gaussianBound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical, errorIdentity, Gaussian.Cast.ofCoordinate_normSq, ←
    Gaussian.Cast.ofCoordinate_sub,
    Gaussian.Cast.ofCoordinate_normSq] at gaussianBound
  change error ^ 2 ≤
    taylorRemainderBound p interval * ((point - center) ^ 2) ^ 2
      at gaussianBound
  simpa only [error] using (calc
    error ^ 2 ≤
        taylorRemainderBound p interval * ((point - center) ^ 2) ^ 2 :=
      gaussianBound
    _ = taylorRemainderBound p interval * (point - center) ^ 4 := by
      ring1)
end Purelib.Polynomial.Dense.Rational.Bounds.Taylor

end
