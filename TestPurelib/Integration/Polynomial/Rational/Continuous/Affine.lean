module
import Purelib.Integration.Polynomial.Rational.Continuous.Affine

/-! Affine transport of an actual finite nonconstant rational polynomial. -/

namespace TestPurelib.Integration.Polynomial.Rational.Continuous.Affine

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial.Rational.Continuous
open Purelib.Polynomial.Dense.Rational

/-- The original descending coefficients of the identity polynomial. -/
private def identity : Basic.CoordinatePolynomial := ⟨[1, 0]⟩

/-- Two rational endpoints in opposite orientations. -/
private def forward : Partition.Interval := ⟨2, 3⟩
private def backward : Partition.Interval := ⟨3, 2⟩

/-- The actual polynomial-derived oriented bound process. -/
private def process : BoundProcess := Affine.boundProcess identity forward

/-- The original finite affine substitution reads the same nonconstant polynomial on both orientations. -/
example : (Affine.substituted identity forward).eval (1 / 2) = (5 / 2 : Fraction.Rational) ∧
    (Affine.substituted identity backward).eval (1 / 2) = (5 / 2 : Fraction.Rational) := by decide +kernel

/-- The original polynomial process handles an actual positive finite request. -/
example : (process.bound (process.request process.initial 8 (by decide))).width < 8 :=
  process.accurate process.initial 8 (by decide)

end TestPurelib.Integration.Polynomial.Rational.Continuous.Affine
