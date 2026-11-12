module
import Purelib.Integration.Polynomial.Rational.Continuous

/-! Integration requests built from actual finite rational coefficient lists. -/

namespace TestPurelib.Integration.Polynomial.Rational.Continuous

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Rational
open Purelib.Polynomial.Dense.Rational

/-- The original descending coefficients of the identity polynomial. -/
private def identity : Basic.CoordinatePolynomial := ⟨[1, 0]⟩

/-- The original constant polynomial. -/
private def constant : Basic.CoordinatePolynomial := ⟨[3]⟩

/-- A finite accuracy request for the original nonconstant polynomial. -/
private def coarse : AccuracyRequest := ⟨20, by decide⟩

/-- A finite accuracy request for the original constant polynomial. -/
private def constantRequest : AccuracyRequest := ⟨4, by decide⟩

/-- The persistent original bound process for the same finite coefficient list. -/
private def polynomialProcess : BoundProcess := Continuous.boundProcess identity

/-- One saved request to the polynomial's original bound process. -/
private def saved : polynomialProcess.State := polynomialProcess.request polynomialProcess.initial 2 (by decide)

/-- The original finite Horner fold computes the expected positive slope factor. -/
example : Bounds.Uniform.slopeFactor identity = 5 := by decide +kernel

/-- The actual polynomial evaluator and computed mesh produce two retained cells. -/
example : (Continuous.integrate identity coarse).frontier.cells.length = 2 := by decide +kernel

/-- The nonconstant source's actual left-tagged sum and chosen midpoint are both one quarter. -/
example : (Continuous.integrate identity coarse).frontier.taggedSum = (1 / 4 : Fraction.Rational) ∧
    (Continuous.integrate identity coarse).answer = (1 / 4 : Fraction.Rational) := by decide +kernel

/-- A constant coefficient list gives its original exact value as the finite midpoint answer. -/
example : (Continuous.integrate constant constantRequest).answer = 3 := by decide +kernel

/-- Two requests to the same finite polynomial have the proved independent-construction bound. -/
example : Fraction.abs ((Continuous.integrate identity coarse).answer -
    (Continuous.integrate identity constantRequest).answer) < coarse.tolerance + constantRequest.tolerance :=
  Continuous.answer_difference_lt identity coarse constantRequest

/-- Continuing the actual saved polynomial state refines its prior bound and meets the new request. -/
example : (polynomialProcess.bound (polynomialProcess.request saved 1 (by decide))).Refines
      (polynomialProcess.bound saved) ∧
    (polynomialProcess.bound (polynomialProcess.request saved 1 (by decide))).width < 1 :=
  ⟨polynomialProcess.request_refines saved 1 (by decide), polynomialProcess.accurate saved 1 (by decide)⟩

end TestPurelib.Integration.Polynomial.Rational.Continuous
