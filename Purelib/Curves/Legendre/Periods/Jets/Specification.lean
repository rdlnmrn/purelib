module
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Curves.Legendre.PicardFuchs.Polynomials
import Purelib.Polynomial.Dense.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Data.Gaussian.Cast

open Purelib.Polynomial

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Specification

/-- The value-channel integrand `x^k/y`, for `k=0,1`. -/
def valueSpecification (coordinate : Fin 2) :
  OddPower.Basic.OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := Dense.Gaussian.Basic.constantOnePolynomial
      denominatorPairs := 0
      scale := 1 }
  else
    { numerator := Dense.Gaussian.Basic.coordinatePolynomial
      denominatorPairs := 0
      scale := 1 }

/-- The first parameter derivative `x^k g(x)/(2 y^3)`. -/
def firstDerivativeSpecification (coordinate : Fin 2) :
    OddPower.Basic.OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := Polynomials.basePolynomial
      denominatorPairs := 1
      scale := LegendrePeriodJets.realGaussian (1 / 2) }
  else
    { numerator := Polynomials.weightedBasePolynomial
      denominatorPairs := 1
      scale := LegendrePeriodJets.realGaussian (1 / 2) }

/-- The second parameter derivative `3 x^k g(x)^2/(4 y^5)`. -/
def secondDerivativeSpecification (coordinate : Fin 2) :
    OddPower.Basic.OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := Polynomials.squaredBasePolynomial
      denominatorPairs := 2
      scale := LegendrePeriodJets.realGaussian (3 / 4) }
  else
    { numerator := Polynomials.weightedSquaredBasePolynomial
      denominatorPairs := 2
      scale := LegendrePeriodJets.realGaussian (3 / 4) }

/-- The first value channel is the unit numerator over the original sheet value. -/
@[simp] theorem valueSpecification_zero :
    valueSpecification 0 =
      { numerator := Dense.Gaussian.Basic.constantOnePolynomial
        denominatorPairs := 0
        scale := 1 } := rfl

/-- The second value channel is the coordinate numerator over the original sheet value. -/
@[simp] theorem valueSpecification_one :
    valueSpecification 1 =
      { numerator := Dense.Gaussian.Basic.coordinatePolynomial
        denominatorPairs := 0
        scale := 1 } := by
  unfold valueSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The first derivative channel uses the base quadratic over twice the sheet cube. -/
@[simp] theorem firstDerivativeSpecification_zero :
    firstDerivativeSpecification 0 =
      { numerator := Polynomials.basePolynomial
        denominatorPairs := 1
        scale := LegendrePeriodJets.realGaussian (1 / 2) } := rfl

/-- The weighted first derivative channel uses x times the base quadratic over twice the sheet cube. -/
@[simp] theorem firstDerivativeSpecification_one :
    firstDerivativeSpecification 1 =
      { numerator := Polynomials.weightedBasePolynomial
        denominatorPairs := 1
        scale := LegendrePeriodJets.realGaussian (1 / 2) } := by
  unfold firstDerivativeSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The second derivative channel uses three quarters of the squared base quadratic over the sheet fifth power. -/
@[simp] theorem secondDerivativeSpecification_zero :
    secondDerivativeSpecification 0 =
      { numerator := Polynomials.squaredBasePolynomial
        denominatorPairs := 2
        scale := LegendrePeriodJets.realGaussian (3 / 4) } := rfl

/-- The weighted second derivative channel includes the original coordinate factor over the sheet fifth power. -/
@[simp] theorem secondDerivativeSpecification_one :
    secondDerivativeSpecification 1 =
      { numerator := Polynomials.weightedSquaredBasePolynomial
        denominatorPairs := 2
        scale := LegendrePeriodJets.realGaussian (3 / 4) } := by
  unfold secondDerivativeSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

end Purelib.Curves.Legendre.Periods.Jets.Specification

end
