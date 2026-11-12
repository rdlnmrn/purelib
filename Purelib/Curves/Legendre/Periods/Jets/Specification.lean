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

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic

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

open Purelib.Curves.Legendre
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The original coordinate-selected numerator of the two value rows. -/
def valueNumerator (coordinate : Fin 2) : CoefficientPolynomial :=
  if coordinate = 0 then Dense.Gaussian.Basic.constantOnePolynomial
  else Dense.Gaussian.Basic.coordinatePolynomial

/-- The original coordinate-selected numerator of the first parameter derivative rows. -/
def firstDerivativeNumerator (coordinate : Fin 2) : CoefficientPolynomial :=
  if coordinate = 0 then Polynomials.basePolynomial
  else Polynomials.weightedBasePolynomial

/-- The original coordinate-selected numerator of the second parameter derivative rows. -/
def secondDerivativeNumerator (coordinate : Fin 2) : CoefficientPolynomial :=
  if coordinate = 0 then Polynomials.squaredBasePolynomial
  else Polynomials.weightedSquaredBasePolynomial

/-- The value-channel integrand `x^k/y`, for `k=0,1`. -/
def valueSpecification (parameter : Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
  OddPowerDifferential (Paths.polynomial parameter) :=
  OddPowerDifferential.ofCoefficients (Paths.polynomial parameter) (valueNumerator coordinate) 0 1

/-- Both original value-channel differentials have exactly one sheet factor in their denominator. -/
theorem valueSpecification_denominatorPairs (parameter : Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
    (valueSpecification parameter coordinate).denominatorPairs = 0 := rfl

/-- The first parameter derivative `x^k g(x)/(2 y^3)`. -/
def firstDerivativeSpecification (parameter : Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
    OddPowerDifferential (Paths.polynomial parameter) :=
  OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
    (firstDerivativeNumerator coordinate) 1 (LegendrePeriodJets.realGaussian (1 / 2))

/-- The second parameter derivative `3 x^k g(x)^2/(4 y^5)`. -/
def secondDerivativeSpecification (parameter : Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
    OddPowerDifferential (Paths.polynomial parameter) :=
  OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
    (secondDerivativeNumerator coordinate) 2 (LegendrePeriodJets.realGaussian (3 / 4))

/-- The first value channel is the unit numerator over the original sheet value. -/
@[simp] theorem valueSpecification_zero (parameter : Data.Gaussian.Basic.Canonical) :
    valueSpecification parameter 0 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Dense.Gaussian.Basic.constantOnePolynomial 0 1 := rfl

/-- The second value channel is the coordinate numerator over the original sheet value. -/
@[simp] theorem valueSpecification_one (parameter : Data.Gaussian.Basic.Canonical) :
    valueSpecification parameter 1 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Dense.Gaussian.Basic.coordinatePolynomial 0 1 := by
  unfold valueSpecification valueNumerator
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The first derivative channel uses the base quadratic over twice the sheet cube. -/
@[simp] theorem firstDerivativeSpecification_zero (parameter : Data.Gaussian.Basic.Canonical) :
    firstDerivativeSpecification parameter 0 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Polynomials.basePolynomial 1 (LegendrePeriodJets.realGaussian (1 / 2)) := rfl

/-- The weighted first derivative channel uses x times the base quadratic over twice the sheet cube. -/
@[simp] theorem firstDerivativeSpecification_one (parameter : Data.Gaussian.Basic.Canonical) :
    firstDerivativeSpecification parameter 1 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Polynomials.weightedBasePolynomial 1 (LegendrePeriodJets.realGaussian (1 / 2)) := by
  unfold firstDerivativeSpecification firstDerivativeNumerator
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The second derivative channel uses three quarters of the squared base quadratic over the sheet fifth power. -/
@[simp] theorem secondDerivativeSpecification_zero (parameter : Data.Gaussian.Basic.Canonical) :
    secondDerivativeSpecification parameter 0 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Polynomials.squaredBasePolynomial 2 (LegendrePeriodJets.realGaussian (3 / 4)) := rfl

/-- The weighted second derivative channel includes the original coordinate factor over the sheet fifth power. -/
@[simp] theorem secondDerivativeSpecification_one (parameter : Data.Gaussian.Basic.Canonical) :
    secondDerivativeSpecification parameter 1 =
      OddPowerDifferential.ofCoefficients (Paths.polynomial parameter)
      Polynomials.weightedSquaredBasePolynomial 2 (LegendrePeriodJets.realGaussian (3 / 4)) := by
  unfold secondDerivativeSpecification secondDerivativeNumerator
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

end Purelib.Curves.Legendre.Periods.Jets.Specification

end
