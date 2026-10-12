module
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Grid.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Rounding.Nearest

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Field

/-!
# Gaussian grid fractions

The two nearest integral coordinates share the original positive natural denominator.
The retained fraction has exact coordinate readbacks and denominator-squared height.
-/

public section

namespace Purelib.Approximation.Gaussian.Grid.Basic

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical.Fraction
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding

/-- The square-grid Gaussian fraction obtained by nearest rounding in both coordinates. -/
@[expose] def gridFraction (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
  Fraction.NaturalDenominator :=
  let denominator := Grid.Basic.gridDenominator radius
  NaturalDenominator.grid
    (Nearest.nearestCoordinate
      (Fraction.Arithmetic.normalizedMul
        (denominator : Fraction.Rational) center.re))
    (Nearest.nearestCoordinate
      (Fraction.Arithmetic.normalizedMul
        (denominator : Fraction.Rational) center.im))
    denominator (Grid.Basic.gridDenominator_pos radius)

/-- The nearest square-grid Gaussian fraction has height equal to its grid denominator
squared. -/
@[simp] theorem gridFraction_height (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    (gridFraction center radius).height = Grid.Basic.gridDenominator radius ^ 2 := rfl

/-- The grid fraction's real value is the real coordinate rounded on the original
denominator grid. -/
@[simp] theorem gridFraction_value_re (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    (gridFraction center radius).value.re =
      Grid.Basic.gridCoordinate center.re (Grid.Basic.gridDenominator radius) := by
  simp only [gridFraction, Grid.Basic.gridCoordinate,
    Fraction.Arithmetic.normalizedDiv_eq,
    Fraction.Arithmetic.normalizedMul_eq]
  rfl

/-- The grid fraction's imaginary value is the imaginary coordinate rounded on the original
denominator grid. -/
@[simp] theorem gridFraction_value_im (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) :
    (gridFraction center radius).value.im =
      Grid.Basic.gridCoordinate center.im (Grid.Basic.gridDenominator radius) := by
  simp only [gridFraction, Grid.Basic.gridCoordinate,
    Fraction.Arithmetic.normalizedDiv_eq,
    Fraction.Arithmetic.normalizedMul_eq]
  rfl

end Purelib.Approximation.Gaussian.Grid.Basic
