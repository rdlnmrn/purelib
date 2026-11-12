module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact endpoint expansions on the original radial chart

The prescribed original base and normalized-ordinate endpoints supply their
own quadratic certificates on the same embedded chart increment. Their
original velocities and finite remainder bounds construct the certificates;
no primitive endpoint is defined from an integral or derivative sample.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent

open Purelib
open Purelib.Calculus.Jet
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle

/-- Construct the base-coordinate expansion on the actual original radial endpoints and oriented velocity.

Positive scale between one and two supplies the original squared-axis bound.
The source and target are the prescribed original conic base coordinates,
and their quantified finite tangent remainder pays the displayed factor.
-/
def baseExpansion (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) : Quadratic.Basic.Certificate (Stereographic.Tangent.increment delta) :=
  { base := (point site parameter scale (Waist.direction quarter time) positive).base
    slope := baseVelocity site parameter scale quarter time
    output := (point site parameter scale (Waist.direction quarter (time + delta)) positive).base
    remainder := (point site parameter scale (Waist.direction quarter (time + delta)) positive).base -
      (point site parameter scale (Waist.direction quarter time) positive).base -
      Stereographic.Tangent.increment delta * baseVelocity site parameter scale quarter time
    expansion := rfl
    factor := (25 / 4) * Norm.Basic.normSq (halfGap site parameter)
    factor_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 25 / 4 by decide +kernel) (Norm.Basic.normSq_nonneg (halfGap site parameter))
    remainder_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical (Stereographic.Tangent.increment delta),
        Stereographic.Tangent.increment_fourth]
      have bound := base_remainder_normSq_le site parameter scale quarter positive lower upper time delta
      rewrite [Norm.Basic.normSq_eq_canonical] at bound
      exact bound }

/-- Construct the ordinate expansion on the same original radial endpoints and normalized-ordinate velocity.

The prescribed normalized ordinates retain the original half-gap, scale and
oriented quarter. The independently proved finite ordinate remainder supplies
its fourth-power chart bound, including a zero chart increment.
-/
def ordinateExpansion (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) : Quadratic.Basic.Certificate (Stereographic.Tangent.increment delta) :=
  { base := (point site parameter scale (Waist.direction quarter time) positive).ordinate
    slope := ordinateVelocity site parameter scale quarter time
    output := (point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate
    remainder := (point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate -
      (point site parameter scale (Waist.direction quarter time) positive).ordinate -
      Stereographic.Tangent.increment delta * ordinateVelocity site parameter scale quarter time
    expansion := rfl
    factor := (25 / 4) * Norm.Basic.normSq (halfGap site parameter)
    factor_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 25 / 4 by decide +kernel) (Norm.Basic.normSq_nonneg (halfGap site parameter))
    remainder_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical (Stereographic.Tangent.increment delta),
        Stereographic.Tangent.increment_fourth]
      have bound := ordinate_remainder_normSq_le site parameter scale quarter positive lower upper time delta
      rewrite [Norm.Basic.normSq_eq_canonical] at bound
      exact bound }

/-- Read the prescribed original source base coordinate from its actual constructed expansion. -/
theorem baseExpansion_base (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (baseExpansion site parameter scale quarter positive lower upper time delta).base =
      (point site parameter scale (Waist.direction quarter time) positive).base := by
  unfold baseExpansion
  rfl

/-- Read the prescribed original target base coordinate from the same retained expansion. -/
theorem baseExpansion_output (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (baseExpansion site parameter scale quarter positive lower upper time delta).output =
      (point site parameter scale (Waist.direction quarter (time + delta)) positive).base := by
  unfold baseExpansion
  rfl

/-- Read the prescribed original source normalized ordinate from its actual constructed expansion. -/
theorem ordinateExpansion_base (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (ordinateExpansion site parameter scale quarter positive lower upper time delta).base =
      (point site parameter scale (Waist.direction quarter time) positive).ordinate := by
  unfold ordinateExpansion
  rfl

/-- Read the prescribed original target normalized ordinate from the same retained expansion. -/
theorem ordinateExpansion_output (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (ordinateExpansion site parameter scale quarter positive lower upper time delta).output =
      (point site parameter scale (Waist.direction quarter (time + delta)) positive).ordinate := by
  unfold ordinateExpansion
  rfl

/-- Read the identical original oriented base velocity from its retained endpoint expansion. -/
theorem baseExpansion_slope (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (baseExpansion site parameter scale quarter positive lower upper time delta).slope =
      baseVelocity site parameter scale quarter time := by
  unfold baseExpansion
  rfl

/-- The original base expansion retains its computed half-gap remainder factor. -/
theorem baseExpansion_factor (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (baseExpansion site parameter scale quarter positive lower upper time delta).factor =
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold baseExpansion
  rfl

/-- Read the original normalized-ordinate velocity from that same prescribed endpoint expansion. -/
theorem ordinateExpansion_slope (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (ordinateExpansion site parameter scale quarter positive lower upper time delta).slope =
      ordinateVelocity site parameter scale quarter time := by
  unfold ordinateExpansion
  rfl

/-- The original ordinate expansion retains the same computed half-gap remainder factor. -/
theorem ordinateExpansion_factor (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (quarter : UnitCircuitQuarter) (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (time delta : Fraction.Rational) :
    (ordinateExpansion site parameter scale quarter positive lower upper time delta).factor =
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
  unfold ordinateExpansion
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent

end
