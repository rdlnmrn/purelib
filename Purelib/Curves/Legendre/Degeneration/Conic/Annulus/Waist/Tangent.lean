module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Original cubic waist tangents with finite remainders

The original quarter multiplier and labelled half-gap determine the displayed
cubic base velocity. Exact finite differences retain a quantified quadratic
remainder. Its factorization through the normalized ordinate identifies the
differential pullback without division by a branch-point ordinate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Tangent

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle.Stereographic

/-- The exact velocity of the original rotated rational direction chart. -/
@[expose] def directionVelocity (quarter : UnitCircuitQuarter) (time : Fraction.Rational) : Canonical :=
  Quarter.unitCircuitMultiplier quarter * Stereographic.Tangent.velocity time

/-- The exact original cubic base velocity, with the same labelled half-gap and quarter orientation. -/
@[expose] def baseVelocity (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : Canonical :=
  halfGap site parameter * Components.Projection.realPart (directionVelocity quarter time)

/-- The rotated direction velocity factors through the same original direction and logarithmic velocity. -/
theorem directionVelocity_eq (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    directionVelocity quarter time =
      (direction quarter time).value * Stereographic.Tangent.logarithmicVelocity time := by
  unfold directionVelocity
  rewrite [Stereographic.Tangent.velocity_eq_point_mul, direction_value]
  ring1

/-- The original cubic base velocity equals the normalized ordinate times its exact chart logarithmic velocity.

This scalar identity remains valid at both zero-ordinate branch points.
It determines the branch-safe pullback of the original `dx/y` differential.
-/
theorem baseVelocity_eq_ordinate_mul (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (time : Fraction.Rational) :
    baseVelocity site parameter quarter time = (point site parameter (direction quarter time) regular bound).ordinate *
      Stereographic.Tangent.logarithmicVelocity time := by
  unfold baseVelocity
  rewrite [directionVelocity_eq, Components.Projection.realPart_mul_imaginary _ _
    (Stereographic.Tangent.logarithmicVelocity_real time), point_ordinate]
  ring1

/-- Rotation retains the same finite squared tangent-remainder bound for the original quarter direction. -/
theorem direction_remainder_normSq_le (quarter : UnitCircuitQuarter) (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((direction quarter (time + delta)).value - (direction quarter time).value -
      Stereographic.Tangent.increment delta * directionVelocity quarter time) ≤ 4 * delta ^ 4 := by
  have difference : (direction quarter (time + delta)).value - (direction quarter time).value -
      Stereographic.Tangent.increment delta * directionVelocity quarter time =
      Quarter.unitCircuitMultiplier quarter * (unitQuarterPoint (time + delta) - unitQuarterPoint time -
        Stereographic.Tangent.increment delta * Stereographic.Tangent.velocity time) := by
    rewrite [direction_value, direction_value]
    unfold directionVelocity
    ring1
  rewrite [difference, Norm.Basic.normSq_mul, Quarter.unitCircuitMultiplier_unit, Fraction.Field.one_mul]
  exact Stereographic.Tangent.remainder_normSq_le _ _

/-- Every finite increment of the original cubic base chart has its quantified quadratic tangent remainder. -/
theorem base_remainder_normSq_le (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (time delta : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter (direction quarter (time + delta)) regular bound).base -
      (point site parameter (direction quarter time) regular bound).base -
      Stereographic.Tangent.increment delta * baseVelocity site parameter quarter time) ≤
        4 * Norm.Basic.normSq (halfGap site parameter) * delta ^ 4 := by
  let remainder := (direction quarter (time + delta)).value - (direction quarter time).value -
    Stereographic.Tangent.increment delta * directionVelocity quarter time
  have realScalar : Components.Projection.realPart
      (Stereographic.Tangent.increment delta * directionVelocity quarter time) =
      Stereographic.Tangent.increment delta * Components.Projection.realPart (directionVelocity quarter time) := by
    rewrite [Basic.mul_comm (Stereographic.Tangent.increment delta) (directionVelocity quarter time),
      Components.Projection.realPart_mul_real _ _ (by rfl)]
    exact Basic.mul_comm _ _
  have difference : (point site parameter (direction quarter (time + delta)) regular bound).base -
      (point site parameter (direction quarter time) regular bound).base -
      Stereographic.Tangent.increment delta * baseVelocity site parameter quarter time =
        halfGap site parameter * Components.Projection.realPart remainder := by
    unfold remainder baseVelocity
    rewrite [point_base, point_base, Components.Projection.realPart_sub, Components.Projection.realPart_sub, realScalar]
    ring1
  calc
    _ = Norm.Basic.normSq (halfGap site parameter) * Norm.Basic.normSq (Components.Projection.realPart remainder) := by
      rewrite [difference, Norm.Basic.normSq_mul]
      rfl
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * Norm.Basic.normSq remainder :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Components.Projection.normSq_realPart_le _)
        (Norm.Basic.normSq_nonneg _)
    _ ≤ Norm.Basic.normSq (halfGap site parameter) * (4 * delta ^ 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (direction_remainder_normSq_le _ _ _)
        (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Tangent
