module

public import Purelib.RootIsolation.Multiplicity.Circle.Argument
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Fixed reading bounds of original circle observations

The exact branch computes its original root quadrance once. The higher
branch reads the original radius and collar. Their cached radius and radial
endpoints can be consumed by every formal factor stage before any new model
observations or finite mode horizons are selected.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Clearance.Circle (Certificate)

namespace Bounds

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}

/-- The fixed sample ceiling uses the exact original point or the same original higher ambient box. -/
@[expose] def radiusValue : (observation : FactorObservation input context) →
    (locations : Locations clearance observation) → ObservationArgument observation locations → Rational
  | .exact root _ _, _, _ => 1 + Norm.Basic.normSq root.point
  | .higher _ _, _, argument => argument.request.radius

/-- The original inside endpoint uses an exact root quadrance or half the same positive collar. -/
@[expose] def ceilingValue : (observation : FactorObservation input context) →
    (locations : Locations clearance observation) → ObservationArgument observation locations → Rational
  | .exact root _ _, _, _ => Norm.Basic.normSq root.point
  | .higher _ _, locations, _ => max 0 (1 - locations.request.collar.width / 2)

/-- The original outside endpoint uses an exact root quadrance or half the same positive collar. -/
@[expose] def floorValue : (observation : FactorObservation input context) →
    (locations : Locations clearance observation) → ObservationArgument observation locations → Rational
  | .exact root _ _, _, _ => Norm.Basic.normSq root.point
  | .higher _ _, locations, _ => 1 + locations.request.collar.width / 2

end Bounds

set_option genInjectivity false in
/-- Source-fixed cached bounds for the same original observation, locations and argument.

Exact-point quadrance is shared by the radius and both radial endpoints.
Higher endpoints consume the same original collar and argument radius.
The defining equations identify the original source values independently
of any formal root reading or requested final model error.
-/
structure Bounds {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}
    (observation : FactorObservation input context) (locations : Locations clearance observation)
    (argument : ObservationArgument observation locations) where
  /-- The once-materialized fixed sample norm ceiling. -/
  radius : Rational
  /-- The ceiling uses the same original exact point or higher ambient bound. -/
  radius_eq : radius = Bounds.radiusValue observation locations argument
  /-- The retained endpoint for each originally inside root. -/
  ceiling : Rational
  /-- The endpoint uses the same original point or collar. -/
  ceiling_eq : ceiling = Bounds.ceilingValue observation locations argument
  /-- The retained endpoint for each originally outside root. -/
  floor : Rational
  /-- The endpoint uses the same original point or collar. -/
  floor_eq : floor = Bounds.floorValue observation locations argument

constructive_injectivity Bounds

namespace Bounds

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {context : PositiveContext input.entries} {clearance : Certificate context.focus.part.polynomial}

/-- Prepare the original physical bounds once, before constructing any formal-model observation. -/
@[expose] def prepare : (observation : FactorObservation input context) →
    (locations : Locations clearance observation) → (argument : ObservationArgument observation locations) →
    Bounds observation locations argument
  | .exact root _ _, _, _ =>
      let pointNorm := Norm.Basic.normSq root.point
      { radius := 1 + pointNorm, radius_eq := rfl
        ceiling := pointNorm, ceiling_eq := rfl, floor := pointNorm, floor_eq := rfl }
  | .higher _ _, locations, argument =>
      let halfWidth := locations.request.collar.width / 2
      { radius := argument.request.radius, radius_eq := rfl
        ceiling := max 0 (1 - halfWidth), ceiling_eq := rfl, floor := 1 + halfWidth, floor_eq := rfl }

variable {observation : FactorObservation input context} {locations : Locations clearance observation}
variable {argument : ObservationArgument observation locations}

/-- The same original fixed sample ceiling is nonnegative. -/
theorem radius_nonnegative (bounds : Bounds observation locations argument) : 0 ≤ bounds.radius := by
  rewrite [bounds.radius_eq]
  cases observation with
  | exact root _ _ =>
      have nonnegative := Fraction.Order.Arithmetic.add_le_add_direct
        (by decide : (0 : Rational) ≤ 1) (Norm.Basic.normSq_nonneg root.point)
      rewrite [zero_add] at nonnegative
      exact nonnegative
  | higher boxes _ =>
      change 0 ≤ argument.request.radius
      rewrite [argument.request.radius_eq]
      exact (Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox _).normSqBound_nonneg

/-- Every same retained inside endpoint is nonnegative. -/
theorem ceiling_nonnegative (bounds : Bounds observation locations argument) : 0 ≤ bounds.ceiling := by
  rewrite [bounds.ceiling_eq]
  cases observation with
  | exact root _ _ => exact Norm.Basic.normSq_nonneg root.point
  | higher _ _ => exact Fraction.Order.Basic.le_max_left _ _

/-- An original inside label puts its cached physical ceiling strictly below unit quadrance. -/
theorem inside_ceiling (bounds : Bounds observation locations argument)
    (index : Fin context.focus.part.polynomial.natDegree)
    (inside : Locations.insideAt observation locations index = true) : bounds.ceiling < 1 := by
  rewrite [bounds.ceiling_eq]
  cases observation with
  | exact root _ _ =>
      cases locations with
      | inside holds =>
          change Norm.Basic.normSq root.point < 1
          rewrite [Norm.Basic.normSq_eq_canonical]
          exact holds
      | outside _ => cases inside
  | higher _ _ =>
      change max 0 (1 - locations.request.collar.width / 2) < 1
      have halfPositive := Fraction.Order.Field.div_pos_direct locations.request.collar.positive
        (by decide : (0 : Rational) < 2)
      have below := Fraction.Order.Arithmetic.sub_lt_sub_left_direct halfPositive 1
      change 1 - locations.request.collar.width / 2 < (1 : Rational) at below
      exact Fraction.Order.Basic.max_lt (by decide) below

/-- An original outside label puts its cached physical floor strictly beyond unit quadrance. -/
theorem outside_floor (bounds : Bounds observation locations argument)
    (index : Fin context.focus.part.polynomial.natDegree)
    (outside : Locations.insideAt observation locations index = false) : 1 < bounds.floor := by
  rewrite [bounds.floor_eq]
  cases observation with
  | exact root _ _ =>
      cases locations with
      | inside _ => cases outside
      | outside holds =>
          change 1 < Norm.Basic.normSq root.point
          rewrite [Norm.Basic.normSq_eq_canonical]
          exact holds
  | higher _ _ =>
      change 1 < 1 + locations.request.collar.width / 2
      have halfPositive := Fraction.Order.Field.div_pos_direct locations.request.collar.positive
        (by decide : (0 : Rational) < 2)
      have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct halfPositive 1
      rewrite [add_zero] at shifted
      exact shifted

end Bounds

end Purelib.RootIsolation.Multiplicity.Circle.Roots.Reading

end
