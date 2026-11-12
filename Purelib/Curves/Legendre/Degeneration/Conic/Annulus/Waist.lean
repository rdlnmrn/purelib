module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus
public import Purelib.Geometry.Gaussian.UnitCircle.Basic
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Quadratic.Split
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Tactic.Ring

/-!
# Rational waist circuits in the original Legendre nodal annulus

An original certified unit direction is scaled by the same labelled half-gap.
Four existing rational quarter charts provide a closed circuit of exact conic
points and actual signed cubic channels. A finite parameter-distance bound
derives both annulus admission and original cofactor clearance internally.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.Field
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Quadratic

/-- The original certified unit vertex on one of the four rational quarter charts. -/
def direction (quarter : UnitCircuitQuarter) (parameter : Fraction.Rational) : UnitVertex :=
  { value := Quarter.unitCircuitMultiplier quarter * Stereographic.unitQuarterPoint parameter
    unit := by
      rewrite [Norm.Basic.normSq_mul, Quarter.unitCircuitMultiplier_unit, Stereographic.unitQuarterPoint_unit]
      decide +kernel }

/-- Read the exact original quarter multiplier and stereographic point from the certified direction. -/
theorem direction_value (quarter : UnitCircuitQuarter) (parameter : Fraction.Rational) :
    (direction quarter parameter).value =
      Quarter.unitCircuitMultiplier quarter * Stereographic.unitQuarterPoint parameter := by
  unfold direction
  rfl

/-- The computed waist coordinate keeps the original half-gap and complete certified unit direction. -/
@[expose] def coordinate (site : Fin 2) (parameter : Canonical) (direction : UnitVertex) : Canonical :=
  halfGap site parameter * direction.value

/-- Every waist coordinate has exactly the original half-gap's squared norm. -/
theorem coordinate_normSq (site : Fin 2) (parameter : Canonical) (direction : UnitVertex) :
    Norm.Basic.normSq (coordinate site parameter direction) = Norm.Basic.normSq (halfGap site parameter) := by
  unfold coordinate
  rewrite [Norm.Basic.normSq_mul, direction.unit]
  exact Fraction.Field.mul_one_direct _

/-- The second waist coordinate uses the same half-gap and the conjugate of the original certified unit direction. -/
theorem partner_coordinate (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site) :
    partner site parameter (coordinate site parameter direction) =
      halfGap site parameter * Basic.conj direction.value := by
  have directionNonzero : direction.value ≠ 0 := by
    intro zero
    have unit := direction.unit
    rewrite [zero, Norm.Basic.normSq_zero] at unit
    exact (by decide +kernel : (0 : Fraction.Rational) ≠ 1) unit
  have gapNonzero : halfGap site parameter ≠ 0 := Split.halfGap_ne_zero (by decide +kernel) regular.symm
  have nonzero : coordinate site parameter direction ≠ 0 := Field.mul_ne_zero_direct gapNonzero directionNonzero
  have unitProduct : direction.value * Basic.conj direction.value = 1 := by
    have product := Basic.Canonical.mul_conj direction.value
    rewrite [← Norm.Basic.normSq_eq_canonical, direction.unit] at product
    exact product
  apply ExplicitField.eq_of_mul_eq_mul_right nonzero
  calc
    partner site parameter (coordinate site parameter direction) * coordinate site parameter direction =
        smoothing site parameter := partner_mul_coordinate _ _ _ nonzero
    _ = (halfGap site parameter * Basic.conj direction.value) * coordinate site parameter direction := by
      unfold smoothing coordinate
      calc
        halfGap site parameter ^ 2 = halfGap site parameter ^ 2 * 1 := by ring1
        _ = halfGap site parameter ^ 2 * (direction.value * Basic.conj direction.value) :=
          congrArg (fun value => halfGap site parameter ^ 2 * value) unitProduct.symm
        _ = _ := by ring1

/-- The original parameter-distance bound derives admission to the same original parameter square. -/
theorem parameter_inside (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (parameterBox site).Contains parameter := by
  have distance : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 4 : Fraction.Rational) ^ 2 := by
    rewrite [show (1 / 4 : Fraction.Rational) ^ 2 = 1 / 16 by decide +kernel]
    exact bound
  exact Box.Square.Centered.centeredBox_contains_of_normSq_sub_le (by decide +kernel) distance

/-- The same original parameter-distance bound derives the computed annulus outer bound on its labelled half-gap. -/
theorem halfGap_bound (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Norm.Basic.normSq (halfGap site parameter) ≤ outerRadiusSq := by
  have displacement : halfGap site parameter * 2 = parameter - criticalValue site :=
    Split.halfGap_mul_two _ _ (by decide +kernel)
  have norm := congrArg Norm.Basic.normSq displacement
  rewrite [Norm.Basic.normSq_mul, show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel] at norm
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide +kernel)
  calc
    Norm.Basic.normSq (halfGap site parameter) * 4 = Norm.Basic.normSq (parameter - criticalValue site) := norm
    _ ≤ 1 / 16 := bound
    _ = outerRadiusSq * 4 := by decide +kernel

/-- Every retained unit direction is admitted to the same computed annulus waist. -/
theorem coordinate_inside (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Contains site parameter (coordinate site parameter direction) := by
  unfold Contains
  rewrite [coordinate_normSq]
  exact waist_contains _ _ (halfGap_bound site parameter bound)

/-- Construct the exact original conic waist point with all radial admission derived internally. -/
def point (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Point site parameter :=
  Annulus.point site parameter (coordinate site parameter direction) regular (coordinate_inside _ _ _ bound)

/-- The conic waist point retains the scaled original unit direction as its exact first coordinate. -/
theorem point_plus (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter direction regular bound).plus = coordinate site parameter direction :=
  Annulus.point_plus _ _ _ regular (coordinate_inside _ _ _ bound)

/-- The conic waist point retains the scaled conjugate direction as its exact second coordinate. -/
theorem point_minus (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter direction regular bound).minus = halfGap site parameter * Basic.conj direction.value :=
  (Annulus.point_minus _ _ _ regular (coordinate_inside _ _ _ bound)).trans
    (partner_coordinate site parameter direction regular)

/-- The exact waist abscissa scales the embedded real component of the same original unit direction. -/
theorem point_abscissa (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter direction regular bound).abscissa =
      halfGap site parameter * Components.Projection.realPart direction.value := by
  apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  calc
    (point site parameter direction regular bound).abscissa * 2 =
        (point site parameter direction regular bound).minus + (point site parameter direction regular bound).plus :=
      ExplicitField.div_mul_cancel _ (by decide +kernel)
    _ = halfGap site parameter * Basic.conj direction.value + coordinate site parameter direction := by
      rewrite [point_minus, point_plus]
      rfl
    _ = halfGap site parameter * (direction.value + Basic.conj direction.value) := by
      unfold coordinate
      ring1
    _ = (halfGap site parameter * Components.Projection.realPart direction.value) * 2 := by
      rewrite [← Components.Projection.realPart_mul_two]
      ring1

/-- The exact normalized waist ordinate scales the embedded imaginary component of the same unit direction. -/
theorem point_ordinate (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter direction regular bound).ordinate =
      halfGap site parameter * Components.Projection.imaginaryPart direction.value := by
  apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  calc
    (point site parameter direction regular bound).ordinate * 2 =
        (point site parameter direction regular bound).plus - (point site parameter direction regular bound).minus :=
      Split.halfGap_mul_two _ _ (by decide +kernel)
    _ = coordinate site parameter direction - halfGap site parameter * Basic.conj direction.value := by
      rewrite [point_plus, point_minus]
      rfl
    _ = halfGap site parameter * (direction.value - Basic.conj direction.value) := by
      unfold coordinate
      ring1
    _ = (halfGap site parameter * Components.Projection.imaginaryPart direction.value) * 2 := by
      rewrite [← Components.Projection.imaginaryPart_mul_two]
      ring1

/-- The original cubic base of a waist point is the collision midpoint plus its exact real-direction displacement. -/
theorem point_base (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter direction regular bound).base =
      center site parameter + halfGap site parameter * Components.Projection.realPart direction.value := by
  rewrite [Point.base, point_abscissa]
  rfl

/-- Every original rational quarter starts at its retained quarter-turn multiplier. -/
theorem direction_start_value (quarter : UnitCircuitQuarter) :
    (direction quarter 0).value = Quarter.unitCircuitMultiplier quarter := by
  rewrite [direction_value, Stereographic.unitQuarterPoint_zero, Basic.mul_one]
  rfl

/-- The first original waist quarter starts at the original moving branch with zero normalized ordinate. -/
theorem point_first_start (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (direction .first 0) regular bound).base = Paths.branchPoint parameter 1 ∧
      (point site parameter (direction .first 0) regular bound).ordinate = 0 := by
  constructor
  · rewrite [point_base, direction_start_value]
    change center site parameter + halfGap site parameter * 1 = Paths.branchPoint parameter 1
    rewrite [Basic.mul_one]
    exact center_add_halfGap site parameter
  · rewrite [point_ordinate, direction_start_value]
    change halfGap site parameter * 0 = 0
    exact Basic.mul_zero _

/-- The third original waist quarter starts at the original fixed branch with zero normalized ordinate. -/
theorem point_third_start (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (point site parameter (direction .third 0) regular bound).base = Paths.branchPoint parameter (fixedLabel site) ∧
      (point site parameter (direction .third 0) regular bound).ordinate = 0 := by
  constructor
  · rewrite [point_base, direction_start_value]
    change center site parameter + halfGap site parameter * (-1) = Paths.branchPoint parameter (fixedLabel site)
    calc
      _ = center site parameter - halfGap site parameter := by ring1
      _ = _ := center_sub_halfGap site parameter
  · rewrite [point_ordinate, direction_start_value]
    change halfGap site parameter * 0 = 0
    exact Basic.mul_zero _

/-- The waist point's original cubic base has internally derived spatial cofactor clearance. -/
theorem point_inside (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (spatialBox site).Contains (point site parameter direction regular bound).base :=
  Annulus.point_inside _ _ _ regular (parameter_inside _ _ bound) (coordinate_inside _ _ _ bound)

/-- Construct actual signed original cubic channels at a waist point from the intrinsic parameter-distance bound. -/
def lift (site : Fin 2) (parameter : Canonical) (direction : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    Lift (point site parameter direction regular bound)
      (UnitRoot.owner site (point site parameter direction regular bound).base (point_inside _ _ _ regular bound)) :=
  Lift.build (point site parameter direction regular bound) (point_inside _ _ _ regular bound)

/-- The four original rational unit quarters join exactly and close at the original first direction. -/
theorem directions_join :
    direction .first 1 = direction .second 0 ∧ direction .second 1 = direction .third 0 ∧
      direction .third 1 = direction .fourth 0 ∧ direction .fourth 1 = direction .first 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply UnitVertex.eq_of_value_eq
    rewrite [direction_value, direction_value, Stereographic.unitQuarterPoint_one,
      Stereographic.unitQuarterPoint_zero]
    decide +kernel

/-- The four exact original conic waist pieces join and close on the same labelled fibre. -/
theorem points_join (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    point site parameter (direction .first 1) regular bound = point site parameter (direction .second 0) regular bound ∧
      point site parameter (direction .second 1) regular bound =
        point site parameter (direction .third 0) regular bound ∧
      point site parameter (direction .third 1) regular bound =
        point site parameter (direction .fourth 0) regular bound ∧
      point site parameter (direction .fourth 1) regular bound =
        point site parameter (direction .first 0) regular bound :=
  ⟨congrArg (fun input => point site parameter input regular bound) directions_join.1,
    congrArg (fun input => point site parameter input regular bound) directions_join.2.1,
    congrArg (fun input => point site parameter input regular bound) directions_join.2.2.1,
    congrArg (fun input => point site parameter input regular bound) directions_join.2.2.2⟩

/-- The actual signed cubic channels of the four waist pieces join and close as the same retained programs. -/
theorem values_join (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    (lift site parameter (direction .first 1) regular bound).value =
        (lift site parameter (direction .second 0) regular bound).value ∧
      (lift site parameter (direction .second 1) regular bound).value =
        (lift site parameter (direction .third 0) regular bound).value ∧
      (lift site parameter (direction .third 1) regular bound).value =
        (lift site parameter (direction .fourth 0) regular bound).value ∧
      (lift site parameter (direction .fourth 1) regular bound).value =
        (lift site parameter (direction .first 0) regular bound).value :=
  ⟨congrArg (fun input => (lift site parameter input regular bound).value) directions_join.1,
    congrArg (fun input => (lift site parameter input regular bound).value) directions_join.2.1,
    congrArg (fun input => (lift site parameter input regular bound).value) directions_join.2.2.1,
    congrArg (fun input => (lift site parameter input regular bound).value) directions_join.2.2.2⟩

/-- Every rational waist quarter has an explicit finite squared-distance bound in its original coordinate. -/
theorem quarter_distance_le (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq (coordinate site parameter (direction quarter first) -
      coordinate site parameter (direction quarter last)) ≤
        4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have difference : coordinate site parameter (direction quarter first) -
      coordinate site parameter (direction quarter last) =
      (halfGap site parameter * Quarter.unitCircuitMultiplier quarter) *
        (Stereographic.unitQuarterPoint first - Stereographic.unitQuarterPoint last) := by
    unfold coordinate
    rewrite [direction_value, direction_value]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Quarter.unitCircuitMultiplier_unit,
    Fraction.Field.mul_one_direct]
  calc
    Norm.Basic.normSq (halfGap site parameter) *
        Norm.Basic.normSq (Stereographic.unitQuarterPoint first - Stereographic.unitQuarterPoint last) ≤
        Norm.Basic.normSq (halfGap site parameter) * (4 * (first - last) ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Stereographic.unitQuarterPoint_distance_le first last) (Norm.Basic.normSq_nonneg _)
    _ = _ := by ring1

/-- The entire original cubic base chart has the same finite squared-distance bound as its conic coordinate. -/
theorem quarter_base_distance_le (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (first last : Fraction.Rational) :
    Norm.Basic.normSq ((point site parameter (direction quarter first) regular bound).base -
      (point site parameter (direction quarter last) regular bound).base) ≤
        4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have baseDifference : (point site parameter (direction quarter first) regular bound).base -
      (point site parameter (direction quarter last) regular bound).base =
      halfGap site parameter * Components.Projection.realPart ((direction quarter first).value -
        (direction quarter last).value) := by
    rewrite [point_base, point_base, Components.Projection.realPart_sub]
    ring1
  have coordinateDifference : coordinate site parameter (direction quarter first) -
      coordinate site parameter (direction quarter last) =
      halfGap site parameter * ((direction quarter first).value - (direction quarter last).value) := by
    unfold coordinate
    ring1
  calc
    _ = Norm.Basic.normSq (halfGap site parameter) * Norm.Basic.normSq
        (Components.Projection.realPart ((direction quarter first).value - (direction quarter last).value)) := by
      rewrite [baseDifference, Norm.Basic.normSq_mul]
      rfl
    _ ≤ Norm.Basic.normSq (halfGap site parameter) *
        Norm.Basic.normSq ((direction quarter first).value - (direction quarter last).value) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Components.Projection.normSq_realPart_le _)
        (Norm.Basic.normSq_nonneg _)
    _ = Norm.Basic.normSq (coordinate site parameter (direction quarter first) -
        coordinate site parameter (direction quarter last)) := by
      rewrite [coordinateDifference, Norm.Basic.normSq_mul]
      rfl
    _ ≤ _ := quarter_distance_le _ _ _ _ _

/-- The original cofactor evaluated along the actual original cubic base of the retained rational quarter. -/
@[expose] def cofactor (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (time : Fraction.Rational) : Canonical :=
  (unitPolynomial site).eval (point site parameter (direction quarter time) regular bound).base

/-- The original cofactor path has the internally derived finite quarter variation bound at all rational parameters. -/
theorem cofactor_distance_le (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational))
    (first last : Fraction.Rational) :
    Norm.Basic.normSq (cofactor site parameter quarter regular bound first -
      cofactor site parameter quarter regular bound last) ≤
        4 * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
  have difference : cofactor site parameter quarter regular bound first -
      cofactor site parameter quarter regular bound last =
      (point site parameter (direction quarter first) regular bound).base -
        (point site parameter (direction quarter last) regular bound).base := by
    unfold cofactor
    rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
      Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    ring1
  rewrite [difference]
  exact quarter_base_distance_le _ _ _ regular bound _ _

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
