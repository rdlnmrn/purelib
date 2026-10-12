module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio
-- The existing public Parametrization path re-exports these certificate owners.
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
import Purelib.Curves.Plane.Folium.Parametrization
public import Purelib.Curves.Plane.Folium.Tangent.Conic
public import Purelib.Curves.Plane.Folium.Tangent.Line
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Reciprocal folium tangent directions and spread

The original cross-tangent coefficients are retained as denominator-cleared
polynomials at two supplied parameters. When their product is one, their exact
scaled direction identities identify the two spread values using each retained
non-nullness witness and the scalar ratio operation.
-/

section
namespace Purelib.Curves.Plane.Folium.Tangent.ReciprocalSpread

open Purelib.Algebra.Field
open Purelib.Curves.Plane.Folium
open Purelib.Curves.Plane.Folium.Parametrization
open Purelib.Curves.Plane.Folium.Tangent
open Purelib.Curves.Plane.Folium.Tangent.Conic
open Purelib.Curves.Plane.Folium.Tangent.Line
open Purelib.Geometry.Plane.Line
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K]

/-- First denominator-cleared direction coefficient of the tangent to the tangent
conic at `t`, evaluated at the point with parameter `u`.

The first scalar coefficient retains both parameters and their
displayed parameter denominators. -/
@[expose] public def crossTangentA (parameter otherParameter : K) : K :=
  9 * parameter ^ 2 * Parametrization.parameterDenominator otherParameter -
    18 * parameter * Parametrization.parameterDenominator parameter * otherParameter +
    3 * Parametrization.parameterDenominator parameter ^ 2 * otherParameter ^ 2

/-- Second denominator-cleared direction coefficient of the same tangent.

The second scalar coefficient uses the same retained parameters and
denominator polynomials as the first coefficient. -/
@[expose] public def crossTangentB (parameter otherParameter : K) : K :=
  9 * parameter ^ 4 * Parametrization.parameterDenominator otherParameter +
    3 * Parametrization.parameterDenominator parameter ^ 2 * otherParameter -
    18 * parameter ^ 2 * Parametrization.parameterDenominator parameter *
      otherParameter ^ 2

/-- The two displayed coefficients above really are the gradient of the tangent
conic at the other parameter point, multiplied by `1+u³`.

The two nonzero denominator witnesses clear the original gradient at the
retained second parameter point, without changing its tangent conic
coefficients. -/
public theorem crossTangent_coefficients [Nontrivial K]
    (parameter otherParameter : K)
    (parameterDenominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0)
    (otherDenominatorNonzero : Parametrization.parameterDenominator otherParameter ≠ 0) :
    let conic := Conic.tangentConic parameter parameterDenominatorNonzero
    let point := Parametrization.parameterPoint otherParameter
    Parametrization.parameterDenominator otherParameter *
        (conic.a + 2 * conic.d * point.x + conic.e * point.y) =
          crossTangentA parameter otherParameter ∧
      Parametrization.parameterDenominator otherParameter *
        (conic.b + conic.e * point.x + 2 * conic.f * point.y) =
          crossTangentB parameter otherParameter := by
  dsimp only
  let denominator := Parametrization.parameterDenominator otherParameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator otherDenominatorNonzero
  unfold Conic.tangentConic Parametrization.parameterPoint
  simp only [ExplicitField.div_eq_mul_inv]
  change
    denominator *
          (9 * parameter ^ 2 +
            2 * (3 * parameter * Parametrization.parameterDenominator parameter) *
              ((-3 * otherParameter) * denominator⁻¹) +
            (-(Parametrization.parameterDenominator parameter ^ 2)) *
              ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
        crossTangentA parameter otherParameter ∧
      denominator *
          (9 * parameter ^ 4 +
            (-(Parametrization.parameterDenominator parameter ^ 2)) *
              ((-3 * otherParameter) * denominator⁻¹) +
            2 * (3 * parameter ^ 2 * Parametrization.parameterDenominator parameter) *
              ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
        crossTangentB parameter otherParameter
  constructor
  · calc
      denominator *
            (9 * parameter ^ 2 +
              2 * (3 * parameter * Parametrization.parameterDenominator parameter) *
                ((-3 * otherParameter) * denominator⁻¹) +
              (-(Parametrization.parameterDenominator parameter ^ 2)) *
                ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
          9 * parameter ^ 2 * denominator -
            18 * parameter * Parametrization.parameterDenominator parameter *
              otherParameter * (denominator * denominator⁻¹) +
            3 * Parametrization.parameterDenominator parameter ^ 2 *
              otherParameter ^ 2 * (denominator * denominator⁻¹) := by
        ring1
      _ = crossTangentA parameter otherParameter := by
        rw [cancel]
        unfold crossTangentA
        ring1
  · calc
      denominator *
            (9 * parameter ^ 4 +
              (-(Parametrization.parameterDenominator parameter ^ 2)) *
                ((-3 * otherParameter) * denominator⁻¹) +
              2 * (3 * parameter ^ 2 * Parametrization.parameterDenominator parameter) *
                ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
          9 * parameter ^ 4 * denominator +
            3 * Parametrization.parameterDenominator parameter ^ 2 * otherParameter *
              (denominator * denominator⁻¹) -
            18 * parameter ^ 2 * Parametrization.parameterDenominator parameter *
              otherParameter ^ 2 * (denominator * denominator⁻¹) := by
        ring1
      _ = crossTangentB parameter otherParameter := by
        rw [cancel]
        unfold crossTangentB
        ring1

/-- A line carrying only the denominator-cleared cross-tangent direction. Its
constant is irrelevant to spread.

The original two direction coefficients and zero constant define the line; the
supplied squared-direction witness certifies that these coefficients do not
both vanish. -/
@[expose] public def crossTangentDirection [DecidableEq K]
    (parameter otherParameter : K)
    (nonNull : crossTangentA parameter otherParameter ^ 2 +
      crossTangentB parameter otherParameter ^ 2 ≠ 0) : Geometry.Plane.Line K where
  a := crossTangentA parameter otherParameter
  b := crossTangentB parameter otherParameter
  c := 0
  direction_nonzero := by
    by_cases firstZero : crossTangentA parameter otherParameter = 0
    · right
      intro secondZero
      apply nonNull
      rw [firstZero, secondZero]
      ring1
    · exact Or.inl firstZero

section Folium
open _root_.Purelib.Curves.Plane.Folium.Tangent.ReciprocalSpread
/-- The supplied nonzero squared-direction sum makes the retained cross-tangent
line non-null.

The same supplied squared-direction witness is the non-nullness condition of
the original retained line. -/
private theorem crossTangentDirection_nonNull [DecidableEq K]
    (parameter otherParameter : K)
    (nonNull : crossTangentA parameter otherParameter ^ 2 +
      crossTangentB parameter otherParameter ^ 2 ≠ 0) :
    ¬ (crossTangentDirection parameter otherParameter nonNull).IsNull := by
  unfold crossTangentDirection Geometry.Plane.Line.IsNull
  exact nonNull
/-- Reciprocal folium tangent direction coefficients are swapped after scaling by
the original parameter to the fourth power.

The reciprocal-product witness rewrites the original two tangent coefficients
after their common fourth-power scale. -/
private theorem reciprocal_tangentLine_scaled [Nontrivial K]
    [DecidableEq K]
    (parameter reciprocalParameter : K) (threeNonzero : (3 : K) ≠ 0)
    (productOne : parameter * reciprocalParameter = 1) :
    parameter ^ 4 * (Line.tangentLine reciprocalParameter threeNonzero).a =
        (Line.tangentLine parameter threeNonzero).b ∧
      parameter ^ 4 * (Line.tangentLine reciprocalParameter threeNonzero).b =
        (Line.tangentLine parameter threeNonzero).a := by
  unfold Line.tangentLine
  constructor
  · calc
      parameter ^ 4 * (reciprocalParameter *
          (2 - reciprocalParameter ^ 3)) =
        2 * parameter ^ 3 * (parameter * reciprocalParameter) -
          (parameter * reciprocalParameter) ^ 4 := by ring1
      _ = 2 * parameter ^ 3 - 1 := by rw [productOne]; ring1
  · calc
      parameter ^ 4 * (2 * reciprocalParameter ^ 3 - 1) =
          2 * parameter * (parameter * reciprocalParameter) ^ 3 -
            parameter ^ 4 := by ring1
      _ = parameter * (2 - parameter ^ 3) := by rw [productOne]; ring1
/-- Reciprocal cross-tangent coefficients exchange after scaling by the original
parameter cubed.

The reciprocal-product witness rewrites the original cross-tangent polynomial
after its displayed third-power scale. -/
private theorem reciprocal_crossTangent_scaled
    (parameter reciprocalParameter : K)
    (productOne : parameter * reciprocalParameter = 1) :
    parameter ^ 3 * crossTangentA reciprocalParameter parameter =
      crossTangentB parameter reciprocalParameter := by
  let common :=
    3 * reciprocalParameter + 9 * parameter + 6 * parameter ^ 2 -
      18 * parameter ^ 3 + 9 * parameter ^ 4 + 3 * parameter ^ 5 - 18
  calc
    parameter ^ 3 * crossTangentA reciprocalParameter parameter =
        9 * parameter * (parameter * reciprocalParameter) ^ 2 +
          9 * parameter ^ 4 * (parameter * reciprocalParameter) ^ 2 -
          18 * parameter ^ 3 * (parameter * reciprocalParameter) -
          18 * (parameter * reciprocalParameter) ^ 4 +
          3 * parameter ^ 5 +
          6 * parameter ^ 2 * (parameter * reciprocalParameter) ^ 3 +
          3 * reciprocalParameter *
            (parameter * reciprocalParameter) ^ 5 := by
      unfold crossTangentA Parametrization.parameterDenominator
      ring1
    _ = common := by rw [productOne]; unfold common; ring1
    _ = 9 * parameter ^ 4 +
          9 * parameter * (parameter * reciprocalParameter) ^ 3 +
          3 * reciprocalParameter +
          6 * parameter ^ 2 * (parameter * reciprocalParameter) +
          3 * parameter ^ 5 * (parameter * reciprocalParameter) -
          18 * (parameter * reciprocalParameter) ^ 2 -
          18 * parameter ^ 3 *
            (parameter * reciprocalParameter) ^ 2 := by
      rw [productOne]
      unfold common
      ring1
    _ = crossTangentB parameter reciprocalParameter := by
      unfold crossTangentB Parametrization.parameterDenominator
      ring1
end Folium

/-- Exercise 19.4, second assertion. Under reciprocal parameters, the spread
between the folium tangent and the cross-tangent to its tangent conic is the
same at the two points. The four non-null hypotheses are precisely the finite
conditions needed for the two spreads to be defined.

The original scaled direction identities yield a scalar cross-product equality
between the two retained ratios. The four supplied non-nullness witnesses
justify clearing their two denominators. -/
public theorem reciprocal_tangent_spreads [Nontrivial K] [DecidableEq K]
    (parameter reciprocalParameter : K) (threeNonzero : (3 : K) ≠ 0)
    (productOne : parameter * reciprocalParameter = 1)
    (parameterTangentNonNull :
      ¬ (Line.tangentLine parameter threeNonzero).IsNull)
    (reciprocalTangentNonNull :
      ¬ (Line.tangentLine reciprocalParameter threeNonzero).IsNull)
    (parameterCrossNonNull :
      crossTangentA parameter reciprocalParameter ^ 2 +
        crossTangentB parameter reciprocalParameter ^ 2 ≠ 0)
    (reciprocalCrossNonNull :
      crossTangentA reciprocalParameter parameter ^ 2 +
        crossTangentB reciprocalParameter parameter ^ 2 ≠ 0) :
    Spread.spread (Line.tangentLine parameter threeNonzero)
        (crossTangentDirection parameter reciprocalParameter
          parameterCrossNonNull)
        parameterTangentNonNull
        (show ¬ (crossTangentDirection parameter reciprocalParameter
            parameterCrossNonNull).IsNull from by
          unfold crossTangentDirection Geometry.Plane.Line.IsNull
          exact parameterCrossNonNull) =
      Spread.spread (Line.tangentLine reciprocalParameter threeNonzero)
        (crossTangentDirection reciprocalParameter parameter
          reciprocalCrossNonNull)
        reciprocalTangentNonNull
        (show ¬ (crossTangentDirection reciprocalParameter parameter
            reciprocalCrossNonNull).IsNull from by
          unfold crossTangentDirection Geometry.Plane.Line.IsNull
          exact reciprocalCrossNonNull) := by
  let first := Line.tangentLine parameter threeNonzero
  let second := crossTangentDirection parameter reciprocalParameter
    parameterCrossNonNull
  let reciprocalFirst := Line.tangentLine reciprocalParameter threeNonzero
  let reciprocalSecond := crossTangentDirection reciprocalParameter parameter
    reciprocalCrossNonNull
  have firstScaled := reciprocal_tangentLine_scaled
    parameter
    reciprocalParameter threeNonzero productOne
  have crossFirstScaled := reciprocal_crossTangent_scaled
    parameter
    reciprocalParameter productOne
  have reverseProduct : reciprocalParameter * parameter = 1 := by
    calc
      reciprocalParameter * parameter = parameter * reciprocalParameter := by
        ring1
      _ = 1 := productOne
  have reverseCrossScaled := reciprocal_crossTangent_scaled
    reciprocalParameter parameter reverseProduct
  have crossSecondScaled :
      parameter ^ 3 * crossTangentB reciprocalParameter parameter =
        crossTangentA parameter reciprocalParameter := by
    calc
      parameter ^ 3 * crossTangentB reciprocalParameter parameter =
          parameter ^ 3 *
            (reciprocalParameter ^ 3 *
              crossTangentA parameter reciprocalParameter) := by
        rw [reverseCrossScaled]
      _ = (parameter * reciprocalParameter) ^ 3 *
          crossTangentA parameter reciprocalParameter := by ring1
      _ = crossTangentA parameter reciprocalParameter := by
        rw [productOne]
        ring1
  have firstA : parameter ^ 4 * reciprocalFirst.a = first.b := firstScaled.1
  have firstB : parameter ^ 4 * reciprocalFirst.b = first.a := firstScaled.2
  have secondA : parameter ^ 3 * reciprocalSecond.a = second.b := crossFirstScaled
  have secondB : parameter ^ 3 * reciprocalSecond.b = second.a := crossSecondScaled
  have firstDenominatorNonzero : Basic.lineNorm first * Basic.lineNorm second ≠ 0 :=
    ExplicitField.mul_ne_zero parameterTangentNonNull parameterCrossNonNull
  have reciprocalDenominatorNonzero :
      Basic.lineNorm reciprocalFirst * Basic.lineNorm reciprocalSecond ≠ 0 :=
    ExplicitField.mul_ne_zero reciprocalTangentNonNull reciprocalCrossNonNull
  change
    (first.a * second.b - second.a * first.b) ^ 2 /
        (Basic.lineNorm first * Basic.lineNorm second) =
      (reciprocalFirst.a * reciprocalSecond.b - reciprocalSecond.a * reciprocalFirst.b) ^ 2 /
        (Basic.lineNorm reciprocalFirst * Basic.lineNorm reciprocalSecond)
  apply Ratio.ratio_eq_of_cross_product firstDenominatorNonzero
    reciprocalDenominatorNonzero
  unfold Basic.lineNorm
  rw [← firstA, ← firstB, ← secondA, ← secondB]
  ring1

end Purelib.Curves.Plane.Folium.Tangent.ReciprocalSpread
end
