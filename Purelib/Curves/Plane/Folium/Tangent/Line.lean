module

import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
-- Parametrization deliberately re-exports these original certificate owners.
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
public import Purelib.Curves.Plane.Cubic.Tangent.Line
import Purelib.Curves.Plane.Cubic.Taylor
import Purelib.Curves.Plane.Folium.Basic
public import Purelib.Curves.Plane.Folium.Parametrization
import Purelib.Geometry.Plane.Line.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Tangent lines at retained folium parameter points

The displayed folium tangent keeps its three retained coefficients and a
constructive nonzero direction witness. The Taylor-gradient identities retain
the same parameter point and denominator, with an explicit common scale whose
nonvanishing hypotheses are recorded separately.
-/

section
namespace Purelib.Curves.Plane.Folium.Tangent.Line

open Purelib.Algebra.Field
open Purelib.Curves.Plane.Cubic.Basic
open Purelib.Curves.Plane.Folium
open Purelib.Curves.Plane.Folium
open Purelib.Curves.Plane.Folium.Parametrization
open Purelib.Geometry.Plane
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [ExplicitField K]

section Folium
open _root_.Purelib.Curves.Plane.Folium.Tangent.Line
/-- When three is nonzero, the two displayed folium tangent direction coefficients
cannot both vanish.

The explicit characteristic condition excludes simultaneous vanishing of the
two original direction coefficients; decidable equality retains their direct
case split. -/
private theorem tangentDirection_nonzero [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) :
    parameter * (2 - parameter ^ 3) ≠ 0 ∨
      2 * parameter ^ 3 - 1 ≠ 0 := by
  by_cases firstZero : parameter * (2 - parameter ^ 3) = 0
  · right
    intro secondZero
    have parameterNonzero : parameter ≠ 0 := by
      intro parameterZero
      have oneZero : (1 : K) = 0 := by
        calc
          (1 : K) = -(2 * parameter ^ 3 - 1) := by rw [parameterZero]; ring1
          _ = 0 := by rw [secondZero]; ring1
      exact one_ne_zero oneZero
    have threeTimesParameterZero : (3 : K) * parameter = 0 := by
      calc
        (3 : K) * parameter =
            2 * (parameter * (2 - parameter ^ 3)) +
              parameter * (2 * parameter ^ 3 - 1) := by ring1
        _ = 0 := by rw [firstZero, secondZero]; ring1
    exact
      (ExplicitField.mul_ne_zero threeNonzero parameterNonzero)
        threeTimesParameterZero
  · exact Or.inl firstZero
end Folium

/-- Equation (19.5), retaining the representative printed by the source.

The three coefficients are the scalar formulas at the supplied
parameter. The characteristic condition supplies a constructive nonzero
direction witness. -/
@[expose] public def tangentLine [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) : Geometry.Plane.Line K where
  a := parameter * (2 - parameter ^ 3)
  b := 2 * parameter ^ 3 - 1
  c := 3 * parameter ^ 2
  direction_nonzero := by
    by_cases firstZero : parameter * (2 - parameter ^ 3) = 0
    · right
      intro secondZero
      have parameterNonzero : parameter ≠ 0 := by
        intro parameterZero
        have oneZero : (1 : K) = 0 := by
          calc
            (1 : K) = -(2 * parameter ^ 3 - 1) := by rw [parameterZero]; ring1
            _ = 0 := by rw [secondZero]; ring1
        exact one_ne_zero oneZero
      have threeTimesParameterZero : (3 : K) * parameter = 0 := by
        calc
          (3 : K) * parameter =
              2 * (parameter * (2 - parameter ^ 3)) +
                parameter * (2 * parameter ^ 3 - 1) := by ring1
          _ = 0 := by rw [firstZero, secondZero]; ring1
      exact
        (ExplicitField.mul_ne_zero threeNonzero parameterNonzero)
          threeTimesParameterZero
    · exact Or.inl firstZero

/-- The printed tangent representative passes through its parameter point,
including at `t=0` where the cubic itself is singular.

The supplied denominator witness permits scalar cancellation at the same
original parameter point. The displayed line coefficients are retained,
including the singular zero parameter. -/
public theorem tangentLine_contains [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    (tangentLine parameter threeNonzero).Contains (Parametrization.parameterPoint parameter) := by
  let denominator := Parametrization.parameterDenominator parameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold tangentLine Geometry.Plane.Line.Contains Parametrization.parameterPoint
  simp only [ExplicitField.div_eq_mul_inv]
  change
    parameter * (2 - parameter ^ 3) *
          ((-3 * parameter) * denominator⁻¹) +
        (2 * parameter ^ 3 - 1) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        3 * parameter ^ 2 = 0
  calc
    parameter * (2 - parameter ^ 3) *
          ((-3 * parameter) * denominator⁻¹) +
        (2 * parameter ^ 3 - 1) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        3 * parameter ^ 2 =
      3 * parameter ^ 2 * (1 - denominator * denominator⁻¹) := by
        unfold denominator Parametrization.parameterDenominator
        ring1
    _ = 0 := by rw [cancel]; ring1

/-- The nonzero scale relating the Taylor gradient to equation (19.5).

The scale retains the original parameter denominator inverse and the original
scalar factor in the Taylor-gradient comparison. -/
@[expose] public def tangentScale (parameter : K) : K :=
  9 * parameter * (Parametrization.parameterDenominator parameter)⁻¹ ^ 2

section Folium
open _root_.Purelib.Curves.Plane.Folium.Tangent.Line
/-- The common Taylor-to-folium tangent scale is nonzero when three, the parameter
and its denominator are nonzero.

The three supplied nonzero witnesses certify the original scalar factor,
parameter and squared denominator inverse, hence their displayed product. -/
private theorem tangentScale_nonzero [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    tangentScale parameter ≠ 0 := by
  have nineNonzero : (9 : K) ≠ 0 := by
    have threeSquaredNonzero : (3 : K) * 3 ≠ 0 :=
      ExplicitField.mul_ne_zero threeNonzero threeNonzero
    intro nineZero
    apply threeSquaredNonzero
    calc
      (3 : K) * 3 = 9 := by ring1
      _ = 0 := nineZero
  have inverseNonzero :
      (Parametrization.parameterDenominator parameter)⁻¹ ≠ 0 :=
    ExplicitField.inv_ne_zero denominatorNonzero
  have inverseSquareNonzero :
      (Parametrization.parameterDenominator parameter)⁻¹ ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero inverseNonzero inverseNonzero
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero nineNonzero parameterNonzero)
    inverseSquareNonzero
end Folium

/-- The first Taylor coefficient at (19.3) is the first coefficient of (19.5),
multiplied by the explicit common scale.

The equality compares the original first Taylor coefficient at the retained
parameter point with the same displayed tangent coefficient and common scale. -/
public theorem taylorA_parameterPoint [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    CubicCurve.taylorA (curve (K := K)) (Parametrization.parameterPoint parameter) =
      tangentScale parameter * (parameter * (2 - parameter ^ 3)) := by
  let denominator := Parametrization.parameterDenominator parameter
  rw [show CubicCurve.taylorA (Folium.curve (K := K)) (Parametrization.parameterPoint parameter) =
      3 * (Parametrization.parameterPoint parameter).x ^ 2 +
        3 * (Parametrization.parameterPoint parameter).y by
    unfold CubicCurve.taylorA Folium.curve
    ring1]
  unfold Parametrization.parameterPoint tangentScale
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    3 * ((-3 * parameter) * denominator⁻¹) ^ 2 +
          3 * ((-3 * parameter ^ 2) * denominator⁻¹) =
        27 * parameter ^ 2 * denominator⁻¹ ^ 2 -
          9 * parameter ^ 2 * denominator⁻¹ := by
      ring1
    _ =
        (27 * parameter ^ 2 - 9 * parameter ^ 2 * denominator) *
          denominator⁻¹ ^ 2 := by
      calc
        27 * parameter ^ 2 * denominator⁻¹ ^ 2 -
            9 * parameter ^ 2 * denominator⁻¹ =
          27 * parameter ^ 2 * denominator⁻¹ ^ 2 +
            (-9 * parameter ^ 2) * denominator⁻¹ + 0 := by ring1
        _ = (27 * parameter ^ 2 +
              (-9 * parameter ^ 2) * denominator + 0 * denominator ^ 2) *
            denominator⁻¹ ^ 2 :=
          Purelib.Algebra.Field.Inverse.clear_quadratic_denominator denominatorNonzero
        _ = (27 * parameter ^ 2 - 9 * parameter ^ 2 * denominator) *
            denominator⁻¹ ^ 2 := by ring1
    _ = 9 * parameter * denominator⁻¹ ^ 2 *
        (parameter * (2 - parameter ^ 3)) := by
      unfold denominator Parametrization.parameterDenominator
      ring1

/-- The second Taylor coefficient at (19.3) is the second coefficient of (19.5),
multiplied by the same explicit scale.

The equality compares the original second Taylor coefficient at the retained
parameter point with the same displayed tangent coefficient and common scale. -/
public theorem taylorB_parameterPoint [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    CubicCurve.taylorB (curve (K := K)) (Parametrization.parameterPoint parameter) =
      tangentScale parameter * (2 * parameter ^ 3 - 1) := by
  let denominator := Parametrization.parameterDenominator parameter
  rw [show CubicCurve.taylorB (Folium.curve (K := K)) (Parametrization.parameterPoint parameter) =
      3 * (Parametrization.parameterPoint parameter).x +
        3 * (Parametrization.parameterPoint parameter).y ^ 2 by
    unfold CubicCurve.taylorB Folium.curve
    ring1]
  unfold Parametrization.parameterPoint tangentScale
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    3 * ((-3 * parameter) * denominator⁻¹) +
          3 * ((-3 * parameter ^ 2) * denominator⁻¹) ^ 2 =
        27 * parameter ^ 4 * denominator⁻¹ ^ 2 -
          9 * parameter * denominator⁻¹ := by
      ring1
    _ =
        (27 * parameter ^ 4 - 9 * parameter * denominator) *
          denominator⁻¹ ^ 2 := by
      calc
        27 * parameter ^ 4 * denominator⁻¹ ^ 2 -
            9 * parameter * denominator⁻¹ =
          27 * parameter ^ 4 * denominator⁻¹ ^ 2 +
            (-9 * parameter) * denominator⁻¹ + 0 := by ring1
        _ = (27 * parameter ^ 4 +
              (-9 * parameter) * denominator + 0 * denominator ^ 2) *
            denominator⁻¹ ^ 2 :=
          Purelib.Algebra.Field.Inverse.clear_quadratic_denominator denominatorNonzero
        _ = (27 * parameter ^ 4 - 9 * parameter * denominator) *
            denominator⁻¹ ^ 2 := by ring1
    _ = 9 * parameter * denominator⁻¹ ^ 2 *
        (2 * parameter ^ 3 - 1) := by
      unfold denominator Parametrization.parameterDenominator
      ring1

/-- Every allowed nonzero folium parameter is first-order nonsingular.

The nonzero common scale and the retained line direction witness select a
nonzero original Taylor-gradient coefficient. -/
public theorem firstOrderNonSingular_parameterPoint
    [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    (Folium.curve (K := K)).IsFirstOrderNonSingularAt
      (Parametrization.parameterPoint parameter) := by
  have scaleNonzero := tangentScale_nonzero parameter threeNonzero
    parameterNonzero denominatorNonzero
  rcases (tangentLine parameter threeNonzero).direction_nonzero with
    firstNonzero | secondNonzero
  · left
    rw [taylorA_parameterPoint parameter denominatorNonzero]
    exact ExplicitField.mul_ne_zero scaleNonzero firstNonzero
  · right
    rw [taylorB_parameterPoint parameter denominatorNonzero]
    exact ExplicitField.mul_ne_zero scaleNonzero secondNonzero

/-- Equation (19.5) is exactly the first-order tangent produced by the general
cubic Taylor construction, up to its displayed common scale.

The original Taylor line and printed line retain the same parameter point. The
denominator and nonzero parameter hypotheses certify their common scale and
all three coefficient comparisons. -/
public theorem tangentLine_formula [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    let nonSingular := firstOrderNonSingular_parameterPoint parameter
      threeNonzero parameterNonzero denominatorNonzero
    (CubicCurve.tangentLine (Folium.curve (K := K)) (Parametrization.parameterPoint parameter)
        nonSingular).Equivalent
      (tangentLine parameter threeNonzero) := by
  dsimp only
  let nonSingular := firstOrderNonSingular_parameterPoint parameter
    threeNonzero parameterNonzero denominatorNonzero
  let taylorLine := CubicCurve.tangentLine (Folium.curve (K := K))
    (Parametrization.parameterPoint parameter) nonSingular
  let printedLine := tangentLine parameter threeNonzero
  have firstCoefficient :
      taylorLine.a = tangentScale parameter * printedLine.a := by
    unfold taylorLine printedLine CubicCurve.tangentLine tangentLine
    exact taylorA_parameterPoint parameter denominatorNonzero
  have secondCoefficient :
      taylorLine.b = tangentScale parameter * printedLine.b := by
    unfold taylorLine printedLine CubicCurve.tangentLine tangentLine
    exact taylorB_parameterPoint parameter denominatorNonzero
  have printedContains : printedLine.Contains (Parametrization.parameterPoint parameter) := by
    exact tangentLine_contains parameter threeNonzero denominatorNonzero
  have constantCoefficient :
      taylorLine.c = tangentScale parameter * printedLine.c := by
    have constantDefinition :
        taylorLine.c =
          -taylorLine.a * (Parametrization.parameterPoint parameter).x -
            taylorLine.b * (Parametrization.parameterPoint parameter).y := by
      rfl
    rw [constantDefinition, firstCoefficient, secondCoefficient]
    unfold Geometry.Plane.Line.Contains at printedContains
    calc
      -(tangentScale parameter * printedLine.a) *
            (Parametrization.parameterPoint parameter).x -
          tangentScale parameter * printedLine.b *
            (Parametrization.parameterPoint parameter).y =
        tangentScale parameter * printedLine.c -
          tangentScale parameter *
            (printedLine.a * (Parametrization.parameterPoint parameter).x +
              printedLine.b * (Parametrization.parameterPoint parameter).y + printedLine.c) := by
        ring1
      _ = tangentScale parameter * printedLine.c := by
        rw [printedContains]
        ring1
  unfold Geometry.Plane.Line.Equivalent
  rw [firstCoefficient, secondCoefficient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩
end Purelib.Curves.Plane.Folium.Tangent.Line
end
