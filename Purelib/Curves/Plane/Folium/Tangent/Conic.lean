module

import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Curves.Plane.Conic.Translation
public import Purelib.Curves.Plane.Cubic.Tangent.Conic
import Purelib.Curves.Plane.Cubic.Taylor
import Purelib.Curves.Plane.Folium.Basic
public import Purelib.Curves.Plane.Folium.Parametrization
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Cubic.Basic

open Purelib.Curves.Plane.Folium

open Purelib.Curves.Plane.Folium.Parametrization

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, §19.4: the folium of Descartes

The folium, its rational parametrization, first- and second-order tangent
formulae, and the reciprocal-parameter spread symmetry are all finite
polynomial constructions.  Denominators and the characteristic-three
exception are exposed as explicit hypotheses.
-/

namespace Purelib.Curves.Plane.Folium.Tangent.Conic

section Folium

variable {K : Type*} [ExplicitField K]

/-- Equation (19.6), the second-order tangent conic in the source's cleared coefficient representative. -/
def tangentConic [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) : Conic K where
  d := 3 * parameter * parameterDenominator parameter
  e := -(parameterDenominator parameter ^ 2)
  f := 3 * parameter ^ 2 * parameterDenominator parameter
  a := 9 * parameter ^ 2
  b := 9 * parameter ^ 4
  c := 9 * parameter ^ 3
  quadratic_nonzero := Or.inr (Or.inl (by
    have squareNonzero :
        parameterDenominator parameter * parameterDenominator parameter ≠ 0 :=
      ExplicitField.mul_ne_zero
        denominatorNonzero denominatorNonzero
    intro negativeSquareZero
    apply squareNonzero
    calc
      parameterDenominator parameter * parameterDenominator parameter =
          parameterDenominator parameter ^ 2 := by ring1
      _ = -(-(parameterDenominator parameter ^ 2)) := by ring1
      _ = 0 := by rw [negativeSquareZero]; ring1))

/-- The conic (19.6) contains the point at which it is tangent. -/
theorem tangentConic_contains [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (tangentConic parameter denominatorNonzero).Contains
      (parameterPoint parameter) := by
  let denominator := parameterDenominator parameter
  unfold tangentConic Conic.Contains Conic.evaluate
    parameterPoint
  simp only [ExplicitField.div_eq_mul_inv]
  change
    (3 * parameter * denominator) *
          (((-3 * parameter) * denominator⁻¹) ^ 2) +
        (-(denominator ^ 2)) *
          ((-3 * parameter) * denominator⁻¹) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        (3 * parameter ^ 2 * denominator) *
          (((-3 * parameter ^ 2) * denominator⁻¹) ^ 2) +
        9 * parameter ^ 2 *
          ((-3 * parameter) * denominator⁻¹) +
        9 * parameter ^ 4 *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        9 * parameter ^ 3 = 0
  let quadratic :=
    27 * parameter ^ 3 * denominator -
      9 * denominator ^ 2 * parameter ^ 3 +
      27 * parameter ^ 6 * denominator
  let linear := -27 * parameter ^ 3 - 27 * parameter ^ 6
  let constant := 9 * parameter ^ 3
  calc
    (3 * parameter * denominator) *
            (((-3 * parameter) * denominator⁻¹) ^ 2) +
          (-(denominator ^ 2)) *
            ((-3 * parameter) * denominator⁻¹) *
            ((-3 * parameter ^ 2) * denominator⁻¹) +
          (3 * parameter ^ 2 * denominator) *
            (((-3 * parameter ^ 2) * denominator⁻¹) ^ 2) +
          9 * parameter ^ 2 *
            ((-3 * parameter) * denominator⁻¹) +
          9 * parameter ^ 4 *
            ((-3 * parameter ^ 2) * denominator⁻¹) +
          9 * parameter ^ 3 =
        quadratic * denominator⁻¹ ^ 2 +
          linear * denominator⁻¹ + constant := by
      unfold quadratic linear constant
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 :=
      Inverse.clear_quadratic_denominator denominatorNonzero
    _ = 0 := by
      have cleared :
          quadratic + linear * denominator + constant * denominator ^ 2 = 0 := by
        unfold quadratic linear constant denominator parameterDenominator
        ring1
      rw [cleared]
      ring1

/-- The mixed quadratic Taylor coefficient is constantly `3`, so every parameter point is second-order nonsingular when
the characteristic is not three. -/
theorem secondOrderNonSingular_parameterPoint [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) :
    (curve (K := K)).IsSecondOrderNonSingularAt
      (parameterPoint parameter) := by
  right
  left
  unfold CubicCurve.taylorE curve parameterPoint
  simpa only [zero_mul, add_zero, mul_zero] using threeNonzero

/-- Equation (19.6) is the general second-order Taylor conic. The equality is recorded coefficientwise after clearing
the common nonzero scale: `3·(printed coefficient) = -(1+t³)²·(Taylor coefficient)`. -/
theorem tangentConic_formula_cleared [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    let secondOrder :=
      secondOrderNonSingular_parameterPoint (K := K) parameter threeNonzero
    let taylor := CubicCurve.tangentConic (curve (K := K))
      (parameterPoint parameter) secondOrder
    let printed := tangentConic parameter denominatorNonzero
    3 * printed.d = -(parameterDenominator parameter ^ 2) * taylor.d ∧
      3 * printed.e = -(parameterDenominator parameter ^ 2) * taylor.e ∧
      3 * printed.f = -(parameterDenominator parameter ^ 2) * taylor.f ∧
      3 * printed.a = -(parameterDenominator parameter ^ 2) * taylor.a ∧
      3 * printed.b = -(parameterDenominator parameter ^ 2) * taylor.b ∧
      3 * printed.c = -(parameterDenominator parameter ^ 2) * taylor.c := by
  dsimp only
  let denominator := parameterDenominator parameter
  let secondOrder :=
    secondOrderNonSingular_parameterPoint (K := K) parameter threeNonzero
  let taylor := CubicCurve.tangentConic (curve (K := K))
    (parameterPoint parameter) secondOrder
  let printed := tangentConic parameter denominatorNonzero
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have denominatorSquareInverse :
      denominator ^ 2 * denominator⁻¹ = denominator := by
    calc
      denominator ^ 2 * denominator⁻¹ =
          denominator * (denominator * denominator⁻¹) := by ring1
      _ = denominator := by rw [cancel]; ring1
  have denominatorSquareInverseSquare :
      denominator ^ 2 * denominator⁻¹ ^ 2 = (1 : K) := by
    calc
      denominator ^ 2 * denominator⁻¹ ^ 2 =
          (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [cancel]; ring1
  have taylorD : taylor.d = -9 * parameter * denominator⁻¹ := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD curve parameterPoint
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have taylorE : taylor.e = 3 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorE curve
    ring1
  have taylorF : taylor.f = -9 * parameter ^ 2 * denominator⁻¹ := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorF curve parameterPoint
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have taylorA : taylor.a = -27 * parameter ^ 2 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD CubicCurve.taylorE
      CubicCurve.taylorA curve parameterPoint
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have taylorB : taylor.b = -27 * parameter ^ 4 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorE CubicCurve.taylorF
      CubicCurve.taylorB curve parameterPoint
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have taylorC : taylor.c = -27 * parameter ^ 3 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD CubicCurve.taylorE
      CubicCurve.taylorF CubicCurve.taylorA CubicCurve.taylorB curve
      parameterPoint
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  dsimp only [tangentConic]
  change
    3 * (3 * parameter * denominator) = -(denominator ^ 2) * taylor.d ∧
      3 * (-(denominator ^ 2)) = -(denominator ^ 2) * taylor.e ∧
      3 * (3 * parameter ^ 2 * denominator) =
        -(denominator ^ 2) * taylor.f ∧
      3 * (9 * parameter ^ 2) = -(denominator ^ 2) * taylor.a ∧
      3 * (9 * parameter ^ 4) = -(denominator ^ 2) * taylor.b ∧
      3 * (9 * parameter ^ 3) = -(denominator ^ 2) * taylor.c
  rw [taylorD, taylorE, taylorF, taylorA, taylorB, taylorC]
  constructor
  · calc
      3 * (3 * parameter * denominator) =
          9 * parameter * denominator := by ring1
      _ = 9 * parameter * (denominator ^ 2 * denominator⁻¹) := by
        rw [denominatorSquareInverse]
      _ = -(denominator ^ 2) * (-9 * parameter * denominator⁻¹) := by
        ring1
  · constructor
    · ring1
    · constructor
      · calc
          3 * (3 * parameter ^ 2 * denominator) =
              9 * parameter ^ 2 * denominator := by ring1
          _ = 9 * parameter ^ 2 *
              (denominator ^ 2 * denominator⁻¹) := by
            rw [denominatorSquareInverse]
          _ = -(denominator ^ 2) *
              (-9 * parameter ^ 2 * denominator⁻¹) := by ring1
      · constructor
        · calc
            3 * (9 * parameter ^ 2) = 27 * parameter ^ 2 := by ring1
            _ = 27 * parameter ^ 2 *
                (denominator ^ 2 * denominator⁻¹ ^ 2) := by
              rw [denominatorSquareInverseSquare]
              ring1
            _ = -(denominator ^ 2) *
                (-27 * parameter ^ 2 * denominator⁻¹ ^ 2) := by ring1
        · constructor
          · calc
              3 * (9 * parameter ^ 4) = 27 * parameter ^ 4 := by ring1
              _ = 27 * parameter ^ 4 *
                  (denominator ^ 2 * denominator⁻¹ ^ 2) := by
                rw [denominatorSquareInverseSquare]
                ring1
              _ = -(denominator ^ 2) *
                  (-27 * parameter ^ 4 * denominator⁻¹ ^ 2) := by ring1
          · calc
              3 * (9 * parameter ^ 3) = 27 * parameter ^ 3 := by ring1
              _ = 27 * parameter ^ 3 *
                  (denominator ^ 2 * denominator⁻¹ ^ 2) := by
                rw [denominatorSquareInverseSquare]
                ring1
              _ = -(denominator ^ 2) *
                  (-27 * parameter ^ 3 * denominator⁻¹ ^ 2) := by ring1

/-- At the singular parameter `t=0`, equation (19.6) is the pair of lines `xy=0`, up to the harmless nonzero coefficient
`-1`. -/
theorem tangentConic_at_zero [Nontrivial K]
    (oneNonzero : parameterDenominator (0 : K) ≠ 0) :
    let conic := tangentConic (0 : K) oneNonzero
    conic.d = 0 ∧ conic.e = -1 ∧ conic.f = 0 ∧
      conic.a = 0 ∧ conic.b = 0 ∧ conic.c = 0 ∧
      ∀ point : Plane.Point K, conic.evaluate point = -(point.x * point.y) := by
  dsimp only [tangentConic, parameterDenominator]
  refine ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1, ?_⟩
  intro point
  unfold Conic.evaluate
  ring1

/-- Exercise 19.4, first assertion: the tangent conic at parameter `t` passes through the point at parameter `u`
whenever `(tu)³=1`. -/
theorem tangentConic_contains_of_parameter_product_cube
  [Nontrivial K]
    (parameter reciprocalParameter : K)
    (parameterDenominatorNonzero : parameterDenominator parameter ≠
      0)
    (reciprocalDenominatorNonzero :
      parameterDenominator reciprocalParameter ≠ 0)
    (productCube : (parameter * reciprocalParameter) ^ 3 = 1) :
    (tangentConic parameter parameterDenominatorNonzero).Contains
      (parameterPoint reciprocalParameter) := by
  let denominator := parameterDenominator reciprocalParameter
  let quadratic :=
    27 * parameter * parameterDenominator parameter *
        reciprocalParameter ^ 2 -
      9 * parameterDenominator parameter ^ 2 *
        reciprocalParameter ^ 3 +
      27 * parameter ^ 2 * parameterDenominator parameter *
        reciprocalParameter ^ 4
  let linear :=
    -27 * parameter ^ 2 * reciprocalParameter -
      27 * parameter ^ 4 * reciprocalParameter ^ 2
  let constant := 9 * parameter ^ 3
  unfold Conic.Contains tangentConic Conic.evaluate
    parameterPoint
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    3 * parameter * parameterDenominator parameter *
              (-3 * reciprocalParameter *
                (parameterDenominator reciprocalParameter)⁻¹) ^ 2 +
            -parameterDenominator parameter ^ 2 *
                (-3 * reciprocalParameter *
                  (parameterDenominator reciprocalParameter)⁻¹) *
              (-3 * reciprocalParameter ^ 2 *
                (parameterDenominator reciprocalParameter)⁻¹) +
          3 * parameter ^ 2 * parameterDenominator parameter *
            (-3 * reciprocalParameter ^ 2 *
              (parameterDenominator reciprocalParameter)⁻¹) ^ 2 +
        9 * parameter ^ 2 *
          (-3 * reciprocalParameter *
            (parameterDenominator reciprocalParameter)⁻¹) +
      9 * parameter ^ 4 *
          (-3 * reciprocalParameter ^ 2 *
            (parameterDenominator reciprocalParameter)⁻¹) +
        9 * parameter ^ 3 =
      quadratic * denominator⁻¹ ^ 2 +
        linear * denominator⁻¹ + constant := by
      unfold quadratic linear constant denominator
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 :=
      Inverse.clear_quadratic_denominator reciprocalDenominatorNonzero
    _ = 0 := by
      have clearedZero :
          quadratic + linear * denominator + constant * denominator ^ 2 = 0 := by
        calc
          quadratic + linear * denominator + constant * denominator ^ 2 =
              9 * (1 - (parameter * reciprocalParameter) ^ 3) *
                (3 * parameter * reciprocalParameter ^ 2 -
                  reciprocalParameter ^ 3 + parameter ^ 3 -
                  3 * parameter ^ 2 * reciprocalParameter) := by
            unfold quadratic linear constant denominator parameterDenominator
            ring1
          _ = 0 := by rw [productCube]; ring1
      rw [clearedZero]
      ring1
end Folium

end Purelib.Curves.Plane.Folium.Tangent.Conic

end
