module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Tangent
import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Geometry.Conics.Parabola.Reflection
public import Purelib.Geometry.Conics.Parabola.Tangent
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 19 worked examples

This module begins with the translated-conic and tangent-line calculations in
Examples 19.1--19.4, then records the exact two-tangent identity and its
eleven-element-field instance from Exercise 19.2.
-/

namespace Purelib.Geometry.Conics.Parabola.Standard

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace ExampleNineteenFour

/-- The parabola `y²=4x`, displayed as `⟨0:0:1:-4:0:0⟩`. -/
def parabola [Nontrivial K] : Conic K
  where
  d := 0
  e := 0
  f := 1
  a := -4
  b := 0
  c := 0
  quadratic_nonzero := Or.inr (Or.inr one_ne_zero)

/-- The book's parametrized point `[t²,2t]`. -/
def point (parameter : K) : Geometry.Plane.Point
  K :=
  ⟨parameter ^ 2, 2 * parameter⟩

/-- The normalized tangent representative `⟨1:-t:t²⟩`. -/
def normalizedTangent [Nontrivial K] (parameter :
  K) : Geometry.Plane.Line K where
  a := 1
  b := -parameter
  c := parameter ^ 2
  direction_nonzero := Or.inl one_ne_zero

/-- Negating a nonzero four gives a nonzero field element. -/
private theorem negative_four_nonzero (fourNonzero
  : (4 : K) ≠ 0) :
    (-4 : K) ≠ 0 := by
  intro negativeZero
  apply fourNonzero
  calc
    (4 : K) = -(-4) := by ring1
    _ = 0 := by rw [negativeZero]; ring1

/-- Example 19.4: every displayed parameter point lies on `y²=4x`; the tangent formula is proportional to `⟨1:-t:t²⟩`.
-/
theorem example_19_4 [Nontrivial K]
    (parameter : K) (fourNonzero : (4 : K) ≠ 0) :
    let source := parabola (K := K)
    let basePoint := point parameter
    let nonSingular : source.IsNonSingularAt basePoint := by
      unfold Conic.IsNonSingularAt source basePoint parabola
        point
      left
      intro gradientZero
      apply negative_four_nonzero fourNonzero
      calc
        (-4 : K) = -4 + 2 * 0 * parameter ^ 2 + 0 * (2 * parameter) := by
          ring1
        _ = 0 := gradientZero
    let tangent := Conic.tangentLine source basePoint nonSingular
    source.Contains basePoint ∧
      tangent.Equivalent (normalizedTangent parameter) ∧
      tangent.Contains basePoint := by
  dsimp only
  let source := parabola (K := K)
  let basePoint := point parameter
  have onParabola : source.Contains basePoint := by
    unfold source basePoint parabola
      point Conic.Contains Conic.evaluate
    ring1
  have nonSingular : source.IsNonSingularAt basePoint := by
    unfold source basePoint parabola
      point Conic.IsNonSingularAt
    left
    intro gradientZero
    apply negative_four_nonzero fourNonzero
    calc
      (-4 : K) = -4 + 2 * 0 * parameter ^ 2 + 0 * (2 * parameter) := by
        ring1
      _ = 0 := gradientZero
  let tangent := Conic.tangentLine source basePoint nonSingular
  have tangentEquivalent : tangent.Equivalent (normalizedTangent
    parameter) := by
    unfold tangent source basePoint Conic.tangentLine parabola
      point
      normalizedTangent Geometry.Plane.Line.Equivalent
    exact ⟨by ring1, by ring1, by ring1⟩
  exact ⟨onParabola, tangentEquivalent,
    Conic.tangentLine_contains source basePoint onParabola nonSingular⟩

/-- Away from characteristic two, every point—not merely a parametrized one—lying on the displayed parabola is
first-order non-singular. -/
theorem every_point_nonSingular [Nontrivial K]
    (fourNonzero : (4 : K) ≠ 0) (candidate : Geometry.Plane.Point K)
    (_onParabola : (parabola (K := K)).Contains candidate) :
    (parabola (K := K)).IsNonSingularAt candidate := by
  unfold Conic.IsNonSingularAt parabola
  left
  intro gradientZero
  apply negative_four_nonzero fourNonzero
  calc
    (-4 : K) = -4 + 2 * 0 * candidate.x + 0 * candidate.y := by ring1
    _ = 0 := gradientZero

end ExampleNineteenFour

namespace ExerciseNineteenOne

/-- Focus `[a,0]` for the parabola `y²=4ax`. -/
def focus (parameter : K) : Geometry.Plane.Point
  K := ⟨parameter, 0⟩

/-- Directrix `x=-a`, displayed as `⟨1:0:a⟩`. -/
def directrix [Nontrivial K] (parameter : K) :
  Geometry.Plane.Line K where
  a := 1
  b := 0
  c := parameter
  direction_nonzero := Or.inl one_ne_zero

/-- The focus/directrix construction of `y²=4ax`. -/
def parabola [Nontrivial K] [DecidableEq K]
  (parameter : K) : Conic K :=
  Conic.parabolaConic (focus parameter)
    (directrix parameter)

/-- The standard directrix `x = -parameter` has nonzero normal norm. -/
theorem directrix_nonNull [Nontrivial K] (parameter
  : K) :
    ¬ (directrix parameter).IsNull := by
  intro nullLine
  unfold directrix Geometry.Plane.Line.IsNull at nullLine
  have oneEqualsZero : (1 : K) = 0 := by
    calc
      (1 : K) = 1 ^ 2 + 0 ^ 2 := by ring1
      _ = 0 := nullLine
  exact (one_ne_zero : (1 : K) ≠ 0) oneEqualsZero

/-- The standard focus lies off its directrix when two and the parameter are nonzero. -/
theorem focus_not_on_directrix [Nontrivial K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) :
    ¬ (directrix parameter).Contains
      (focus parameter) := by
  intro incidence
  have twiceParameterZero : 2 * parameter = 0 := by
    unfold directrix focus
      Geometry.Plane.Line.Contains at incidence
    calc
      2 * parameter = 1 * parameter + 0 * 0 + parameter := by ring1
      _ = 0 := incidence
  exact (Algebra.Field.ExplicitField.mul_ne_zero twoNonzero parameterNonzero)
    twiceParameterZero

/-- The standard focus and directrix present the parabola `y² = 4ax`.

Nonzero two and nonzero `a` retain the required focus/directrix separation. -/
theorem presentation [Nontrivial K] [DecidableEq K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) :
    (parabola parameter).IsParabolaPresentation
      (focus parameter)
        (directrix parameter) :=
  Conic.parabolaConic_isParabolaPresentation (focus parameter)
    (directrix parameter)
      (directrix_nonNull parameter)
    (focus_not_on_directrix parameter twoNonzero parameterNonzero)

/-- The focus/directrix construction expands to `y²-4ax=0`. -/
theorem parabola_coefficients [Nontrivial K]
  [DecidableEq K]
    (parameter : K) :
    let source := parabola parameter
    source.d = 0 ∧ source.e = 0 ∧ source.f = 1 ∧
      source.a = -4 * parameter ∧ source.b = 0 ∧ source.c = 0 := by
  dsimp only [parabola, Conic.parabolaConic,
    focus,
    directrix, Basic.lineNorm]
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Exercise 19.1: the direct focus/directrix specialization of the parabola reflection theorem for `y²=4ax`. -/
theorem exercise_19_1 [Nontrivial K] [DecidableEq
  K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) (basePoint : Geometry.Plane.Point K)
    (onParabola : (parabola parameter).Contains basePoint)
    (focusLineNonNull :
      ¬ (Incidence.lineThrough basePoint (focus parameter)
        (Conic.parabola_point_ne_focus (parabola parameter)
          (focus parameter) basePoint
            (directrix parameter)
          (presentation parameter twoNonzero parameterNonzero)
          onParabola)).IsNull) :
    let parabolaPresentation :=
      presentation parameter twoNonzero parameterNonzero
    let pointFocusDistinct :=
      Conic.parabola_point_ne_focus (parabola parameter)
        (focus parameter) basePoint
          (directrix parameter)
        parabolaPresentation onParabola
    let nonSingular :=
      Conic.parabola_nonSingularAt (parabola parameter)
        (focus parameter) basePoint
          (directrix parameter) twoNonzero
        parabolaPresentation
    let tangent :=
      Conic.tangentLine (parabola parameter) basePoint nonSingular
    let focusLine := Incidence.lineThrough basePoint (focus
      parameter) pointFocusDistinct
    let normalLine := Construction.altitudeThrough basePoint
      (directrix parameter)
    ∃ tangentNonNull : ¬ tangent.IsNull,
      ∃ normalLineNonNull : ¬ normalLine.IsNull,
        Spread.spread tangent focusLine tangentNonNull focusLineNonNull =
          Spread.spread tangent normalLine tangentNonNull normalLineNonNull := by
  exact Conic.parabola_reflection (parabola parameter)
    (focus parameter)
    basePoint (directrix parameter) twoNonzero
    (presentation parameter twoNonzero parameterNonzero)
      onParabola
    focusLineNonNull

end ExerciseNineteenOne

namespace ExerciseNineteenTwo

/-- The focus `[1,0]` of `y²=4x`. -/
def focus : Geometry.Plane.Point K := ⟨1, 0⟩

/-- The parameter point `[t²,2t]`. -/
def point (parameter : K) : Geometry.Plane.Point
  K :=
  ⟨parameter ^ 2, 2 * parameter⟩

/-- The tangent `⟨1:-t:t²⟩` at the parameter point. -/
def tangent [Nontrivial K] (parameter : K) :
  Geometry.Plane.Line K where
  a := 1
  b := -parameter
  c := parameter ^ 2
  direction_nonzero := Or.inl one_ne_zero

/-- The explicit intersection `[t₁t₂,t₁+t₂]` of two parameter tangents. -/
def tangentIntersection (firstParameter
  secondParameter : K) : Geometry.Plane.Point K :=
  ⟨firstParameter * secondParameter, firstParameter + secondParameter⟩

/-- Each normalized tangent contains its parameter point. -/
theorem tangent_contains_point [Nontrivial K]
  (parameter : K) :
    (Conics.Parabola.Standard.ExerciseNineteenTwo.tangent parameter).Contains
      (point parameter) := by
  unfold Conics.Parabola.Standard.ExerciseNineteenTwo.tangent point
    Geometry.Plane.Line.Contains
  ring1

/-- The explicit intersection lies on both displayed tangents. -/
theorem tangent_intersection
    [Nontrivial K]
    (firstParameter secondParameter : K) :
    (Conics.Parabola.Standard.ExerciseNineteenTwo.tangent firstParameter).Contains
        (tangentIntersection firstParameter secondParameter) ∧
      (Conics.Parabola.Standard.ExerciseNineteenTwo.tangent secondParameter).Contains
        (tangentIntersection firstParameter secondParameter) := by
  unfold Conics.Parabola.Standard.ExerciseNineteenTwo.tangent
    tangentIntersection Geometry.Plane.Line.Contains
  constructor <;> ring1

/-- Distinct parameters give genuinely distinct line proportions. -/
theorem tangents_not_equivalent
    [Nontrivial K]
    (firstParameter secondParameter : K)
    (parametersDistinct : firstParameter ≠ secondParameter) :
    ¬ (Conics.Parabola.Standard.ExerciseNineteenTwo.tangent firstParameter).Equivalent
      (Conics.Parabola.Standard.ExerciseNineteenTwo.tangent secondParameter) := by
  intro equivalent
  apply parametersDistinct
  have firstEquation := equivalent.1
  unfold Conics.Parabola.Standard.ExerciseNineteenTwo.tangent at firstEquation
  change (1 : K) * (-secondParameter) = 1 * (-firstParameter) at firstEquation
  have negativesEqual : -firstParameter = -secondParameter := by
    simpa only [one_mul] using firstEquation.symm
  calc
    firstParameter = -(-firstParameter) := by ring1
    _ = -(-secondParameter) := by rw [negativesEqual]
    _ = secondParameter := by ring1

/-- Relate tangent-intersection quadrances to focus quadrances on the standard parabola.

For any two parameters, the squared quadrance from either parabola point to the tangent intersection, multiplied by the
other point's focus quadrance, gives the same value (Exercise 19.2). -/
theorem exercise_19_2
    (firstParameter secondParameter : K) :
    Quadrance.quadrance (point firstParameter)
          (tangentIntersection firstParameter secondParameter) ^ 2 *
        Quadrance.quadrance (point secondParameter)
          focus =
      Quadrance.quadrance (point secondParameter)
          (tangentIntersection firstParameter secondParameter) ^ 2 *
        Quadrance.quadrance (point firstParameter)
          focus := by
  unfold point
    tangentIntersection focus
    Quadrance.quadrance
  ring1

end ExerciseNineteenTwo

end

end Purelib.Geometry.Conics.Parabola.Standard

end
