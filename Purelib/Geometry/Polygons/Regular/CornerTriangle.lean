module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Null
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Reflection.Point
import Purelib.Geometry.Triangles.Isosceles.Numeric
import Purelib.Geometry.Triangles.Trigonometry.Spread
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Null

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

namespace Purelib.Geometry.Polygons.Regular.CornerTriangle

variable {K : Type*} [ExplicitField K]

/-- The finite scalar calculation at the heart of Theorem 98. The reflection part of the geometric theorem supplies the
two quadrance formulas, while the ordinary Spread law and Equal spreads theorem supply the three spread inputs. -/
theorem polygon_triangle_scalars
    (q r d value baseFirst apex baseThird : K)
    (qNonzero : q ≠ 0) (rNonzero : r ≠ 0) (dNonzero : d ≠ 0)
    (valueNonzero : value ≠ 0) (baseFirstNonzero : baseFirst ≠ 0)
    (apexNonzero : apex ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (sideValue : r = 4 * value * q)
    (diagonalValue : d = 16 * value * (1 - value) * q)
    (firstSpreadLaw : baseFirst / r = apex / d)
    (secondSpreadLaw : apex / d = baseThird / r)
    (equalSpreadAlternatives :
      apex = 0 ∨ apex = 4 * baseFirst * (1 - baseFirst)) :
    r = 4 * value * q ∧
      d = 16 * value * (1 - value) * q ∧
      baseFirst = value ∧ baseThird = value ∧
      apex = 4 * value * (1 - value) := by
  have baseSpreadsEqual : baseFirst = baseThird := by
    calc
      baseFirst = (baseFirst / r) * r :=
        (ExplicitField.div_mul_cancel baseFirst rNonzero).symm
      _ = (baseThird / r) * r := by rw [firstSpreadLaw, secondSpreadLaw]
      _ = baseThird := ExplicitField.div_mul_cancel baseThird rNonzero
  have apexLogistic : apex = 4 * baseFirst * (1 - baseFirst) := by
    rcases equalSpreadAlternatives with apexZero | logistic
    · exact False.elim (apexNonzero apexZero)
    · exact logistic
  have diagonalFromBase :=
    (Triangles.Isosceles.Numeric.isosceles_triangle r d baseFirst apex rNonzero dNonzero
      baseFirstNonzero twoNonzero firstSpreadLaw apexLogistic).1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    have sixteenAsProduct : (16 : K) = 4 * 4 := by ring1
    rw [sixteenAsProduct]
    exact ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have cancellationNonzero : (16 : K) * value * q ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero sixteenNonzero valueNonzero) qNonzero
  have complementsEqual : 1 - baseFirst = 1 - value := by
    apply ExplicitField.eq_of_mul_eq_mul_left cancellationNonzero
    calc
      (16 * value * q) * (1 - baseFirst) = d := by
        rw [diagonalFromBase, sideValue]
        ring1
      _ = (16 * value * q) * (1 - value) := by
        rw [diagonalValue]
        ring1
  have baseFirstValue : baseFirst = value := by
    calc
      baseFirst = 1 - (1 - baseFirst) := by ring1
      _ = 1 - (1 - value) := by rw [complementsEqual]
      _ = value := by ring1
  exact ⟨sideValue, diagonalValue, baseFirstValue,
    baseSpreadsEqual.symm.trans baseFirstValue, by
      rw [apexLogistic, baseFirstValue]⟩

set_option genInjectivity false in
/-- The finite three-vertex window used in the proof of Theorem 98. `second` is the reflection of `first` in the first
intervening star line; `third` is obtained by the next reflection, and also by reflecting `first` in the middle radial
line. -/
structure PolygonTriangleConfiguration (K : Type*)
  [Algebra.Field.ExplicitField K]
    [DecidableEq K] (value : K) where
  /-- The common center of the three radii. -/ center : Plane.Point K
  /-- The first vertex of the corner triangle. -/ first : Plane.Point K
  /-- The middle vertex of the corner triangle. -/ second : Plane.Point K
  /-- The third vertex of the corner triangle. -/ third : Plane.Point K
  /-- The first radius has distinct endpoints. -/ centerFirstDistinct : center ≠ first
  /-- The second radius has distinct endpoints. -/ centerSecondDistinct : center ≠ second
  /-- The third radius has distinct endpoints. -/ centerThirdDistinct : center ≠ third
  /-- The first side has distinct endpoints. -/ firstSecondDistinct : first ≠ second
  /-- The diagonal has distinct endpoints. -/ firstThirdDistinct : first ≠ third
  /-- The second side has distinct endpoints. -/ secondThirdDistinct : second ≠ third
  /-- The line of the first radius is non-null. -/ centerFirstNonNull :
    ¬ (Incidence.lineThrough center first centerFirstDistinct).IsNull
  /-- The line of the second radius is non-null. -/ centerSecondNonNull :
    ¬ (Incidence.lineThrough center second centerSecondDistinct).IsNull
  /-- The line of the third radius is non-null. -/ centerThirdNonNull :
    ¬ (Incidence.lineThrough center third centerThirdDistinct).IsNull
  /-- The line of the first side is non-null. -/ firstSecondNonNull :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull
  /-- The diagonal line is non-null. -/ firstThirdNonNull :
    ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull
  /-- The line of the second side is non-null. -/ secondThirdNonNull :
    ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull
  /-- The mirror taking the first vertex to the second. -/ firstMirror : Plane.Line K
  /-- The mirror taking the second vertex to the third. -/ secondMirror : Plane.Line K
  /-- The first reflection mirror is non-null. -/ firstMirrorNonNull : ¬ firstMirror.IsNull
  /-- The second reflection mirror is non-null. -/ secondMirrorNonNull : ¬ secondMirror.IsNull
  /-- The first mirror passes through the center. -/ centerOnFirstMirror : firstMirror.Contains center
  /-- The second mirror passes through the center. -/ centerOnSecondMirror : secondMirror.Contains center
  /-- Reflecting the first vertex in the first mirror gives the second. -/ secondReflection :
    second = Reflection.Point.reflectPoint firstMirror firstMirrorNonNull first
  /-- Reflecting the second vertex in the second mirror gives the third. -/ thirdReflection :
    third = Reflection.Point.reflectPoint secondMirror secondMirrorNonNull second
  /-- Reflection in the middle radial line exchanges the outer vertices. -/ diagonalReflection :
    third = Reflection.Point.reflectPoint
      (Incidence.lineThrough center second centerSecondDistinct)
      centerSecondNonNull first
  /-- The first radius and its mirror have the prescribed spread. -/ firstMirrorSpread :
    Spread.spread (Incidence.lineThrough center first centerFirstDistinct) firstMirror
      centerFirstNonNull firstMirrorNonNull = value
  /-- The second radius and its mirror have the prescribed spread. -/ secondMirrorSpread :
    Spread.spread (Incidence.lineThrough center second centerSecondDistinct) secondMirror
      centerSecondNonNull secondMirrorNonNull = value
  /-- The first two radii have spread four times the value times its complement. -/ doubleRadialSpread :
    Spread.spread (Incidence.lineThrough center first centerFirstDistinct)
        (Incidence.lineThrough center second centerSecondDistinct)
        centerFirstNonNull centerSecondNonNull =
      4 * value * (1 - value)
  /-- The first and second radii have equal quadrance. -/ secondRadius : Quadrance.quadrance center second =
    Quadrance.quadrance center first
  /-- The first and third radii have equal quadrance. -/ thirdRadius : Quadrance.quadrance center third =
    Quadrance.quadrance center first
  /-- The sides at the first corner are not parallel. -/ firstCornerNonparallel :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).Parallel
      (Incidence.lineThrough first third firstThirdDistinct)
  /-- The sides at the middle corner are not parallel. -/ middleCornerNonparallel :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).Parallel
      (Incidence.lineThrough second third secondThirdDistinct)

constructive_injectivity PolygonTriangleConfiguration

/-- Theorem 98 (Polygon triangle): the two successive sides have quadrance `4sQ`, the short diagonal has quadrance
`16s(1-s)Q`, the two base spreads are `s`, and the remaining spread is `4s(1-s)`. -/
theorem polygon_triangle [Nontrivial K] [DecidableEq K]
    (value : K) (valueNonzero : value ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (configuration : PolygonTriangleConfiguration K value) :
    Quadrance.quadrance configuration.first configuration.second =
        4 * value * Quadrance.quadrance configuration.center configuration.first ∧
      Quadrance.quadrance configuration.second configuration.third =
        4 * value * Quadrance.quadrance configuration.center configuration.first ∧
      Quadrance.quadrance configuration.first configuration.third =
        16 * value * (1 - value) *
          Quadrance.quadrance configuration.center configuration.first ∧
      Spread.spread
          (Incidence.lineThrough configuration.first configuration.second
            configuration.firstSecondDistinct)
          (Incidence.lineThrough configuration.first configuration.third
            configuration.firstThirdDistinct)
          configuration.firstSecondNonNull
          configuration.firstThirdNonNull = value ∧
      Spread.spread
          (Incidence.lineThrough configuration.first configuration.third
            configuration.firstThirdDistinct)
          (Incidence.lineThrough configuration.second configuration.third
            configuration.secondThirdDistinct)
          configuration.firstThirdNonNull
          configuration.secondThirdNonNull = value ∧
      Spread.spread
          (Incidence.lineThrough configuration.first configuration.second
            configuration.firstSecondDistinct)
          (Incidence.lineThrough configuration.second configuration.third
            configuration.secondThirdDistinct)
          configuration.firstSecondNonNull
          configuration.secondThirdNonNull =
        4 * value * (1 - value) := by
  let q := Quadrance.quadrance configuration.center configuration.first
  let r := Quadrance.quadrance configuration.first configuration.second
  let d := Quadrance.quadrance configuration.first configuration.third
  let firstSide := Incidence.lineThrough configuration.first configuration.second
    configuration.firstSecondDistinct
  let diagonal := Incidence.lineThrough configuration.first configuration.third
    configuration.firstThirdDistinct
  let secondSide := Incidence.lineThrough configuration.second configuration.third
    configuration.secondThirdDistinct
  let baseFirst := Spread.spread firstSide diagonal
    configuration.firstSecondNonNull configuration.firstThirdNonNull
  let apex := Spread.spread firstSide secondSide
    configuration.firstSecondNonNull configuration.secondThirdNonNull
  let baseThird := Spread.spread diagonal secondSide
    configuration.firstThirdNonNull configuration.secondThirdNonNull
  have qNonzero : q ≠ 0 := by
    unfold q
    exact TriangleRatios.quadrance_ne_zero_of_line_nonNull configuration.center
      configuration.first configuration.centerFirstDistinct
      configuration.centerFirstNonNull
  have rNonzero : r ≠ 0 := by
    unfold r
    exact TriangleRatios.quadrance_ne_zero_of_line_nonNull configuration.first
      configuration.second configuration.firstSecondDistinct
      configuration.firstSecondNonNull
  have dNonzero : d ≠ 0 := by
    unfold d
    exact TriangleRatios.quadrance_ne_zero_of_line_nonNull configuration.first
      configuration.third configuration.firstThirdDistinct
      configuration.firstThirdNonNull
  have baseFirstNonzero : baseFirst ≠ 0 := by
    intro spreadZero
    apply configuration.firstCornerNonparallel
    exact (Spread.spread_eq_zero_iff_parallel firstSide diagonal
      configuration.firstSecondNonNull
      configuration.firstThirdNonNull).1 spreadZero
  have apexNonzero : apex ≠ 0 := by
    intro spreadZero
    apply configuration.middleCornerNonparallel
    exact (Spread.spread_eq_zero_iff_parallel firstSide secondSide
      configuration.firstSecondNonNull
      configuration.secondThirdNonNull).1 spreadZero
  have firstSideValue : r = 4 * value * q := by
    unfold r q
    calc
      Quadrance.quadrance configuration.first configuration.second =
          Quadrance.quadrance configuration.first
            (Reflection.Point.reflectPoint configuration.firstMirror
              configuration.firstMirrorNonNull configuration.first) := by
        rw [configuration.secondReflection]
      _ = 4 * Spread.spread
            (Incidence.lineThrough configuration.center configuration.first
              configuration.centerFirstDistinct)
            configuration.firstMirror configuration.centerFirstNonNull
            configuration.firstMirrorNonNull *
          Quadrance.quadrance configuration.center configuration.first :=
        Reflection.Point.reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.first configuration.centerFirstDistinct
          configuration.centerFirstNonNull configuration.firstMirror
          configuration.firstMirrorNonNull configuration.centerOnFirstMirror
      _ = 4 * value *
          Quadrance.quadrance configuration.center configuration.first := by
        rw [configuration.firstMirrorSpread]
  have secondSideValue :
      Quadrance.quadrance configuration.second configuration.third = 4 * value * q := by
    unfold q
    calc
      Quadrance.quadrance configuration.second configuration.third =
          Quadrance.quadrance configuration.second
            (Reflection.Point.reflectPoint configuration.secondMirror
              configuration.secondMirrorNonNull configuration.second) := by
        rw [configuration.thirdReflection]
      _ = 4 * Spread.spread
            (Incidence.lineThrough configuration.center configuration.second
              configuration.centerSecondDistinct)
            configuration.secondMirror configuration.centerSecondNonNull
            configuration.secondMirrorNonNull *
          Quadrance.quadrance configuration.center configuration.second :=
        Reflection.Point.reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.second configuration.centerSecondDistinct
          configuration.centerSecondNonNull configuration.secondMirror
          configuration.secondMirrorNonNull configuration.centerOnSecondMirror
      _ = 4 * value * Quadrance.quadrance configuration.center configuration.first := by
        rw [configuration.secondMirrorSpread, configuration.secondRadius]
  have diagonalValue : d = 16 * value * (1 - value) * q := by
    unfold d q
    calc
      Quadrance.quadrance configuration.first configuration.third =
          Quadrance.quadrance configuration.first
            (Reflection.Point.reflectPoint
              (Incidence.lineThrough configuration.center configuration.second
                configuration.centerSecondDistinct)
              configuration.centerSecondNonNull configuration.first) := by
        rw [configuration.diagonalReflection]
      _ = 4 * Spread.spread
            (Incidence.lineThrough configuration.center configuration.first
              configuration.centerFirstDistinct)
            (Incidence.lineThrough configuration.center configuration.second
              configuration.centerSecondDistinct)
            configuration.centerFirstNonNull
            configuration.centerSecondNonNull *
          Quadrance.quadrance configuration.center configuration.first :=
        Reflection.Point.reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.first configuration.centerFirstDistinct
          configuration.centerFirstNonNull
          (Incidence.lineThrough configuration.center configuration.second
            configuration.centerSecondDistinct)
          configuration.centerSecondNonNull
          (Incidence.lineThrough_contains_first configuration.center configuration.second
            configuration.centerSecondDistinct)
      _ = 16 * value * (1 - value) *
          Quadrance.quadrance configuration.center configuration.first := by
        rw [configuration.doubleRadialSpread]
        ring1
  have sideQuadrancesEqual :
      Quadrance.quadrance configuration.second configuration.third = r := by
    calc
      Quadrance.quadrance configuration.second configuration.third = 4 * value * q :=
        secondSideValue
      _ = r := firstSideValue.symm
  let reversedFirstSideNonNull := Line.Null.reversedLine_nonNull
    configuration.first configuration.second
    configuration.firstSecondDistinct configuration.firstSecondNonNull
  let reversedDiagonalNonNull := Line.Null.reversedLine_nonNull
    configuration.first configuration.third configuration.firstThirdDistinct
    configuration.firstThirdNonNull
  let reversedSecondSideNonNull := Line.Null.reversedLine_nonNull
    configuration.second configuration.third
    configuration.secondThirdDistinct configuration.secondThirdNonNull
  have apexCanonical :
      Spread.spread
          (Incidence.lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull = apex := by
    unfold apex firstSide
    exact Spread.spread_eq_of_parallel_pairs
      (Incidence.lineThrough configuration.second configuration.first
        configuration.firstSecondDistinct.symm)
      secondSide
      (Incidence.lineThrough configuration.first configuration.second
        configuration.firstSecondDistinct)
      secondSide reversedFirstSideNonNull configuration.secondThirdNonNull
      configuration.firstSecondNonNull configuration.secondThirdNonNull
      (Plane.Line.parallel_symm (Line.Relations.lineThrough_reverse_parallel
        configuration.first configuration.second
        configuration.firstSecondDistinct))
      (Plane.Line.parallel_refl secondSide)
  have baseThirdCanonical :
      Spread.spread
          (Incidence.lineThrough configuration.third configuration.first
            configuration.firstThirdDistinct.symm)
          (Incidence.lineThrough configuration.third configuration.second
            configuration.secondThirdDistinct.symm)
          reversedDiagonalNonNull reversedSecondSideNonNull = baseThird := by
    unfold baseThird diagonal secondSide
    exact Spread.spread_eq_of_parallel_pairs
      (Incidence.lineThrough configuration.third configuration.first
        configuration.firstThirdDistinct.symm)
      (Incidence.lineThrough configuration.third configuration.second
        configuration.secondThirdDistinct.symm)
      (Incidence.lineThrough configuration.first configuration.third
        configuration.firstThirdDistinct)
      (Incidence.lineThrough configuration.second configuration.third
        configuration.secondThirdDistinct)
      reversedDiagonalNonNull reversedSecondSideNonNull
      configuration.firstThirdNonNull configuration.secondThirdNonNull
      (Plane.Line.parallel_symm (Line.Relations.lineThrough_reverse_parallel
        configuration.first configuration.third
        configuration.firstThirdDistinct))
      (Plane.Line.parallel_symm (Line.Relations.lineThrough_reverse_parallel
        configuration.second configuration.third
        configuration.secondThirdDistinct))
  have spreadLaws := Triangles.Trigonometry.Spread.spread_law configuration.first configuration.second
    configuration.third configuration.firstSecondDistinct
    configuration.firstThirdDistinct configuration.secondThirdDistinct
    configuration.firstSecondNonNull configuration.firstThirdNonNull
    configuration.secondThirdNonNull twoNonzero
  have firstSpreadLaw : baseFirst / r = apex / d := by
    have law := spreadLaws.1
    rw [sideQuadrancesEqual] at law
    change baseFirst / r =
      Spread.spread
          (Incidence.lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull / d at law
    rw [apexCanonical] at law
    exact law
  have secondSpreadLaw : apex / d = baseThird / r := by
    have law := spreadLaws.2
    change
      Spread.spread
          (Incidence.lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull / d =
        Spread.spread
          (Incidence.lineThrough configuration.third configuration.first
            configuration.firstThirdDistinct.symm)
          (Incidence.lineThrough configuration.third configuration.second
            configuration.secondThirdDistinct.symm)
          reversedDiagonalNonNull reversedSecondSideNonNull / r at law
    rw [apexCanonical, baseThirdCanonical] at law
    exact law
  have baseSpreadsEqual : baseFirst = baseThird := by
    calc
      baseFirst = (baseFirst / r) * r :=
        (ExplicitField.div_mul_cancel baseFirst rNonzero).symm
      _ = (baseThird / r) * r := by rw [firstSpreadLaw, secondSpreadLaw]
      _ = baseThird := ExplicitField.div_mul_cancel baseThird rNonzero
  have equalSpreadAlternatives :
      apex = 0 ∨ apex = 4 * baseFirst * (1 - baseFirst) := by
    have alternatives := Triple.equal_spreads firstSide diagonal secondSide
      configuration.firstSecondNonNull configuration.firstThirdNonNull
      configuration.secondThirdNonNull baseSpreadsEqual
    exact alternatives
  have scalarConclusion := polygon_triangle_scalars q r d value baseFirst apex
    baseThird qNonzero rNonzero dNonzero valueNonzero baseFirstNonzero
    apexNonzero twoNonzero firstSideValue diagonalValue firstSpreadLaw
    secondSpreadLaw equalSpreadAlternatives
  rcases scalarConclusion with
    ⟨sideFormula, diagonalFormula, firstSpreadValue,
      thirdSpreadValue, apexSpreadValue⟩
  exact ⟨sideFormula, secondSideValue, diagonalFormula,
    firstSpreadValue, thirdSpreadValue, apexSpreadValue⟩
end Purelib.Geometry.Polygons.Regular.CornerTriangle

end
