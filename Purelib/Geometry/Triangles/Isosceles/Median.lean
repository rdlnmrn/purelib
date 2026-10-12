module

import Purelib.Algebra.Field.Midpoint
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Right.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: the isosceles median

The line in Theorem 67 is represented by its vertex and its displayed
intersection with the opposite side.  This keeps all three conditions—altitude,
median, and equal-spread vertex bisector—finite and executable.
-/

namespace Purelib.Geometry.Triangles.Isosceles.Median

variable {K : Type*} [ExplicitField K]

/-- In an isosceles triangle, a displayed cevian is perpendicular to the base exactly when its intersection with the
base is the midpoint. This is the altitude/median half of Theorem 67. -/
theorem isosceles_altitude_iff_midpoint [DecidableEq K]
    (first second vertex foot : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (footOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      Quadrance.quadrance vertex first = Quadrance.quadrance vertex second) :
    (Incidence.lineThrough vertex foot vertexFootDistinct).Perpendicular
        (Incidence.lineThrough first second firstSecondDistinct) ↔
      foot = Affine.midpoint first second := by
  let base := Incidence.lineThrough first second firstSecondDistinct
  let cevian := Incidence.lineThrough vertex foot vertexFootDistinct
  have baseContainsFirst : base.Contains first := by
    unfold base
    exact Incidence.lineThrough_contains_first first second firstSecondDistinct
  have baseContainsSecond : base.Contains second := by
    unfold base
    exact Incidence.lineThrough_contains_second first second firstSecondDistinct
  constructor
  · intro perpendicular
    have firstPythagoras :
        Quadrance.quadrance vertex foot + Quadrance.quadrance first foot =
          Quadrance.quadrance first vertex := by
      by_cases footIsFirst : foot = first
      · subst foot
        rw [Quadrance.quadrance_self, add_zero, Quadrance.quadrance_symm vertex first]
      · have firstFootDistinct : first ≠ foot := by
          intro equalPoints
          exact footIsFirst equalPoints.symm
        have firstFootParallel :
            (Incidence.lineThrough first foot firstFootDistinct).Parallel base :=
          Incidence.lineThrough_parallel_of_contains base first foot firstFootDistinct
            baseContainsFirst footOnBase
        have firstFootPerpendicular :
            (Incidence.lineThrough first foot firstFootDistinct).Perpendicular cevian :=
          Relations.perpendicular_of_parallel_left base
            (Incidence.lineThrough first foot firstFootDistinct) cevian
            (Plane.Line.parallel_symm firstFootParallel)
            (Plane.Line.perpendicular_symm perpendicular)
        exact (Right.Quadrance.pythagoras_iff_perpendicular first vertex foot
          firstFootDistinct vertexFootDistinct twoNonzero).2
            firstFootPerpendicular
    have secondPythagoras :
        Quadrance.quadrance vertex foot + Quadrance.quadrance second foot =
          Quadrance.quadrance second vertex := by
      by_cases footIsSecond : foot = second
      · subst foot
        rw [Quadrance.quadrance_self, add_zero, Quadrance.quadrance_symm vertex second]
      · have secondFootDistinct : second ≠ foot := by
          intro equalPoints
          exact footIsSecond equalPoints.symm
        have secondFootParallel :
            (Incidence.lineThrough second foot secondFootDistinct).Parallel base :=
          Incidence.lineThrough_parallel_of_contains base second foot secondFootDistinct
            baseContainsSecond footOnBase
        have secondFootPerpendicular :
            (Incidence.lineThrough second foot secondFootDistinct).Perpendicular cevian :=
          Relations.perpendicular_of_parallel_left base
            (Incidence.lineThrough second foot secondFootDistinct) cevian
            (Plane.Line.parallel_symm secondFootParallel)
            (Plane.Line.perpendicular_symm perpendicular)
        exact (Right.Quadrance.pythagoras_iff_perpendicular second vertex foot
          secondFootDistinct vertexFootDistinct twoNonzero).2
            secondFootPerpendicular
    have equalReversedVertexQuadrances :
        Quadrance.quadrance first vertex = Quadrance.quadrance second vertex := by
      calc
        Quadrance.quadrance first vertex = Quadrance.quadrance vertex first :=
          Quadrance.quadrance_symm first vertex
        _ = Quadrance.quadrance vertex second := equalVertexQuadrances
        _ = Quadrance.quadrance second vertex := Quadrance.quadrance_symm vertex second
    have equalFootQuadrances :
        Quadrance.quadrance foot first = Quadrance.quadrance foot second := by
      calc
        Quadrance.quadrance foot first = Quadrance.quadrance first foot :=
          Quadrance.quadrance_symm foot first
        _ = Quadrance.quadrance first vertex - Quadrance.quadrance vertex foot := by
          rw [← firstPythagoras]
          ring1
        _ = Quadrance.quadrance second vertex - Quadrance.quadrance vertex foot := by
          rw [equalReversedVertexQuadrances]
        _ = Quadrance.quadrance second foot := by
          rw [← secondPythagoras]
          ring1
        _ = Quadrance.quadrance foot second := Quadrance.quadrance_symm second foot
    exact Quadrance.midpoint_unique_of_equal_quadrance first second foot
      firstSecondDistinct twoNonzero baseNonNull footOnBase
      equalFootQuadrances
  · intro footIsMidpoint
    subst foot
    have vertexOnBisector :
        (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct).Contains
          vertex :=
      (PerpendicularBisector.equal_quadrance_iff_perpendicularBisector_contains first second vertex
        firstSecondDistinct twoNonzero).1 equalVertexQuadrances
    have midpointOnBisector :
        (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct).Contains
          (Affine.midpoint first second) :=
      PerpendicularBisector.perpendicularBisector_contains_midpoint first second firstSecondDistinct
    have cevianParallelBisector :
        (Incidence.lineThrough vertex (Affine.midpoint first second)
          vertexFootDistinct).Parallel
            (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct) :=
      Incidence.lineThrough_parallel_of_contains
        (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct)
        vertex (Affine.midpoint first second) vertexFootDistinct
        vertexOnBisector midpointOnBisector
    exact Relations.perpendicular_of_parallel_left
      (PerpendicularBisector.perpendicularBisector first second firstSecondDistinct)
      (Incidence.lineThrough vertex (Affine.midpoint first second) vertexFootDistinct)
      (Incidence.lineThrough first second firstSecondDistinct)
      (Plane.Line.parallel_symm cevianParallelBisector)
      (PerpendicularBisector.perpendicularBisector_perpendicular first second firstSecondDistinct)

/-- The median of an isosceles triangle makes equal spreads with its two equal sides. -/
theorem isosceles_midpoint_equal_spreads [DecidableEq K]
    (first second vertex : Plane.Point K)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexMidpointDistinct : vertex ≠ Affine.midpoint first second)
    (sideFirstNonNull :
      ¬ (Incidence.lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (Incidence.lineThrough vertex second vertexSecondDistinct).IsNull)
    (medianNonNull :
      ¬ (Incidence.lineThrough vertex (Affine.midpoint first second)
        vertexMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalVertexQuadrances :
      Quadrance.quadrance vertex first = Quadrance.quadrance vertex second) :
    Spread.spread (Incidence.lineThrough vertex first vertexFirstDistinct)
        (Incidence.lineThrough vertex (Affine.midpoint first second) vertexMidpointDistinct)
        sideFirstNonNull medianNonNull =
      Spread.spread (Incidence.lineThrough vertex second vertexSecondDistinct)
        (Incidence.lineThrough vertex (Affine.midpoint first second) vertexMidpointDistinct)
        sideSecondNonNull medianNonNull := by
  have determinantOpposite :
      (Incidence.lineThrough vertex first vertexFirstDistinct).a *
          (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).b -
        (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).a *
          (Incidence.lineThrough vertex first vertexFirstDistinct).b =
      -((Incidence.lineThrough vertex second vertexSecondDistinct).a *
          (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).b -
        (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).a *
          (Incidence.lineThrough vertex second vertexSecondDistinct).b) := by
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    unfold Incidence.lineThrough Affine.midpoint
    calc
      ((vertex.y - first.y) *
            ((first.x + second.x) / 2 - vertex.x) -
          (vertex.y - (first.y + second.y) / 2) *
            (first.x - vertex.x)) * 2 =
        (vertex.y - first.y) *
            (((first.x + second.x) / 2 - vertex.x) * 2) -
          ((vertex.y - (first.y + second.y) / 2) * 2) *
            (first.x - vertex.x) := by ring1
      _ = (vertex.y - first.y) *
            (first.x + second.x - 2 * vertex.x) -
          (2 * vertex.y - first.y - second.y) *
            (first.x - vertex.x) := by
        rw [Purelib.Algebra.Field.Midpoint.half_sum_sub_target_mul_two first.x second.x vertex.x
          twoNonzero,
          Purelib.Algebra.Field.Midpoint.target_sub_half_sum_mul_two first.y second.y vertex.y
            twoNonzero]
      _ = -((vertex.y - second.y) *
            (first.x + second.x - 2 * vertex.x) -
          (2 * vertex.y - first.y - second.y) *
            (second.x - vertex.x)) := by ring1
      _ = (-((vertex.y - second.y) *
            ((first.x + second.x) / 2 - vertex.x) -
          (vertex.y - (first.y + second.y) / 2) *
            (second.x - vertex.x))) * 2 := by
        rw [show
            (first.x + second.x - 2 * vertex.x) =
              ((first.x + second.x) / 2 - vertex.x) * 2 by
          exact (Purelib.Algebra.Field.Midpoint.half_sum_sub_target_mul_two first.x second.x vertex.x
            twoNonzero).symm,
          show
            (2 * vertex.y - first.y - second.y) =
              (vertex.y - (first.y + second.y) / 2) * 2 by
          exact (Purelib.Algebra.Field.Midpoint.target_sub_half_sum_mul_two first.y second.y vertex.y
            twoNonzero).symm]
        ring1
  unfold Spread.spread
  rw [show
      ((Incidence.lineThrough vertex first vertexFirstDistinct).a *
          (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).b -
        (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).a *
          (Incidence.lineThrough vertex first vertexFirstDistinct).b) ^ 2 =
      ((Incidence.lineThrough vertex second vertexSecondDistinct).a *
          (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).b -
        (Incidence.lineThrough vertex (Affine.midpoint first second)
            vertexMidpointDistinct).a *
          (Incidence.lineThrough vertex second vertexSecondDistinct).b) ^ 2 by
        rw [determinantOpposite]
        ring1]
  rw [Quadrance.lineThrough_norm_eq_quadrance vertex first vertexFirstDistinct,
    Quadrance.lineThrough_norm_eq_quadrance vertex second vertexSecondDistinct,
    equalVertexQuadrances]

/-- A cevian of a noncollinear isosceles triangle is an equal-spread vertex bisector exactly when it meets the opposite
side at its midpoint. -/
theorem isosceles_bisector_iff_midpoint [Nontrivial K] [DecidableEq
  K]
    (first second vertex foot : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (sideFirstNonNull :
      ¬ (Incidence.lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (Incidence.lineThrough vertex second vertexSecondDistinct).IsNull)
    (cevianNonNull :
      ¬ (Incidence.lineThrough vertex foot vertexFootDistinct).IsNull)
    (notCollinear : ¬ Incidence.Collinear first second vertex)
    (footOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      Quadrance.quadrance vertex first = Quadrance.quadrance vertex second) :
    Spread.spread (Incidence.lineThrough vertex first vertexFirstDistinct)
        (Incidence.lineThrough vertex foot vertexFootDistinct)
        sideFirstNonNull cevianNonNull =
      Spread.spread (Incidence.lineThrough vertex second vertexSecondDistinct)
        (Incidence.lineThrough vertex foot vertexFootDistinct)
        sideSecondNonNull cevianNonNull ↔
      foot = Affine.midpoint first second := by
  let sideFirst := Incidence.lineThrough vertex first vertexFirstDistinct
  let sideSecond := Incidence.lineThrough vertex second vertexSecondDistinct
  let cevian := Incidence.lineThrough vertex foot vertexFootDistinct
  let dFirst := sideFirst.a * cevian.b - cevian.a * sideFirst.b
  let dSecond := sideSecond.a * cevian.b - cevian.a * sideSecond.b
  have determinantNonzero : Incidence.pointDeterminant first second vertex ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((Incidence.collinear_iff_pointDeterminant_eq_zero first second vertex).2
        determinantZero)
  constructor
  · intro equalSpreads
    have sideNormEqual : Line.Basic.lineNorm sideFirst = Line.Basic.lineNorm sideSecond := by
      unfold sideFirst sideSecond
      rw [Quadrance.lineThrough_norm_eq_quadrance vertex first vertexFirstDistinct,
        Quadrance.lineThrough_norm_eq_quadrance vertex second vertexSecondDistinct,
        equalVertexQuadrances]
    have commonDenominatorNonzero :
        Line.Basic.lineNorm sideSecond * Line.Basic.lineNorm cevian ≠ 0 :=
      ExplicitField.mul_ne_zero sideSecondNonNull cevianNonNull
    have equalNumeratorSquares : dFirst ^ 2 = dSecond ^ 2 := by
      unfold Spread.spread at equalSpreads
      change dFirst ^ 2 / (Line.Basic.lineNorm sideFirst * Line.Basic.lineNorm cevian) =
        dSecond ^ 2 / (Line.Basic.lineNorm sideSecond * Line.Basic.lineNorm cevian) at equalSpreads
      rw [sideNormEqual] at equalSpreads
      have cleared := congrArg
        (fun value : K => value * (Line.Basic.lineNorm sideSecond * Line.Basic.lineNorm cevian))
        equalSpreads
      rw [ExplicitField.div_mul_cancel _ commonDenominatorNonzero,
        ExplicitField.div_mul_cancel _ commonDenominatorNonzero]
        at cleared
      exact cleared
    have factorZero : (dFirst - dSecond) * (dFirst + dSecond) = 0 := by
      calc
        (dFirst - dSecond) * (dFirst + dSecond) =
            dFirst ^ 2 - dSecond ^ 2 := by ring1
        _ = 0 := by rw [equalNumeratorSquares]; ring1
    have footOnBaseExpanded :
        (first.y - second.y) * foot.x +
            (second.x - first.x) * foot.y +
            (first.x * second.y - second.x * first.y) = 0 := by
      exact footOnBase
    have determinantDifference :
        dFirst - dSecond = Incidence.pointDeterminant first second vertex := by
      unfold dFirst dSecond sideFirst sideSecond cevian
      simp only [Incidence.lineThrough_a, Incidence.lineThrough_b]
      calc
        ((vertex.y - first.y) * (foot.x - vertex.x) -
              (vertex.y - foot.y) * (first.x - vertex.x)) -
            ((vertex.y - second.y) * (foot.x - vertex.x) -
              (vertex.y - foot.y) * (second.x - vertex.x)) =
          Incidence.pointDeterminant first second vertex -
            ((first.y - second.y) * foot.x +
              (second.x - first.x) * foot.y +
              (first.x * second.y - second.x * first.y)) := by
                unfold Incidence.pointDeterminant
                ring1
        _ = Incidence.pointDeterminant first second vertex := by
          rw [footOnBaseExpanded]
          ring1
    have differenceNonzero : dFirst - dSecond ≠ 0 := by
      rw [determinantDifference]
      exact determinantNonzero
    have determinantSumZero : dFirst + dSecond = 0 := by
      by_cases sumZero : dFirst + dSecond = 0
      · exact sumZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero differenceNonzero sumZero)
            factorZero)
    have xProductZero :
        Incidence.pointDeterminant first second vertex *
          (2 * foot.x - first.x - second.x) = 0 := by
      calc
        Incidence.pointDeterminant first second vertex *
            (2 * foot.x - first.x - second.x) =
          (second.x - first.x) * (dFirst + dSecond) -
            (first.x + second.x - 2 * vertex.x) *
              ((first.y - second.y) * foot.x +
                (second.x - first.x) * foot.y +
                (first.x * second.y - second.x * first.y)) := by
            unfold dFirst dSecond sideFirst sideSecond cevian
            simp only [Incidence.lineThrough_a, Incidence.lineThrough_b]
            unfold Incidence.pointDeterminant
            ring1
        _ = 0 := by rw [determinantSumZero, footOnBaseExpanded]; ring1
    have yProductZero :
        Incidence.pointDeterminant first second vertex *
          (2 * foot.y - first.y - second.y) = 0 := by
      calc
        Incidence.pointDeterminant first second vertex *
            (2 * foot.y - first.y - second.y) =
          (2 * vertex.y - first.y - second.y) *
              ((first.y - second.y) * foot.x +
                (second.x - first.x) * foot.y +
                (first.x * second.y - second.x * first.y)) -
            (first.y - second.y) * (dFirst + dSecond) := by
            unfold dFirst dSecond sideFirst sideSecond cevian
            simp only [Incidence.lineThrough_a, Incidence.lineThrough_b]
            unfold Incidence.pointDeterminant
            ring1
        _ = 0 := by rw [determinantSumZero, footOnBaseExpanded]; ring1
    have xErrorZero : 2 * foot.x - first.x - second.x = 0 :=
      ExplicitField.eq_zero_of_mul_eq_zero_left determinantNonzero xProductZero
    have yErrorZero : 2 * foot.y - first.y - second.y = 0 :=
      ExplicitField.eq_zero_of_mul_eq_zero_left determinantNonzero yProductZero
    apply Plane.Point.ext
    · change foot.x = (first.x + second.x) / 2
      apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
      calc
        foot.x * 2 = 2 * foot.x := by ring1
        _ = first.x + second.x := by
          calc
            2 * foot.x =
                (2 * foot.x - first.x - second.x) +
                  first.x + second.x := by ring1
            _ = first.x + second.x := by rw [xErrorZero]; ring1
        _ = ((first.x + second.x) / 2) * 2 :=
          (ExplicitField.div_mul_cancel _ twoNonzero).symm
    · change foot.y = (first.y + second.y) / 2
      apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
      calc
        foot.y * 2 = 2 * foot.y := by ring1
        _ = first.y + second.y := by
          calc
            2 * foot.y =
                (2 * foot.y - first.y - second.y) +
                  first.y + second.y := by ring1
            _ = first.y + second.y := by rw [yErrorZero]; ring1
        _ = ((first.y + second.y) / 2) * 2 :=
          (ExplicitField.div_mul_cancel _ twoNonzero).symm
  · intro footIsMidpoint
    subst foot
    exact isosceles_midpoint_equal_spreads first second vertex
      vertexFirstDistinct vertexSecondDistinct vertexFootDistinct
      sideFirstNonNull sideSecondNonNull cevianNonNull twoNonzero
      equalVertexQuadrances

/-- Theorem 67 (Isosceles median). For a non-null, noncollinear isosceles triangle and a non-null line from the vertex
to a displayed point of the opposite side, being the altitude, meeting the side at its midpoint, and making equal vertex
spreads are equivalent. -/
theorem isosceles_median [Nontrivial K] [DecidableEq K]
    (first second vertex foot : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (sideFirstNonNull :
      ¬ (Incidence.lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (Incidence.lineThrough vertex second vertexSecondDistinct).IsNull)
    (cevianNonNull :
      ¬ (Incidence.lineThrough vertex foot vertexFootDistinct).IsNull)
    (notCollinear : ¬ Incidence.Collinear first second vertex)
    (footOnBase :
      (Incidence.lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      Quadrance.quadrance vertex first = Quadrance.quadrance vertex second) :
    ((Incidence.lineThrough vertex foot vertexFootDistinct).Perpendicular
          (Incidence.lineThrough first second firstSecondDistinct) ↔
        foot = Affine.midpoint first second) ∧
      (Spread.spread (Incidence.lineThrough vertex first vertexFirstDistinct)
            (Incidence.lineThrough vertex foot vertexFootDistinct)
            sideFirstNonNull cevianNonNull =
          Spread.spread (Incidence.lineThrough vertex second vertexSecondDistinct)
            (Incidence.lineThrough vertex foot vertexFootDistinct)
            sideSecondNonNull cevianNonNull ↔
        foot = Affine.midpoint first second) := by
  exact ⟨isosceles_altitude_iff_midpoint first second vertex foot
      firstSecondDistinct vertexFootDistinct twoNonzero baseNonNull
      footOnBase equalVertexQuadrances,
    isosceles_bisector_iff_midpoint first second vertex foot
      firstSecondDistinct vertexFirstDistinct vertexSecondDistinct
      vertexFootDistinct twoNonzero sideFirstNonNull sideSecondNonNull
      cevianNonNull notCollinear footOnBase equalVertexQuadrances⟩

end Purelib.Geometry.Triangles.Isosceles.Median

end
