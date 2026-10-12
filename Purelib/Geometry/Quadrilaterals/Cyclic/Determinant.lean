module
public import Purelib.Geometry.Quadrilaterals.Cyclic.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Circles.Concyclic.Determinant
import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Quadrilaterals.Basic
import Purelib.Geometry.Triangles.Circumcenter.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals.Basic

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Forward direction of Theorem 109: four points on one displayed circle make the printed coordinate determinant
vanish. -/
theorem coordinateCircleDeterminant_eq_zero_of_isCyclic
    (quadrilateral : Quadrilaterals.Basic.Quadrilateral K) (cyclic : quadrilateral.IsCyclic) :
    Quadrilateral.coordinateCircleDeterminant quadrilateral.first quadrilateral.second
      quadrilateral.third quadrilateral.fourth = 0 := by
  rcases cyclic with
    ⟨circle, center, circleQuadrance, presentation, firstOnCircle,
      secondOnCircle, thirdOnCircle, fourthOnCircle⟩
  rw [Quadrilateral.coordinateCircleDeterminant_eq_fourPointCircleDeterminant]
  exact Conic.fourPointCircleDeterminant_eq_zero circle center
    circleQuadrance presentation quadrilateral.first quadrilateral.second
    quadrilateral.third quadrilateral.fourth firstOnCircle secondOnCircle
    thirdOnCircle fourthOnCircle

open Purelib.Geometry.Triangles.Circumcenter.Basic in
/-- Converse direction of Theorem 109: the determinant equation constructs the normalized circle through the first three
vertices and proves that it also contains the fourth. -/
theorem isCyclic_of_coordinateCircleDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilaterals.Basic.Quadrilateral K) (twoNonzero : (2 : K) ≠ 0)
    (determinantZero :
      Quadrilateral.coordinateCircleDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third quadrilateral.fourth = 0) :
    quadrilateral.IsCyclic := by
  let center := Triangles.Circumcenter.Basic.circumcenterPoint quadrilateral.first quadrilateral.second
    quadrilateral.third quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct
      quadrilateral.firstSecondThirdNoncollinear
  let circleQuadrance := Quadrance.quadrance center quadrilateral.first
  rcases circumcenter quadrilateral.first quadrilateral.second
      quadrilateral.third quadrilateral.firstSecondDistinct
      quadrilateral.firstThirdDistinct quadrilateral.secondThirdDistinct
      quadrilateral.firstSecondThirdNoncollinear twoNonzero with
    ⟨_centerOnSecondThirdBisector, _centerOnFirstThirdBisector,
      _centerOnFirstSecondBisector, firstSecondRadius, secondThirdRadius⟩
  have firstRadius :
      Quadrance.quadrance quadrilateral.first center = circleQuadrance := by
    unfold circleQuadrance
    exact Quadrance.quadrance_symm quadrilateral.first center
  have secondRadius :
      Quadrance.quadrance quadrilateral.second center = circleQuadrance := by
    calc
      Quadrance.quadrance quadrilateral.second center =
          Quadrance.quadrance center quadrilateral.second :=
        Quadrance.quadrance_symm quadrilateral.second center
      _ = Quadrance.quadrance center quadrilateral.first := firstSecondRadius.symm
      _ = circleQuadrance := rfl
  have thirdRadius :
      Quadrance.quadrance quadrilateral.third center = circleQuadrance := by
    calc
      Quadrance.quadrance quadrilateral.third center =
          Quadrance.quadrance center quadrilateral.third :=
        Quadrance.quadrance_symm quadrilateral.third center
      _ = Quadrance.quadrance center quadrilateral.second := secondThirdRadius.symm
      _ = Quadrance.quadrance center quadrilateral.first := firstSecondRadius.symm
      _ = circleQuadrance := rfl
  have translatedDeterminantZero :
      Conic.fourPointCircleDeterminant quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth = 0 := by
    calc
      Conic.fourPointCircleDeterminant quadrilateral.first
          quadrilateral.second quadrilateral.third quadrilateral.fourth =
        Quadrilateral.coordinateCircleDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third quadrilateral.fourth :=
        (Quadrilateral.coordinateCircleDeterminant_eq_fourPointCircleDeterminant
          quadrilateral.first quadrilateral.second quadrilateral.third
          quadrilateral.fourth).symm
      _ = 0 := determinantZero
  have baseDeterminantNonzero :
      Incidence.pointDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third ≠ 0 := by
    intro baseDeterminantZero
    exact quadrilateral.firstSecondThirdNoncollinear
      ((Incidence.collinear_iff_pointDeterminant_eq_zero quadrilateral.first
        quadrilateral.second quadrilateral.third).2 baseDeterminantZero)
  have clearedFourthRadius :
      Incidence.pointDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third *
        (circleQuadrance - Quadrance.quadrance quadrilateral.fourth center) = 0 := by
    calc
      Incidence.pointDeterminant quadrilateral.first quadrilateral.second
          quadrilateral.third *
          (circleQuadrance - Quadrance.quadrance quadrilateral.fourth center) =
        Conic.fourPointCircleDeterminant quadrilateral.first
          quadrilateral.second quadrilateral.third quadrilateral.fourth :=
        (Quadrilateral.fourPointCircleDeterminant_eq_radius_difference
          quadrilateral.first quadrilateral.second quadrilateral.third
          quadrilateral.fourth center circleQuadrance firstRadius
          secondRadius thirdRadius).symm
      _ = 0 := translatedDeterminantZero
  have fourthDifferenceZero :
      circleQuadrance - Quadrance.quadrance quadrilateral.fourth center = 0 :=
    Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left baseDeterminantNonzero clearedFourthRadius
  have fourthRadius :
      Quadrance.quadrance quadrilateral.fourth center = circleQuadrance := by
    calc
      Quadrance.quadrance quadrilateral.fourth center =
          circleQuadrance -
            (circleQuadrance - Quadrance.quadrance quadrilateral.fourth center) := by
        ring1
      _ = circleQuadrance := by rw [fourthDifferenceZero]; ring1
  let circle := Conic.circleConic center circleQuadrance
  have presentation :
      circle.IsCirclePresentation center circleQuadrance :=
    Conic.circleConic_isCirclePresentation center circleQuadrance
  refine ⟨circle, center, circleQuadrance, presentation, ?_, ?_, ?_, ?_⟩
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.first circleQuadrance presentation).2 firstRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.second circleQuadrance presentation).2 secondRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.third circleQuadrance presentation).2 thirdRadius
  · exact (Conic.contains_iff_quadrance_eq circle center
      quadrilateral.fourth circleQuadrance presentation).2 fourthRadius

/-- Theorem 109 (Cyclic quadrilateral): a displayed quadrilateral is cyclic exactly when the source's four-by-four
coordinate determinant vanishes. -/
theorem cyclic_quadrilateral [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilaterals.Basic.Quadrilateral K) (twoNonzero : (2 : K) ≠ 0) :
    quadrilateral.IsCyclic ↔
      Quadrilateral.coordinateCircleDeterminant quadrilateral.first quadrilateral.second
        quadrilateral.third quadrilateral.fourth = 0 := by
  constructor
  · exact coordinateCircleDeterminant_eq_zero_of_isCyclic quadrilateral
  · exact isCyclic_of_coordinateCircleDeterminant_eq_zero quadrilateral
      twoNonzero

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
