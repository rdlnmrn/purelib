module
import Purelib.Geometry.Plane.Line.VertexBisector.Existence
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Line.VertexBisector.Construction
import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Spread

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.VertexBisector.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.VertexBisector

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, §12.5: incenters

The triangle is represented by its three non-null, pairwise nonparallel side
lines.  A chosen bisector at each of the first two vertices is input data,
matching the constructive existence condition from Theorem 45.  Reflection
shows that those bisectors cannot be parallel.  Their intersection has equal
quadrance to all three side lines, and explicit square witnesses then select a
third vertex bisector through the same point.
-/

namespace Purelib.Geometry.Triangles.Incenter.Basic

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Theorem 88 (Incenter). `thirdSide` and `secondSide` meet at the first vertex, `thirdSide` and `firstSide` at the
second, and `secondSide` and `firstSide` at the third. The result constructs the common point and a third bisector
containing it. -/
theorem incenter
    [Nontrivial K] [DecidableEq K]
    (firstSide secondSide thirdSide : Plane.Line K)
    (firstSideNonNull : ¬ firstSide.IsNull)
    (secondSideNonNull : ¬ secondSide.IsNull)
    (thirdSideNonNull : ¬ thirdSide.IsNull)
    (firstVertexNonparallel : ¬ thirdSide.Parallel secondSide)
    (secondVertexNonparallel : ¬ thirdSide.Parallel firstSide)
    (thirdVertexNonparallel : ¬ secondSide.Parallel firstSide)
    (twoNonzero : (2 : K) ≠ 0)
    (firstBisector secondBisector : Plane.Line K)
    (isFirstBisector :
      VertexBisector.Basic.IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel)
    (isSecondBisector :
      VertexBisector.Basic.IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel) :
    ∃ bisectorsNonparallel : ¬ firstBisector.Parallel secondBisector,
      let center := Intersection.lineIntersection firstBisector secondBisector
        bisectorsNonparallel
      firstBisector.Contains center ∧
        secondBisector.Contains center ∧
        ∃ thirdBisector : Plane.Line K,
          VertexBisector.Basic.IsVertexBisector secondSide firstSide thirdBisector
              secondSideNonNull firstSideNonNull thirdVertexNonparallel ∧
            thirdBisector.Contains center := by
  rcases isFirstBisector with
    ⟨firstBisectorNonNull, firstBisectorContainsVertex,
      firstEqualSpreads⟩
  rcases isSecondBisector with
    ⟨secondBisectorNonNull, secondBisectorContainsVertex,
      secondEqualSpreads⟩
  have firstSidesNotEquivalent : ¬ thirdSide.Equivalent secondSide := by
    intro equivalent
    exact firstVertexNonparallel (Relations.line_parallel_of_equivalent equivalent)
  have secondSidesNotEquivalent : ¬ thirdSide.Equivalent firstSide := by
    intro equivalent
    exact secondVertexNonparallel (Relations.line_parallel_of_equivalent equivalent)
  let firstVertex := Intersection.lineIntersection thirdSide secondSide
    firstVertexNonparallel
  let secondVertex := Intersection.lineIntersection thirdSide firstSide
    secondVertexNonparallel
  have firstReflected :
      (Line.reflectLine firstBisector thirdSide firstBisectorNonNull).Equivalent
        secondSide := by
    apply (Spread.spread_reflection firstBisector thirdSide secondSide firstVertex
      firstBisectorNonNull thirdSideNonNull secondSideNonNull
      firstBisectorContainsVertex
      (Intersection.lineIntersection_on_first thirdSide secondSide firstVertexNonparallel)
      (Intersection.lineIntersection_on_second thirdSide secondSide firstVertexNonparallel)
      firstSidesNotEquivalent).2
    exact firstEqualSpreads
  have secondReflected :
      (Line.reflectLine secondBisector thirdSide secondBisectorNonNull).Equivalent
        firstSide := by
    apply (Spread.spread_reflection secondBisector thirdSide firstSide secondVertex
      secondBisectorNonNull thirdSideNonNull firstSideNonNull
      secondBisectorContainsVertex
      (Intersection.lineIntersection_on_first thirdSide firstSide secondVertexNonparallel)
      (Intersection.lineIntersection_on_second thirdSide firstSide secondVertexNonparallel)
      secondSidesNotEquivalent).2
    exact secondEqualSpreads
  have bisectorsNonparallel : ¬ firstBisector.Parallel secondBisector := by
    intro parallelBisectors
    have reflectedParallel := Line.reflectLine_parallel_of_parallel_mirrors
      firstBisector secondBisector thirdSide firstBisectorNonNull
      secondBisectorNonNull parallelBisectors
    have secondToFirstReflected :
        secondSide.Parallel
          (Line.reflectLine firstBisector thirdSide firstBisectorNonNull) :=
      Plane.Line.parallel_symm (Relations.line_parallel_of_equivalent firstReflected)
    have firstReflectedToSecondReflected :
        (Line.reflectLine firstBisector thirdSide firstBisectorNonNull).Parallel
          (Line.reflectLine secondBisector thirdSide secondBisectorNonNull) :=
      reflectedParallel
    have secondReflectedToFirst :
        (Line.reflectLine secondBisector thirdSide secondBisectorNonNull).Parallel
          firstSide := Relations.line_parallel_of_equivalent secondReflected
    apply thirdVertexNonparallel
    exact Relations.line_parallel_trans
      (Relations.line_parallel_trans secondToFirstReflected
        firstReflectedToSecondReflected)
      secondReflectedToFirst
  refine ⟨bisectorsNonparallel, ?_⟩
  dsimp only
  let center := Intersection.lineIntersection firstBisector secondBisector
    bisectorsNonparallel
  have centerOnFirst : firstBisector.Contains center :=
    Intersection.lineIntersection_on_first firstBisector secondBisector
      bisectorsNonparallel
  have centerOnSecond : secondBisector.Contains center :=
    Intersection.lineIntersection_on_second firstBisector secondBisector
      bisectorsNonparallel
  have firstBisectorAgain :
      VertexBisector.Basic.IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel :=
    ⟨firstBisectorNonNull, firstBisectorContainsVertex, firstEqualSpreads⟩
  have secondBisectorAgain :
      VertexBisector.Basic.IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel :=
    ⟨secondBisectorNonNull, secondBisectorContainsVertex, secondEqualSpreads⟩
  have equalThirdSecond :=
    Quadrance.equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel firstBisectorAgain center centerOnFirst
  have equalThirdFirst :=
    Quadrance.equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel secondBisectorAgain center centerOnSecond
  have equalSecondFirst :
      Quadrance.pointLineQuadrance center secondSide secondSideNonNull =
        Quadrance.pointLineQuadrance center firstSide firstSideNonNull :=
    equalThirdSecond.symm.trans equalThirdFirst
  rcases Existence.normProduct_isNonzeroSquare_of_isVertexBisector
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel firstBisectorAgain with
    ⟨firstRoot, _firstRootNonzero, firstRootEquation⟩
  rcases Existence.normProduct_isNonzeroSquare_of_isVertexBisector
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel secondBisectorAgain with
    ⟨secondRoot, _secondRootNonzero, secondRootEquation⟩
  let thirdRoot := firstRoot * secondRoot / Line.Basic.lineNorm thirdSide
  have thirdSideNormCancel :
      Line.Basic.lineNorm thirdSide * (Line.Basic.lineNorm thirdSide)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel _ thirdSideNonNull
  have thirdRootEquation :
      thirdRoot ^ 2 = Line.Basic.lineNorm secondSide * Line.Basic.lineNorm firstSide := by
    unfold thirdRoot
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (firstRoot * secondRoot * (Line.Basic.lineNorm thirdSide)⁻¹) ^ 2 =
          firstRoot ^ 2 * secondRoot ^ 2 *
            (Line.Basic.lineNorm thirdSide)⁻¹ ^ 2 := by ring1
      _ = (Line.Basic.lineNorm thirdSide * Line.Basic.lineNorm secondSide) *
          (Line.Basic.lineNorm thirdSide * Line.Basic.lineNorm firstSide) *
            (Line.Basic.lineNorm thirdSide)⁻¹ ^ 2 := by
              rw [← firstRootEquation, ← secondRootEquation]
      _ = Line.Basic.lineNorm secondSide * Line.Basic.lineNorm firstSide *
          (Line.Basic.lineNorm thirdSide * (Line.Basic.lineNorm thirdSide)⁻¹) ^ 2 := by ring1
      _ = Line.Basic.lineNorm secondSide * Line.Basic.lineNorm firstSide := by
        rw [thirdSideNormCancel]
        ring1
  have centerOnThirdCandidate :=
    (Quadrance.equal_pointLineQuadrance_iff_on_vertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      thirdRootEquation center).1 equalSecondFirst
  refine ⟨centerOnFirst, centerOnSecond, ?_⟩
  rcases centerOnThirdCandidate with centerOnPositive | centerOnNegative
  · let thirdBisector := Construction.positiveVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull thirdVertexNonparallel
    refine ⟨thirdBisector, ?_, centerOnPositive⟩
    exact Construction.positiveVertexBisector_isVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      twoNonzero thirdRootEquation
  · let thirdBisector := Construction.negativeVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull thirdVertexNonparallel
    refine ⟨thirdBisector, ?_, centerOnNegative⟩
    exact Construction.negativeVertexBisector_isVertexBisector secondSide firstSide
      thirdRoot secondSideNonNull firstSideNonNull thirdVertexNonparallel
      twoNonzero thirdRootEquation

end Purelib.Geometry.Triangles.Incenter.Basic

end
