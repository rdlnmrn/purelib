module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Geometry.Circles.SubtendedSpread
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Quadrilaterals.Basic
public import Purelib.Geometry.Trigonometry.Spread.Cyclic.Basic
import Purelib.Geometry.Trigonometry.Spread.Triple
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Circles.Conic.Basic

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- Construct all six normalized subtended spreads and their four triangle certificates from a displayed cyclic
quadrilateral on a non-null circle. -/
def normalizedCyclicSubtendedSpreads
    [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilaterals.Basic.Quadrilateral K)
    (circle : Conic K) (center : Plane.Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains quadrilateral.first)
    (secondOnCircle : circle.Contains quadrilateral.second)
    (thirdOnCircle : circle.Contains quadrilateral.third)
    (fourthOnCircle : circle.Contains quadrilateral.fourth) :
    Quadrilateral.CyclicSubtendedSpreads K where
  r₁₂ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.second
  r₂₃ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.second quadrilateral.third
  r₃₄ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.third quadrilateral.fourth
  r₁₄ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.fourth
  r₁₃ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.third
  r₂₄ := Quadrilateral.normalizedSubtendedSpread circleQuadrance
    quadrilateral.second quadrilateral.fourth
  firstDiagonalAtFourth :=
    Quadrilateral.normalized_subtended_spreads_form_triple circle center
      quadrilateral.first quadrilateral.second quadrilateral.third
      quadrilateral.fourth circleQuadrance
      quadrilateral.firstSecondDistinct quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct quadrilateral.firstFourthDistinct
      quadrilateral.secondFourthDistinct quadrilateral.thirdFourthDistinct
      twoNonzero quadranceNonzero presentation firstOnCircle secondOnCircle
      thirdOnCircle fourthOnCircle
  firstDiagonalAtSecond := by
    have raw := Quadrilateral.normalized_subtended_spreads_form_triple circle center
      quadrilateral.third quadrilateral.fourth quadrilateral.first
      quadrilateral.second circleQuadrance
      quadrilateral.thirdFourthDistinct
      quadrilateral.firstThirdDistinct.symm
      quadrilateral.firstFourthDistinct.symm
      quadrilateral.secondThirdDistinct.symm
      quadrilateral.secondFourthDistinct.symm
      quadrilateral.firstSecondDistinct
      twoNonzero quadranceNonzero presentation thirdOnCircle fourthOnCircle
      firstOnCircle secondOnCircle
    rw [Quadrilateral.normalizedSubtendedSpread_symm circleQuadrance quadrilateral.fourth
      quadrilateral.first,
      Quadrilateral.normalizedSubtendedSpread_symm circleQuadrance quadrilateral.third
        quadrilateral.first] at raw
    exact raw
  secondDiagonalAtThird := by
    have raw := Quadrilateral.normalized_subtended_spreads_form_triple circle center
      quadrilateral.first quadrilateral.second quadrilateral.fourth
      quadrilateral.third circleQuadrance
      quadrilateral.firstSecondDistinct quadrilateral.firstFourthDistinct
      quadrilateral.secondFourthDistinct quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct quadrilateral.thirdFourthDistinct.symm
      twoNonzero quadranceNonzero presentation firstOnCircle secondOnCircle
      fourthOnCircle thirdOnCircle
    exact Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_swap_last raw
  secondDiagonalAtFirst :=
    Quadrilateral.normalized_subtended_spreads_form_triple circle center
      quadrilateral.second quadrilateral.third quadrilateral.fourth
      quadrilateral.first circleQuadrance
      quadrilateral.secondThirdDistinct quadrilateral.secondFourthDistinct
      quadrilateral.thirdFourthDistinct quadrilateral.firstSecondDistinct.symm
      quadrilateral.firstThirdDistinct.symm
      quadrilateral.firstFourthDistinct.symm
      twoNonzero quadranceNonzero presentation secondOnCircle thirdOnCircle
      fourthOnCircle firstOnCircle
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
