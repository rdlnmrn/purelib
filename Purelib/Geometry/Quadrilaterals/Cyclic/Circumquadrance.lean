module
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Quadrilaterals.Basic
import Purelib.Geometry.Quadrilaterals.Cyclic.Spread
import Purelib.Geometry.Trigonometry.Spread.Cyclic.Diagonals
import Purelib.Geometry.Trigonometry.Spread.Quadruple

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial

open Purelib.Geometry.Trigonometry.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 111: quadrilateral circumquadrance

The three printed coefficient polynomials are stored literally.  The proof
keeps the book's substitution `Q_ij = 4*K*r_ij`, but avoids its division and
later cancellation: one homogeneous polynomial identity shows directly that
the requested quadratic is `256*K^6` times the Quadruple-spread relation.
-/

namespace Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Quadrilateral

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

section

/-- Theorem 111 (Quadrilateral circumquadrance), specialized to the four side quadrances of an explicit cyclic
quadrilateral on a non-null circle. -/
theorem quadrilateral_circumquadrance
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
    let q₁₂ := Quadrance.quadrance quadrilateral.first quadrilateral.second
    let q₂₃ := Quadrance.quadrance quadrilateral.second quadrilateral.third
    let q₃₄ := Quadrance.quadrance quadrilateral.third quadrilateral.fourth
    let q₁₄ := Quadrance.quadrance quadrilateral.first quadrilateral.fourth
    Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance ^ 2 -
      2 * Quadrilateral.circumquadranceCoefficientQ q₁₂ q₂₃ q₃₄ q₁₄ *
        circleQuadrance +
      Quadrilateral.circumquadranceCoefficientR q₁₂ q₂₃ q₃₄ q₁₄ = 0 := by
  dsimp only
  let spreads := Quadrilateral.normalizedCyclicSubtendedSpreads quadrilateral circle center
    circleQuadrance twoNonzero quadranceNonzero presentation firstOnCircle
    secondOnCircle thirdOnCircle fourthOnCircle
  have spreadRelation :
      Quadruple.quadrupleSpreadFunction spreads.r₁₂ spreads.r₂₃ spreads.r₃₄
        spreads.r₁₄ = 0 :=
    (Quadrilateral.cyclic_quadrilateral_spreads spreads twoNonzero).1
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have scaleNonzero : 4 * circleQuadrance ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero quadranceNonzero
  have firstScaled :
      Quadrance.quadrance quadrilateral.first quadrilateral.second =
        4 * circleQuadrance * spreads.r₁₂ := by
    change Quadrance.quadrance quadrilateral.first quadrilateral.second =
      4 * circleQuadrance *
        (Quadrance.quadrance quadrilateral.first quadrilateral.second /
          (4 * circleQuadrance))
    calc
      Quadrance.quadrance quadrilateral.first quadrilateral.second =
          (Quadrance.quadrance quadrilateral.first quadrilateral.second /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (Quadrance.quadrance quadrilateral.first quadrilateral.second /
            (4 * circleQuadrance)) := by ring1
  have secondScaled :
      Quadrance.quadrance quadrilateral.second quadrilateral.third =
        4 * circleQuadrance * spreads.r₂₃ := by
    change Quadrance.quadrance quadrilateral.second quadrilateral.third =
      4 * circleQuadrance *
        (Quadrance.quadrance quadrilateral.second quadrilateral.third /
          (4 * circleQuadrance))
    calc
      Quadrance.quadrance quadrilateral.second quadrilateral.third =
          (Quadrance.quadrance quadrilateral.second quadrilateral.third /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (Quadrance.quadrance quadrilateral.second quadrilateral.third /
            (4 * circleQuadrance)) := by ring1
  have thirdScaled :
      Quadrance.quadrance quadrilateral.third quadrilateral.fourth =
        4 * circleQuadrance * spreads.r₃₄ := by
    change Quadrance.quadrance quadrilateral.third quadrilateral.fourth =
      4 * circleQuadrance *
        (Quadrance.quadrance quadrilateral.third quadrilateral.fourth /
          (4 * circleQuadrance))
    calc
      Quadrance.quadrance quadrilateral.third quadrilateral.fourth =
          (Quadrance.quadrance quadrilateral.third quadrilateral.fourth /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (Quadrance.quadrance quadrilateral.third quadrilateral.fourth /
            (4 * circleQuadrance)) := by ring1
  have fourthScaled :
      Quadrance.quadrance quadrilateral.first quadrilateral.fourth =
        4 * circleQuadrance * spreads.r₁₄ := by
    change Quadrance.quadrance quadrilateral.first quadrilateral.fourth =
      4 * circleQuadrance *
        (Quadrance.quadrance quadrilateral.first quadrilateral.fourth /
          (4 * circleQuadrance))
    calc
      Quadrance.quadrance quadrilateral.first quadrilateral.fourth =
          (Quadrance.quadrance quadrilateral.first quadrilateral.fourth /
            (4 * circleQuadrance)) * (4 * circleQuadrance) :=
        (ExplicitField.div_mul_cancel _ scaleNonzero).symm
      _ = 4 * circleQuadrance *
          (Quadrance.quadrance quadrilateral.first quadrilateral.fourth /
            (4 * circleQuadrance)) := by ring1
  exact Quadrilateral.quadrilateral_circumquadrance_of_scaled_spreads
    (Quadrance.quadrance quadrilateral.first quadrilateral.second)
    (Quadrance.quadrance quadrilateral.second quadrilateral.third)
    (Quadrance.quadrance quadrilateral.third quadrilateral.fourth)
    (Quadrance.quadrance quadrilateral.first quadrilateral.fourth)
    spreads.r₁₂ spreads.r₂₃ spreads.r₃₄ spreads.r₁₄ circleQuadrance
    firstScaled secondScaled thirdScaled fourthScaled spreadRelation
end

end Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Quadrilateral

end
