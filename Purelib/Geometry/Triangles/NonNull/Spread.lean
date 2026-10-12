module
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.NonNull.Basic
public import Purelib.Geometry.Triangles.Quadrea.Basic
public import Purelib.Geometry.Triangles.Similarity.Entries
import Purelib.Geometry.Triangles.Trigonometry.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Triangles.NonNull.Basic

open Purelib.Geometry.Triangles.Similarity

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The three spreads at the first, second, and third vertices. -/
def spreads (triangle : NonNull.Basic.NonNullTriangle K)
  : Coordinates3.Vector K :=
  ⟨Spread.spread
      (Incidence.lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct)
      (Incidence.lineThrough triangle.first triangle.third
        triangle.firstThirdDistinct)
      triangle.firstSecondNonNull triangle.firstThirdNonNull,
    Spread.spread
      (Incidence.lineThrough triangle.second triangle.first
        triangle.firstSecondDistinct.symm)
      (Incidence.lineThrough triangle.second triangle.third
        triangle.secondThirdDistinct)
      triangle.firstSecondReversedNonNull triangle.secondThirdNonNull,
    Spread.spread
      (Incidence.lineThrough triangle.third triangle.first
        triangle.firstThirdDistinct.symm)
      (Incidence.lineThrough triangle.third triangle.second
        triangle.secondThirdDistinct.symm)
      triangle.firstThirdReversedNonNull
      triangle.secondThirdReversedNonNull⟩
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The common value in the Spread law. -/
def commonSpreadRatio (triangle :
  NonNull.Basic.NonNullTriangle K) : K :=
  triangle.spreads.t / triangle.quadrances.t
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Reversing both displayed representatives does not change their spread. -/
theorem firstSpread_eq_reversed (triangle :
  NonNull.Basic.NonNullTriangle K) :
    triangle.spreads.t =
      Spread.spread
        (Incidence.lineThrough triangle.second triangle.first
          triangle.firstSecondDistinct.symm)
        (Incidence.lineThrough triangle.third triangle.first
          triangle.firstThirdDistinct.symm)
        triangle.firstSecondReversedNonNull
        triangle.firstThirdReversedNonNull := by
  exact NonNullTriangle.spread_lineThrough_reverse_both triangle.first triangle.second
    triangle.third triangle.firstSecondDistinct
    triangle.firstThirdDistinct triangle.firstSecondNonNull
    triangle.firstThirdNonNull
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The first vertex spread of a non-null triangle is nonzero when two is nonzero. -/
theorem firstSpreadNonzero [Nontrivial K] (triangle :
  NonNull.Basic.NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) : triangle.spreads.t ≠ 0 := by
  have areaNonzero : Quadrea.Basic.quadrea triangle.first triangle.second triangle.third ≠ 0 :=
    (Quadrea.Basic.quadrea_ne_zero_iff_not_collinear triangle.first triangle.second
      triangle.third twoNonzero).2 triangle.notCollinear
  have areaAtFirst := Trigonometry.Spread.quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm triangle.firstSecondReversedNonNull
    triangle.firstThirdReversedNonNull
  rw [Quadrea.Basic.quadrea_cyclic triangle.first triangle.second triangle.third] at areaAtFirst
  rw [← triangle.firstSpread_eq_reversed] at areaAtFirst
  intro spreadZero
  apply areaNonzero
  calc
    Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
        4 * Quadrance.quadrance triangle.third triangle.first *
          Quadrance.quadrance triangle.second triangle.first *
            triangle.spreads.t := areaAtFirst
    _ = 0 := by rw [spreadZero]; ring1
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The common spread-to-quadrance ratio of a non-null triangle is nonzero when two is nonzero. -/
theorem commonSpreadRatioNonzero [Nontrivial K]
    (triangle : NonNull.Basic.NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) : triangle.commonSpreadRatio ≠ 0 := by
  exact ExplicitField.div_ne_zero
    (triangle.firstSpreadNonzero twoNonzero)
    triangle.firstQuadranceNonzero

end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The three denominator-cleared Quadrea--spread identities, packaged in the same opposite-vertex order as `quadrances`
and `spreads`. -/
theorem quadrea_spread_products (triangle :
  NonNull.Basic.NonNullTriangle K) :
    Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
        (Entries.spreadDenominators triangle.quadrances).t *
          triangle.spreads.t ∧
      Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
        (Entries.spreadDenominators triangle.quadrances).r *
          triangle.spreads.r ∧
      Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
        (Entries.spreadDenominators triangle.quadrances).s *
          triangle.spreads.s := by
  have firstArea := Trigonometry.Spread.quadrea_spread triangle.second triangle.third
    triangle.first triangle.firstSecondDistinct.symm
    triangle.firstThirdDistinct.symm triangle.firstSecondReversedNonNull
    triangle.firstThirdReversedNonNull
  rw [Quadrea.Basic.quadrea_cyclic triangle.first triangle.second triangle.third,
    Quadrance.quadrance_symm triangle.third triangle.first,
    Quadrance.quadrance_symm triangle.second triangle.first,
    ← NonNullTriangle.spread_lineThrough_reverse_both triangle.first triangle.second
      triangle.third triangle.firstSecondDistinct
      triangle.firstThirdDistinct triangle.firstSecondNonNull
      triangle.firstThirdNonNull] at firstArea
  have secondArea := Trigonometry.Spread.quadrea_spread triangle.first triangle.third
    triangle.second triangle.firstSecondDistinct
    triangle.secondThirdDistinct.symm triangle.firstSecondNonNull
    triangle.secondThirdReversedNonNull
  rw [Quadrea.Basic.quadrea_swap_second_third triangle.first triangle.second triangle.third,
    Quadrance.quadrance_symm triangle.third triangle.second,
    ← NonNullTriangle.spread_lineThrough_reverse_both triangle.second triangle.first
      triangle.third triangle.firstSecondDistinct.symm
      triangle.secondThirdDistinct triangle.firstSecondReversedNonNull
      triangle.secondThirdNonNull] at secondArea
  have thirdArea := Trigonometry.Spread.quadrea_spread triangle.first triangle.second
    triangle.third triangle.firstThirdDistinct
    triangle.secondThirdDistinct triangle.firstThirdNonNull
    triangle.secondThirdNonNull
  rw [← NonNullTriangle.spread_lineThrough_reverse_both triangle.third triangle.first
      triangle.second triangle.firstThirdDistinct.symm
      triangle.secondThirdDistinct.symm triangle.firstThirdReversedNonNull
      triangle.secondThirdReversedNonNull] at thirdArea
  change Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
    (Entries.spreadDenominators triangle.quadrances).t *
      triangle.spreads.t at firstArea
  change Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
    (Entries.spreadDenominators triangle.quadrances).r *
      triangle.spreads.r at secondArea
  change Quadrea.Basic.quadrea triangle.first triangle.second triangle.third =
    (Entries.spreadDenominators triangle.quadrances).s *
      triangle.spreads.s at thirdArea
  exact ⟨firstArea, secondArea, thirdArea⟩
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Each product of four and two adjacent side quadrances is nonzero when two is nonzero. -/
theorem spreadDenominatorsNonzero (triangle :
  NonNull.Basic.NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) :
    (Entries.spreadDenominators triangle.quadrances).t ≠ 0 ∧
      (Entries.spreadDenominators triangle.quadrances).r ≠ 0 ∧
      (Entries.spreadDenominators triangle.quadrances).s ≠ 0 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  exact ⟨
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero
        triangle.secondQuadranceNonzero)
      triangle.thirdQuadranceNonzero,
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero
        triangle.firstQuadranceNonzero)
      triangle.thirdQuadranceNonzero,
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero
        triangle.firstQuadranceNonzero)
      triangle.secondQuadranceNonzero⟩
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- The three vertex-spread to opposite-quadrance ratios agree.

The triangle retains noncollinearity and non-null sides, and two is assumed nonzero. -/
theorem spreadRatioLaws (triangle :
  NonNull.Basic.NonNullTriangle K)
    (twoNonzero : (2 : K) ≠ 0) :
    triangle.commonSpreadRatio =
        triangle.spreads.r / triangle.quadrances.r ∧
      triangle.spreads.r / triangle.quadrances.r =
        triangle.spreads.s / triangle.quadrances.s := by
  change
    Spread.spread
          (Incidence.lineThrough triangle.first triangle.second
            triangle.firstSecondDistinct)
          (Incidence.lineThrough triangle.first triangle.third
            triangle.firstThirdDistinct)
          triangle.firstSecondNonNull triangle.firstThirdNonNull /
        Quadrance.quadrance triangle.second triangle.third =
      Spread.spread
          (Incidence.lineThrough triangle.second triangle.first
            triangle.firstSecondDistinct.symm)
          (Incidence.lineThrough triangle.second triangle.third
            triangle.secondThirdDistinct)
          triangle.firstSecondReversedNonNull
          triangle.secondThirdNonNull /
        Quadrance.quadrance triangle.first triangle.third ∧
      Spread.spread
          (Incidence.lineThrough triangle.second triangle.first
            triangle.firstSecondDistinct.symm)
          (Incidence.lineThrough triangle.second triangle.third
            triangle.secondThirdDistinct)
          triangle.firstSecondReversedNonNull
          triangle.secondThirdNonNull /
        Quadrance.quadrance triangle.first triangle.third =
      Spread.spread
          (Incidence.lineThrough triangle.third triangle.first
            triangle.firstThirdDistinct.symm)
          (Incidence.lineThrough triangle.third triangle.second
            triangle.secondThirdDistinct.symm)
          triangle.firstThirdReversedNonNull
          triangle.secondThirdReversedNonNull /
        Quadrance.quadrance triangle.first triangle.second
  exact Trigonometry.Spread.spread_law triangle.first triangle.second triangle.third
    triangle.firstSecondDistinct triangle.firstThirdDistinct
    triangle.secondThirdDistinct triangle.firstSecondNonNull
    triangle.firstThirdNonNull triangle.secondThirdNonNull twoNonzero
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end

section
@[expose] public section
namespace Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle
variable {K : Type*} [ExplicitField K]
section
variable [DecidableEq K]

/-- Each vertex spread is the common spread ratio times its opposite side quadrance.

The non-null triangle supplies the three nonzero quadrances, and two is nonzero. -/
theorem spreads_eq_commonRatio_mul_quadrances
    (triangle : NonNull.Basic.NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0) :
    triangle.spreads.t =
        triangle.commonSpreadRatio * triangle.quadrances.t ∧
      triangle.spreads.r =
        triangle.commonSpreadRatio * triangle.quadrances.r ∧
      triangle.spreads.s =
        triangle.commonSpreadRatio * triangle.quadrances.s := by
  have laws := triangle.spreadRatioLaws twoNonzero
  constructor
  · exact (ExplicitField.div_mul_cancel triangle.spreads.t
      triangle.firstQuadranceNonzero).symm
  constructor
  · calc
      triangle.spreads.r =
          (triangle.spreads.r / triangle.quadrances.r) *
            triangle.quadrances.r :=
        (ExplicitField.div_mul_cancel triangle.spreads.r
          triangle.secondQuadranceNonzero).symm
      _ = triangle.commonSpreadRatio * triangle.quadrances.r := by
        rw [← laws.1]
  · calc
      triangle.spreads.s =
          (triangle.spreads.s / triangle.quadrances.s) *
            triangle.quadrances.s :=
        (ExplicitField.div_mul_cancel triangle.spreads.s
          triangle.thirdQuadranceNonzero).symm
      _ = triangle.commonSpreadRatio * triangle.quadrances.s := by
        rw [← laws.2, ← laws.1]
end
end Purelib.Geometry.Triangles.NonNull.Basic.NonNullTriangle

end
