module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

namespace Purelib.Geometry.Triangles.Medial.Basic

variable {K : Type*} [ExplicitField K]

/-- The midpoint of the side opposite the first vertex. -/
def sideMidpointOppositeFirst (_first second third :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint second third

/-- The midpoint of the side opposite the second vertex. -/
def sideMidpointOppositeSecond (first _second third :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint first third

/-- The midpoint of the side opposite the third vertex. -/
def sideMidpointOppositeThird (first second _third :
  Plane.Point K) : Plane.Point K :=
  Affine.midpoint first second

end Purelib.Geometry.Triangles.Medial.Basic

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: the median triangle

All three midpoint sides are retained as displayed lines.  Their distinctness,
parallelism, and non-nullity are proved explicitly, so the final similarity
statement is a finite triple of spread equalities over any explicit field of
characteristic different from two.
-/

namespace Purelib.Geometry.Triangles.Medial.Basic

variable {K : Type*} [ExplicitField K]

/-- The first two opposite-side midpoints are distinct when the corresponding original vertices are distinct and two is
nonzero. -/
theorem medianPoint₁_ne_medianPoint₂
    (first second third : Plane.Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    sideMidpointOppositeFirst first second third ≠
      sideMidpointOppositeSecond first second third := by
  unfold sideMidpointOppositeFirst sideMidpointOppositeSecond
  exact Affine.midpoint_pair_distinct second first third firstSecondDistinct.symm
    twoNonzero

/-- The last two opposite-side midpoints are distinct when the corresponding original vertices are distinct and two is
nonzero. -/
theorem medianPoint₂_ne_medianPoint₃
    (first second third : Plane.Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    sideMidpointOppositeSecond first second third ≠
      sideMidpointOppositeThird first second third := by
  unfold sideMidpointOppositeSecond sideMidpointOppositeThird
  exact Affine.midpoint_pair_distinct_left first third second
    secondThirdDistinct.symm twoNonzero

/-- The first and third opposite-side midpoints are distinct when the corresponding original vertices are distinct and
two is nonzero. -/
theorem medianPoint₁_ne_medianPoint₃
    (first second third : Plane.Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    sideMidpointOppositeFirst first second third ≠
      sideMidpointOppositeThird first second third := by
  unfold sideMidpointOppositeFirst sideMidpointOppositeThird
  intro equalMidpoints
  apply firstThirdDistinct.symm
  apply Affine.midpoint_cancel_common third first second twoNonzero
  calc
    Affine.midpoint third second = Affine.midpoint second third := Affine.midpoint_symm third second
    _ = Affine.midpoint first second := equalMidpoints

/-- The median-triangle side corresponding to `A₁A₂`. -/
def medianSide₁₂ [DecidableEq K]
    (first second third : Plane.Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) : Plane.Line K :=
  Incidence.lineThrough (sideMidpointOppositeFirst first second third)
    (sideMidpointOppositeSecond first second third)
    (medianPoint₁_ne_medianPoint₂ first second third firstSecondDistinct
      twoNonzero)

/-- The median-triangle side corresponding to `A₂A₃`. -/
def medianSide₂₃ [DecidableEq K]
    (first second third : Plane.Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) : Plane.Line K :=
  Incidence.lineThrough (sideMidpointOppositeSecond first second third)
    (sideMidpointOppositeThird first second third)
    (medianPoint₂_ne_medianPoint₃ first second third secondThirdDistinct
      twoNonzero)

/-- The median-triangle side corresponding to `A₁A₃`. -/
def medianSide₁₃ [DecidableEq K]
    (first second third : Plane.Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) : Plane.Line K :=
  Incidence.lineThrough (sideMidpointOppositeFirst first second third)
    (sideMidpointOppositeThird first second third)
    (medianPoint₁_ne_medianPoint₃ first second third firstThirdDistinct
      twoNonzero)

/-- The medial side through the first two opposite-side midpoints is parallel to the corresponding original side. -/
theorem median_side₁₂_parallel [DecidableEq K]
    (first second third : Plane.Point K) (firstSecondDistinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₁₂ first second third firstSecondDistinct twoNonzero).Parallel
      (Incidence.lineThrough first second firstSecondDistinct) := by
  unfold medianSide₁₂ sideMidpointOppositeFirst
    sideMidpointOppositeSecond
  unfold Plane.Line.Parallel Incidence.lineThrough Affine.midpoint
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The medial side through the last two opposite-side midpoints is parallel to the corresponding original side. -/
theorem median_side₂₃_parallel [DecidableEq K]
    (first second third : Plane.Point K) (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₂₃ first second third secondThirdDistinct twoNonzero).Parallel
      (Incidence.lineThrough second third secondThirdDistinct) := by
  unfold medianSide₂₃ sideMidpointOppositeSecond
    sideMidpointOppositeThird
  unfold Plane.Line.Parallel Incidence.lineThrough Affine.midpoint
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The medial side through the first and third opposite-side midpoints is parallel to the corresponding original side.
-/
theorem median_side₁₃_parallel [DecidableEq K]
    (first second third : Plane.Point K) (firstThirdDistinct : first ≠ third)
    (twoNonzero : (2 : K) ≠ 0) :
    (medianSide₁₃ first second third firstThirdDistinct twoNonzero).Parallel
      (Incidence.lineThrough first third firstThirdDistinct) := by
  unfold medianSide₁₃ sideMidpointOppositeFirst
    sideMidpointOppositeThird
  unfold Plane.Line.Parallel Incidence.lineThrough Affine.midpoint
  simp only [ExplicitField.div_eq_mul_inv]
  ring1
end Purelib.Geometry.Triangles.Medial.Basic

end
