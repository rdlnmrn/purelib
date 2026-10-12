module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Line.Basic
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, Exercise 3.16: medians and the centroid

The three median lines are explicit `lineThrough` constructions.  Their
characteristic-three behavior is proved directly from their finite
coefficients: in characteristic three they are parallel, while otherwise the
displayed centroid lies on all three.  No completed point family or implicit
choice of a line is used.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry

/-- The centroid of three displayed points. -/
@[expose] def centroidPoint (first second third : Plane.Point K) : Plane.Point K :=
  ⟨(first.x + second.x + third.x) / 3,
    (first.y + second.y + third.y) / 3⟩

/-- The first coordinate of the centroid is the average of the three first coordinates. -/
@[simp] theorem centroidPoint_x (first second third : Plane.Point K) :
    (centroidPoint first second third).x =
      (first.x + second.x + third.x) / 3 := rfl

/-- The second coordinate of the centroid is the average of the three second coordinates. -/
@[simp] theorem centroidPoint_y (first second third : Plane.Point K) :
    (centroidPoint first second third).y =
      (first.y + second.y + third.y) / 3 := rfl

/-- A line is a median at `vertex` when it contains that vertex and the midpoint of the displayed opposite side. -/
@[expose] def IsMedianLine (line : Plane.Line K)
    (vertex oppositeFirst oppositeSecond : Plane.Point K) : Prop :=
  line.Contains vertex ∧
    line.Contains (Affine.midpoint oppositeFirst oppositeSecond)

/-- Cyclically moving the first vertex to the last preserves noncollinearity. -/
private theorem not_collinear_cyclic_left
    {first second third : Plane.Point K}
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ Incidence.Collinear second third first := by
  rintro ⟨line, containsSecond, containsThird, containsFirst⟩
  exact notCollinear ⟨line, containsFirst, containsSecond, containsThird⟩

/-- Cyclically moving the third vertex to the first preserves noncollinearity. -/
private theorem not_collinear_cyclic_right
    {first second third : Plane.Point K}
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ Incidence.Collinear third first second :=
  not_collinear_cyclic_left (not_collinear_cyclic_left notCollinear)

/-- A vertex of a noncollinear triangle cannot equal the opposite midpoint. -/
theorem vertex_ne_opposite_midpoint
    [Nontrivial K] [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear vertex oppositeFirst oppositeSecond)
    (twoNonzero : (2 : K) ≠ 0) :
    vertex ≠ Affine.midpoint oppositeFirst oppositeSecond := by
  intro vertexIsMidpoint
  apply notCollinear
  apply (Incidence.collinear_iff_pointDeterminant_eq_zero _ _ _).2
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  rw [vertexIsMidpoint]
  unfold Incidence.pointDeterminant Affine.midpoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (oppositeFirst.x + oppositeSecond.x) * (2 : K)⁻¹ *
          oppositeFirst.y -
        (oppositeFirst.x + oppositeSecond.x) * (2 : K)⁻¹ *
          oppositeSecond.y +
        oppositeFirst.x * oppositeSecond.y -
        oppositeSecond.x * oppositeFirst.y +
        oppositeSecond.x *
          ((oppositeFirst.y + oppositeSecond.y) * (2 : K)⁻¹) -
        oppositeFirst.x *
          ((oppositeFirst.y + oppositeSecond.y) * (2 : K)⁻¹) =
      (1 - 2 * (2 : K)⁻¹) *
        (oppositeFirst.x * oppositeSecond.y -
          oppositeSecond.x * oppositeFirst.y) := by
            ring1
    _ = 0 := by rw [twoInverse]; ring1

/-- The executable median line through a vertex and the opposite midpoint. -/
@[expose] def medianLine [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (vertexNotMidpoint :
      vertex ≠ Affine.midpoint oppositeFirst oppositeSecond) : Plane.Line K :=
  Incidence.lineThrough vertex (Affine.midpoint oppositeFirst oppositeSecond)
    vertexNotMidpoint

/-- The constructed median contains its vertex. -/
theorem medianLine_contains_vertex [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (vertexNotMidpoint :
      vertex ≠ Affine.midpoint oppositeFirst oppositeSecond) :
    (medianLine vertex oppositeFirst oppositeSecond vertexNotMidpoint).Contains
      vertex :=
  Incidence.lineThrough_contains_first vertex
    (Affine.midpoint oppositeFirst oppositeSecond) vertexNotMidpoint

/-- The constructed median contains the opposite midpoint. -/
theorem medianLine_contains_midpoint [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (vertexNotMidpoint :
      vertex ≠ Affine.midpoint oppositeFirst oppositeSecond) :
    (medianLine vertex oppositeFirst oppositeSecond vertexNotMidpoint).Contains
      (Affine.midpoint oppositeFirst oppositeSecond) :=
  Incidence.lineThrough_contains_second vertex
    (Affine.midpoint oppositeFirst oppositeSecond) vertexNotMidpoint

/-- The constructed line is a median in the source's incidence definition. -/
theorem medianLine_isMedianLine [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (vertexNotMidpoint :
      vertex ≠ Affine.midpoint oppositeFirst oppositeSecond) :
    IsMedianLine
      (medianLine vertex oppositeFirst oppositeSecond vertexNotMidpoint)
      vertex oppositeFirst oppositeSecond :=
  ⟨medianLine_contains_vertex vertex oppositeFirst oppositeSecond
      vertexNotMidpoint,
    medianLine_contains_midpoint vertex oppositeFirst oppositeSecond
      vertexNotMidpoint⟩

/-- Cyclically rotating the three inputs does not change their centroid. -/
theorem centroidPoint_cyclic_left (first second third : Plane.Point K) :
    centroidPoint second third first = centroidPoint first second third := by
  apply Plane.Point.ext <;>
    unfold centroidPoint <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- The other cyclic rotation also preserves the centroid. -/
theorem centroidPoint_cyclic_right (first second third : Plane.Point K) :
    centroidPoint third first second = centroidPoint first second third := by
  apply Plane.Point.ext <;>
    unfold centroidPoint <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- The centroid is one third of the way from a vertex and two thirds of the way toward the opposite midpoint. -/
theorem centroidPoint_eq_median_affineCombination
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    centroidPoint vertex oppositeFirst oppositeSecond =
      Affine.affineCombination ((1 : K) / 3) vertex ((2 : K) / 3)
        (Affine.midpoint oppositeFirst oppositeSecond) := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  apply Plane.Point.ext
  · unfold centroidPoint Affine.affineCombination Affine.midpoint
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (vertex.x + oppositeFirst.x + oppositeSecond.x) * (3 : K)⁻¹ =
          (vertex.x +
            (2 * (2 : K)⁻¹) *
              (oppositeFirst.x + oppositeSecond.x)) * (3 : K)⁻¹ := by
                rw [twoInverse]
                ring1
      _ = 1 * (3 : K)⁻¹ * vertex.x +
          2 * (3 : K)⁻¹ *
            ((oppositeFirst.x + oppositeSecond.x) * (2 : K)⁻¹) := by
              ring1
  · unfold centroidPoint Affine.affineCombination Affine.midpoint
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (vertex.y + oppositeFirst.y + oppositeSecond.y) * (3 : K)⁻¹ =
          (vertex.y +
            (2 * (2 : K)⁻¹) *
              (oppositeFirst.y + oppositeSecond.y)) * (3 : K)⁻¹ := by
                rw [twoInverse]
                ring1
      _ = 1 * (3 : K)⁻¹ * vertex.y +
          2 * (3 : K)⁻¹ *
            ((oppositeFirst.y + oppositeSecond.y) * (2 : K)⁻¹) := by
              ring1

/-- Outside characteristic three, the displayed centroid lies on each constructed median line. -/
theorem centroidPoint_on_medianLine [DecidableEq K]
    (vertex oppositeFirst oppositeSecond : Plane.Point K)
    (vertexNotMidpoint :
      vertex ≠ Affine.midpoint oppositeFirst oppositeSecond)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    (medianLine vertex oppositeFirst oppositeSecond vertexNotMidpoint).Contains
      (centroidPoint vertex oppositeFirst oppositeSecond) := by
  have threeInverse : (3 : K) * (3 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 3 threeNonzero
  have weightsSum : (1 : K) / 3 + 2 / 3 = 1 := by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      1 * (3 : K)⁻¹ + 2 * (3 : K)⁻¹ =
          3 * (3 : K)⁻¹ := by ring1
      _ = 1 := threeInverse
  unfold medianLine
  rw [centroidPoint_eq_median_affineCombination
    vertex oppositeFirst oppositeSecond twoNonzero]
  exact Affine.affineCombination_on_line vertex
    (Affine.midpoint oppositeFirst oppositeSecond) vertexNotMidpoint
    ((1 : K) / 3) (2 / 3) weightsSum

/-- In characteristic three, two consecutive medians are parallel. The calculation is uniform in the vertices and uses
only the source's visible characteristic-two exclusion for midpoint normalization. -/
theorem consecutive_medianLines_parallel_of_three_eq_zero [DecidableEq K]
    (first second third : Plane.Point K)
    (firstNotMidpoint : first ≠ Affine.midpoint second third)
    (secondNotMidpoint : second ≠ Affine.midpoint third first)
    (twoNonzero : (2 : K) ≠ 0)
    (threeZero : (3 : K) = 0) :
    (medianLine first second third firstNotMidpoint).Parallel
      (medianLine second third first secondNotMidpoint) := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have twoEqualsNegativeOne : (2 : K) = -1 := by
    calc
      (2 : K) = 3 - 1 := by ring1
      _ = -1 := by rw [threeZero]; ring1
  have inverseTwoEqualsNegativeOne : (2 : K)⁻¹ = -1 := by
    calc
      (2 : K)⁻¹ = -(2 * (2 : K)⁻¹) := by
        rw [twoEqualsNegativeOne]
        ring1
      _ = -1 := by rw [twoInverse]
  unfold medianLine Incidence.lineThrough Affine.midpoint Line.Parallel
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [inverseTwoEqualsNegativeOne]
  ring1

/-- A line containing an endpoint and the midpoint contains the other endpoint when two is nonzero. -/
private theorem line_contains_other_endpoint_of_midpoint
    (line : Plane.Line K) (first second : Plane.Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (containsFirst : line.Contains first)
    (containsMidpoint : line.Contains (Affine.midpoint first second)) :
    line.Contains second := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold Plane.Line.Contains at containsFirst containsMidpoint ⊢
  unfold Affine.midpoint at containsMidpoint
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] at containsMidpoint
  calc
    line.a * second.x + line.b * second.y + line.c =
        2 *
            (line.a * ((first.x + second.x) * (2 : K)⁻¹) +
              line.b * ((first.y + second.y) * (2 : K)⁻¹) + line.c) -
          (line.a * first.x + line.b * first.y + line.c) +
          (1 - 2 * (2 : K)⁻¹) *
            (line.a * first.x + line.b * first.y +
              line.a * second.x + line.b * second.y) := by
                ring1
    _ = 0 := by
      rw [containsMidpoint, containsFirst, twoInverse]
      ring1

/-- Outside characteristic three, consecutive medians of a noncollinear triangle cannot be parallel. Their common
centroid would otherwise identify the two lines, forcing all three vertices onto the first median. -/
theorem consecutive_medianLines_nonparallel_of_three_ne_zero
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstNotMidpoint : first ≠ Affine.midpoint second third)
    (secondNotMidpoint : second ≠ Affine.midpoint third first)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (threeNonzero : (3 : K) ≠ 0) :
    ¬ (medianLine first second third firstNotMidpoint).Parallel
        (medianLine second third first secondNotMidpoint) := by
  intro parallel
  let firstMedian := medianLine first second third firstNotMidpoint
  let secondMedian := medianLine second third first secondNotMidpoint
  let centroid := centroidPoint first second third
  have firstContainsCentroid : firstMedian.Contains centroid := by
    unfold firstMedian centroid
    exact centroidPoint_on_medianLine first second third firstNotMidpoint
      twoNonzero threeNonzero
  have secondContainsRotatedCentroid :
      secondMedian.Contains (centroidPoint second third first) := by
    unfold secondMedian
    exact centroidPoint_on_medianLine second third first secondNotMidpoint
      twoNonzero threeNonzero
  have secondContainsCentroid : secondMedian.Contains centroid := by
    unfold centroid
    rw [← centroidPoint_cyclic_left first second third]
    exact secondContainsRotatedCentroid
  have equivalent := Relations.line_equivalent_of_parallel_and_common_point
    firstMedian secondMedian centroid parallel
    firstContainsCentroid secondContainsCentroid
  have firstContainsSecond : firstMedian.Contains second :=
    Relations.line_contains_of_equivalent (Plane.Line.equivalent_symm equivalent) second
      (by
        unfold secondMedian
        exact medianLine_contains_vertex second third first
          secondNotMidpoint)
  have firstContainsThird : firstMedian.Contains third :=
    line_contains_other_endpoint_of_midpoint firstMedian second third
      twoNonzero firstContainsSecond
      (by
        unfold firstMedian
        exact medianLine_contains_midpoint first second third
          firstNotMidpoint)
  apply notCollinear
  exact ⟨firstMedian,
    by
      unfold firstMedian
      exact medianLine_contains_vertex first second third firstNotMidpoint,
    firstContainsSecond, firstContainsThird⟩

/-- Exercise 3.16: the three explicitly constructed medians are pairwise parallel in characteristic three. Otherwise
they are pairwise nonparallel and concurrent at the displayed centroid `[(x₁+x₂+x₃)/3,(y₁+y₂+y₃)/3]`. -/
theorem exercise_3_16 [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    ∃ firstMedian secondMedian thirdMedian : Plane.Line K,
      IsMedianLine firstMedian first second third ∧
        IsMedianLine secondMedian second third first ∧
        IsMedianLine thirdMedian third first second ∧
        (((3 : K) = 0 ∧
            firstMedian.Parallel secondMedian ∧
            secondMedian.Parallel thirdMedian ∧
            thirdMedian.Parallel firstMedian) ∨
          ((3 : K) ≠ 0 ∧
            firstMedian.Contains (centroidPoint first second third) ∧
            secondMedian.Contains (centroidPoint first second third) ∧
            thirdMedian.Contains (centroidPoint first second third) ∧
            ¬ firstMedian.Parallel secondMedian ∧
            ¬ secondMedian.Parallel thirdMedian ∧
            ¬ thirdMedian.Parallel firstMedian)) := by
  have secondCyclicNotCollinear : ¬ Incidence.Collinear second third first :=
    not_collinear_cyclic_left notCollinear
  have thirdCyclicNotCollinear : ¬ Incidence.Collinear third first second :=
    not_collinear_cyclic_right notCollinear
  let firstNotMidpoint := vertex_ne_opposite_midpoint
    first second third notCollinear twoNonzero
  let secondNotMidpoint := vertex_ne_opposite_midpoint
    second third first secondCyclicNotCollinear twoNonzero
  let thirdNotMidpoint := vertex_ne_opposite_midpoint
    third first second thirdCyclicNotCollinear twoNonzero
  let firstMedian := medianLine first second third firstNotMidpoint
  let secondMedian := medianLine second third first secondNotMidpoint
  let thirdMedian := medianLine third first second thirdNotMidpoint
  refine ⟨firstMedian, secondMedian, thirdMedian, ?_, ?_, ?_, ?_⟩
  · unfold firstMedian
    exact medianLine_isMedianLine first second third firstNotMidpoint
  · unfold secondMedian
    exact medianLine_isMedianLine second third first secondNotMidpoint
  · unfold thirdMedian
    exact medianLine_isMedianLine third first second thirdNotMidpoint
  by_cases threeZero : (3 : K) = 0
  · left
    exact ⟨threeZero,
      consecutive_medianLines_parallel_of_three_eq_zero
        first second third firstNotMidpoint secondNotMidpoint
        twoNonzero threeZero,
      consecutive_medianLines_parallel_of_three_eq_zero
        second third first secondNotMidpoint thirdNotMidpoint
        twoNonzero threeZero,
      consecutive_medianLines_parallel_of_three_eq_zero
        third first second thirdNotMidpoint firstNotMidpoint
        twoNonzero threeZero⟩
  · right
    have firstContains := centroidPoint_on_medianLine
      first second third firstNotMidpoint twoNonzero threeZero
    have secondContains := centroidPoint_on_medianLine
      second third first secondNotMidpoint twoNonzero threeZero
    have thirdContains := centroidPoint_on_medianLine
      third first second thirdNotMidpoint twoNonzero threeZero
    rw [centroidPoint_cyclic_left first second third] at secondContains
    rw [centroidPoint_cyclic_right first second third] at thirdContains
    exact ⟨threeZero, firstContains, secondContains, thirdContains,
      consecutive_medianLines_nonparallel_of_three_ne_zero
        first second third firstNotMidpoint secondNotMidpoint notCollinear
        twoNonzero threeZero,
      consecutive_medianLines_nonparallel_of_three_ne_zero
        second third first secondNotMidpoint thirdNotMidpoint
        secondCyclicNotCollinear twoNonzero threeZero,
      consecutive_medianLines_nonparallel_of_three_ne_zero
        third first second thirdNotMidpoint firstNotMidpoint
        thirdCyclicNotCollinear twoNonzero threeZero⟩

end Purelib.Geometry

end

end

end
