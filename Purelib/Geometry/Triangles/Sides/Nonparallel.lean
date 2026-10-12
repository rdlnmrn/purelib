module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, Exercises 3.11–3.12

A triangle is kept as three displayed points with explicit distinctness and
noncollinearity certificates.  Right vertices are perpendicularity equations
between its three finite side lines.  Null-side impossibility exposes the
book's standing characteristic-not-two assumption.
-/

namespace Purelib.Geometry.Triangles.Sides.Nonparallel

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Every pair of sides of a noncollinear triangle is nonparallel.

The side lines are constructed from the retained distinctness proofs. -/
public theorem triangle_side_pairs_nonparallel
    [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).Parallel
        (Incidence.lineThrough second third secondThirdDistinct) ∧
      ¬ (Incidence.lineThrough second third secondThirdDistinct).Parallel
        (Incidence.lineThrough first third firstThirdDistinct) ∧
      ¬ (Incidence.lineThrough first third firstThirdDistinct).Parallel
        (Incidence.lineThrough first second firstSecondDistinct) := by
  constructor
  · intro parallel
    apply notCollinear
    let firstSide := Incidence.lineThrough first second firstSecondDistinct
    let secondSide := Incidence.lineThrough second third secondThirdDistinct
    have equivalent := Relations.line_equivalent_of_parallel_and_common_point
      firstSide secondSide second parallel
      (Incidence.lineThrough_contains_second first second firstSecondDistinct)
      (Incidence.lineThrough_contains_first second third secondThirdDistinct)
    have containsThird : firstSide.Contains third :=
      Relations.line_contains_of_equivalent (Plane.Line.equivalent_symm equivalent) third
        (Incidence.lineThrough_contains_second second third secondThirdDistinct)
    exact ⟨firstSide,
      Incidence.lineThrough_contains_first first second firstSecondDistinct,
      Incidence.lineThrough_contains_second first second firstSecondDistinct,
      containsThird⟩
  constructor
  · intro parallel
    apply notCollinear
    let secondSide := Incidence.lineThrough second third secondThirdDistinct
    let thirdSide := Incidence.lineThrough first third firstThirdDistinct
    have equivalent := Relations.line_equivalent_of_parallel_and_common_point
      secondSide thirdSide third parallel
      (Incidence.lineThrough_contains_second second third secondThirdDistinct)
      (Incidence.lineThrough_contains_second first third firstThirdDistinct)
    have containsFirst : secondSide.Contains first :=
      Relations.line_contains_of_equivalent (Plane.Line.equivalent_symm equivalent) first
        (Incidence.lineThrough_contains_first first third firstThirdDistinct)
    exact ⟨secondSide, containsFirst,
      Incidence.lineThrough_contains_first second third secondThirdDistinct,
      Incidence.lineThrough_contains_second second third secondThirdDistinct⟩
  · intro parallel
    apply notCollinear
    let thirdSide := Incidence.lineThrough first third firstThirdDistinct
    let firstSide := Incidence.lineThrough first second firstSecondDistinct
    have equivalent := Relations.line_equivalent_of_parallel_and_common_point
      thirdSide firstSide first parallel
      (Incidence.lineThrough_contains_first first third firstThirdDistinct)
      (Incidence.lineThrough_contains_first first second firstSecondDistinct)
    have containsSecond : thirdSide.Contains second :=
      Relations.line_contains_of_equivalent (Plane.Line.equivalent_symm equivalent) second
        (Incidence.lineThrough_contains_second first second firstSecondDistinct)
    exact ⟨thirdSide,
      Incidence.lineThrough_contains_first first third firstThirdDistinct,
      containsSecond,
      Incidence.lineThrough_contains_second first third firstThirdDistinct⟩

end Purelib.Geometry.Triangles.Sides.Nonparallel

end

end
