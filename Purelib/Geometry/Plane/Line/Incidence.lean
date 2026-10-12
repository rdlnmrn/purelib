module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.LinearAlgebra.Alternating.Bracket.Fin3
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.LinearAlgebra.Alternating.Bracket

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace Purelib.Geometry.Plane.Line.Incidence

variable {K : Type*}

section Incidence

variable [ExplicitField K]

/-- The signed determinant used by the Collinear points theorem. -/
def pointDeterminant (first second third : Point K) : K
  :=
  first.x * second.y - first.x * third.y +
    second.x * third.y - third.x * second.y +
    third.x * first.y - second.x * first.y

/-- Three points are collinear when one displayed line contains all three. -/
def Collinear (first second third : Point K) : Prop :=
  ∃ line : Line K,
    line.Contains first ∧ line.Contains second ∧ line.Contains third

/-- The explicit coefficient triple through two distinct points. -/
def lineThrough [DecidableEq K] (first second : Plane.Point K)
    (distinct : first ≠ second) : Line K where
  a := first.y - second.y
  b := second.x - first.x
  c := first.x * second.y - second.x * first.y
  direction_nonzero := by
    by_cases sameY : first.y = second.y
    · right
      apply ExplicitField.sub_ne_zero_of_ne
      intro sameX
      apply distinct
      apply Plane.Point.ext
      · exact sameX.symm
      · exact sameY
    · exact Or.inl (ExplicitField.sub_ne_zero_of_ne sameY)

/-- The first coefficient of the line through two points is their second-coordinate difference. -/
@[simp] theorem lineThrough_a [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).a = first.y - second.y := rfl

/-- The second coefficient of the line through two points is their reversed first-coordinate difference. -/
@[simp] theorem lineThrough_b [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).b = second.x - first.x := rfl

/-- The constant coefficient of the line through two points is their coordinate cross product. -/
@[simp] theorem lineThrough_c [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).c =
      first.x * second.y - second.x * first.y := rfl

/-- Theorem 2, existence half: the displayed line contains the first point. -/
theorem lineThrough_contains_first [DecidableEq K] (first second :
  Point K)
    (distinct : first ≠ second) :
    (lineThrough first second distinct).Contains first := by
  unfold Contains lineThrough
  ring1

/-- Theorem 2, existence half: the displayed line contains the second point. -/
theorem lineThrough_contains_second [DecidableEq K] (first second :
  Point K)
    (distinct : first ≠ second) :
    (lineThrough first second distinct).Contains second := by
  unfold Contains lineThrough
  ring1

/-- Theorem 2 (Line through two points), uniqueness up to equality of ordered proportions. No representative is chosen
by quotient or choice. -/
theorem lineThrough_unique [DecidableEq K] (first second :
  Point K)
    (distinct : first ≠ second) (other : Line K)
    (containsFirst : other.Contains first)
    (containsSecond : other.Contains second) :
    (lineThrough first second distinct).Equivalent other := by
  unfold Contains at containsFirst containsSecond
  unfold Equivalent
  constructor
  · calc
      (first.y - second.y) * other.b =
          ((other.a * first.x + other.b * first.y + other.c) -
            (other.a * second.x + other.b * second.y + other.c)) +
            other.a * (second.x - first.x) := by ring1
      _ = other.a * (second.x - first.x) := by
        rw [containsFirst, containsSecond]
        ring1
  constructor
  · calc
      (first.y - second.y) * other.c =
          first.y * (other.a * second.x + other.b * second.y + other.c) -
            second.y * (other.a * first.x + other.b * first.y + other.c) +
            other.a * (first.x * second.y - second.x * first.y) := by ring1
      _ = other.a * (first.x * second.y - second.x * first.y) := by
        rw [containsFirst, containsSecond]
        ring1
  · calc
      (second.x - first.x) * other.c =
          second.x * (other.a * first.x + other.b * first.y + other.c) -
            first.x * (other.a * second.x + other.b * second.y + other.c) +
            other.b * (first.x * second.y - second.x * first.y) := by ring1
      _ = other.b * (first.x * second.y - second.x * first.y) := by
        rw [containsFirst, containsSecond]
        ring1

/-- Three points on one displayed line have zero coordinate determinant. -/
theorem pointDeterminant_eq_zero_of_collinear
    [DecidableEq K]
    {first second third : Point K}
    (collinear : Collinear first second third) :
    pointDeterminant first second third = 0 := by
  rcases collinear with ⟨line, containsFirst, containsSecond, containsThird⟩
  unfold Contains at containsFirst containsSecond containsThird
  have timesA : line.a * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      line.a *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
          (line.a * first.x + line.b * first.y + line.c) *
              (second.y - third.y) +
            (line.a * second.x + line.b * second.y + line.c) *
              (third.y - first.y) +
            (line.a * third.x + line.b * third.y + line.c) *
              (first.y - second.y) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1
  have timesB : line.b * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      line.b *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
          (line.a * first.x + line.b * first.y + line.c) *
              (third.x - second.x) +
            (line.a * second.x + line.b * second.y + line.c) *
              (first.x - third.x) +
            (line.a * third.x + line.b * third.y + line.c) *
              (second.x - first.x) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1
  rcases line.direction_nonzero with aNonzero | bNonzero
  · by_cases determinantZero : pointDeterminant first second third = 0
    · exact determinantZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero aNonzero determinantZero) timesA)
  · by_cases determinantZero : pointDeterminant first second third = 0
    · exact determinantZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero bNonzero determinantZero) timesB)

/-- Three points with zero coordinate determinant lie on a displayed line.

Decidable equality chooses a distinct pair when one exists; in the coincident case a vertical line is constructed
directly. -/
private theorem collinear_of_pointDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (determinantZero : pointDeterminant first second third = 0) :
    Collinear first second third := by
  by_cases firstSecondDistinct : first ≠ second
  · refine ⟨lineThrough first second firstSecondDistinct,
      lineThrough_contains_first first second firstSecondDistinct,
      lineThrough_contains_second first second firstSecondDistinct, ?_⟩
    unfold Contains lineThrough
    unfold pointDeterminant at determinantZero
    calc
      (first.y - second.y) * third.x + (second.x - first.x) * third.y +
          (first.x * second.y - second.x * first.y) =
          first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y := by ring1
      _ = 0 := determinantZero
  · have firstSecondEqual : first = second := by
      by_cases equal : first = second
      · exact equal
      · exact False.elim (firstSecondDistinct equal)
    by_cases firstThirdDistinct : first ≠ third
    · refine ⟨lineThrough first third firstThirdDistinct,
        lineThrough_contains_first first third firstThirdDistinct, ?_,
        lineThrough_contains_second first third firstThirdDistinct⟩
      rw [← firstSecondEqual]
      exact lineThrough_contains_first first third firstThirdDistinct
    · have firstThirdEqual : first = third := by
        by_cases equal : first = third
        · exact equal
        · exact False.elim (firstThirdDistinct equal)
      let line : Line K :=
        { a := 1
          b := 0
          c := -first.x
          direction_nonzero := Or.inl one_ne_zero }
      refine ⟨line, ?_, ?_, ?_⟩
      · unfold line Contains
        ring1
      · rw [← firstSecondEqual]
        unfold line Contains
        ring1
      · rw [← firstThirdEqual]
        unfold line Contains
        ring1

/-- Theorem 3 (Collinear points): the existential incidence definition is equivalent to the six-term determinant formula
in the source. -/
theorem collinear_iff_pointDeterminant_eq_zero
    [Nontrivial K] [DecidableEq K] (first second third : Point K) :
    Collinear first second third ↔ pointDeterminant first
      second third = 0 := by
  exact ⟨pointDeterminant_eq_zero_of_collinear,
    collinear_of_pointDeterminant_eq_zero⟩

/-- The determinant of three displayed line coefficient rows. -/
def lineDeterminant (first second third : Line K) : K :=
  first.a * second.b * third.c - first.a * third.b * second.c +
    second.a * third.b * first.c - third.a * second.b * first.c +
    third.a * first.b * second.c - second.a * first.b * third.c

/-- Theorem 4 (Concurrent lines): three lines containing one displayed point have zero coefficient determinant. -/
theorem lineDeterminant_eq_zero_of_concurrent
    (first second third : Line K) (point : Point K)
    (containsFirst : first.Contains point)
    (containsSecond : second.Contains point)
    (containsThird : third.Contains point) :
    lineDeterminant first second third = 0 := by
  unfold Contains at containsFirst containsSecond containsThird
  unfold lineDeterminant
  calc
    first.a * second.b * third.c - first.a * third.b * second.c +
        second.a * third.b * first.c - third.a * second.b * first.c +
        third.a * first.b * second.c - second.a * first.b * third.c =
      (first.a * point.x + first.b * point.y + first.c) *
          (second.a * third.b - third.a * second.b) -
        (second.a * point.x + second.b * point.y + second.c) *
          (first.a * third.b - third.a * first.b) +
        (third.a * point.x + third.b * point.y + third.c) *
          (first.a * second.b - second.a * first.b) := by ring1
    _ = 0 := by rw [containsFirst, containsSecond, containsThird]; ring1
end Incidence

end Purelib.Geometry.Plane.Line.Incidence

end

end

section
@[expose] public section

/-!
# Divine Proportions, §12.2: the circumcenter formula

The source abbreviates its coordinate numerators with the six-term
antisymmetric bracket `[uv]⁻₁₂₃`.  We expose that polynomial directly and use
it to define the printed circumcenter.  The proof compares its two fractions
with the explicit intersection of two perpendicular bisectors.
-/

namespace Purelib.Geometry.Plane.Line.Incidence

variable {K : Type*} [ExplicitField K]

/-- The coordinate determinant is the basic antisymmetric product `[xy]⁻`. -/
theorem pointDeterminant_eq_antisymmetricTripleProduct
    (first second third : Plane.Point K) :
    pointDeterminant first second third =
      Fin3.antisymmetricTripleProduct
        first.x second.x third.x first.y second.y third.y := by
  unfold pointDeterminant Fin3.antisymmetricTripleProduct
  ring1
end Purelib.Geometry.Plane.Line.Incidence

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10: the isosceles median

The line in Theorem 67 is represented by its vertex and its displayed
intersection with the opposite side.  This keeps all three conditions—altitude,
median, and equal-spread vertex bisector—finite and executable.
-/

namespace Purelib.Geometry.Plane.Line.Incidence

variable {K : Type*} [ExplicitField K]

/-- The line through two distinct points of a displayed line is parallel to that line. -/
theorem lineThrough_parallel_of_contains [DecidableEq K]
    (line : Plane.Line K) (first second : Plane.Point K) (distinct : first ≠ second)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    (lineThrough first second distinct).Parallel line := by
  unfold Plane.Line.Contains at containsFirst containsSecond
  unfold Plane.Line.Parallel lineThrough
  calc
    (first.y - second.y) * line.b -
        line.a * (second.x - first.x) =
      (line.a * first.x + line.b * first.y + line.c) -
        (line.a * second.x + line.b * second.y + line.c) := by ring1
    _ = 0 := by rw [containsFirst, containsSecond]; ring1
end Purelib.Geometry.Plane.Line.Incidence

end

section
/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Line.Incidence

variable {K : Type*} [ExplicitField K]

/-- Swapping the first two vertices preserves noncollinearity. -/
public theorem not_collinear_swap_first_second
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear second first third := by
  intro swapped
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    (collinear_iff_pointDeterminant_eq_zero second first third).1 swapped
  calc
    pointDeterminant first second third =
        -pointDeterminant second first third := by
          unfold pointDeterminant
          ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

/-- Swapping the last two vertices preserves noncollinearity. -/
public theorem not_collinear_swap_second_third
    [Nontrivial K] [DecidableEq K]
    {first second third : Point K}
    (notCollinear : ¬ Collinear first second third) :
    ¬ Collinear first third second := by
  intro swapped
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  have swappedZero :=
    (collinear_iff_pointDeterminant_eq_zero first third second).1 swapped
  calc
    pointDeterminant first second third =
        -pointDeterminant first third second := by
          unfold pointDeterminant
          ring1
    _ = 0 := by rw [swappedZero]; exact neg_zero

/-- Four points are collinear when one displayed line contains all four. -/

def FourCollinear (first second third fourth : Point K) :
  Prop :=
  ∃ line : Line K,
    line.Contains first ∧ line.Contains second ∧
      line.Contains third ∧ line.Contains fourth
end Purelib.Geometry.Plane.Line.Incidence

end

end
