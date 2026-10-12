module

import Purelib.Algebra.Field.Squares
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

section
/-!
# Divine Proportions, §16.1: circle chords

The source introduces a square root of `-1` while excluding null chords.  The
proof here stays constructive: two cleared square identities show directly
that equal-radius points with null separation would force the radius to vanish.
-/

public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Two points on a null displayed line have zero mutual quadrance. -/
theorem quadrance_eq_zero_of_null_line_contains [DecidableEq K]
    (line : Plane.Line K) (lineNull : line.IsNull)
    (first second : Plane.Point K)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    Quadrance.quadrance first second = 0 := by
  have directionEquation :
      line.a * (second.x - first.x) +
        line.b * (second.y - first.y) = 0 := by
    unfold Plane.Line.Contains at containsFirst containsSecond
    calc
      line.a * (second.x - first.x) +
          line.b * (second.y - first.y) =
        (line.a * second.x + line.b * second.y + line.c) -
          (line.a * first.x + line.b * first.y + line.c) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond]; ring1
  have aNonzero : line.a ≠ 0 := by
    by_cases aZero : line.a = 0
    · have bSquareZero : line.b * line.b = 0 := by
        calc
          line.b * line.b = line.a ^ 2 + line.b ^ 2 := by
            rw [aZero]
            ring1
          _ = 0 := lineNull
      have bZero : line.b = 0 := by
        by_cases bZero : line.b = 0
        · exact bZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero bZero bZero) bSquareZero)
      rcases line.direction_nonzero with aNonzero | bNonzero
      · exact False.elim (aNonzero aZero)
      · exact False.elim (bNonzero bZero)
    · exact aZero
  have aSquareNonzero : line.a ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero aNonzero aNonzero
  have squareProductsEqual :
      line.a ^ 2 * (second.x - first.x) ^ 2 =
        line.b ^ 2 * (second.y - first.y) ^ 2 := by
    have linearEquality :
        line.a * (second.x - first.x) =
          -(line.b * (second.y - first.y)) := by
      calc
        line.a * (second.x - first.x) =
            (line.a * (second.x - first.x) +
              line.b * (second.y - first.y)) -
              line.b * (second.y - first.y) := by ring1
        _ = -(line.b * (second.y - first.y)) := by
          rw [directionEquation]
          ring1
    calc
      line.a ^ 2 * (second.x - first.x) ^ 2 =
          (line.a * (second.x - first.x)) ^ 2 := by ring1
      _ = (-(line.b * (second.y - first.y))) ^ 2 := by rw [linearEquality]
      _ = line.b ^ 2 * (second.y - first.y) ^ 2 := by ring1
  apply ExplicitField.eq_zero_of_mul_eq_zero_left aSquareNonzero
  calc
    line.a ^ 2 * Quadrance.quadrance first second =
        line.a ^ 2 * (second.x - first.x) ^ 2 +
          line.a ^ 2 * (second.y - first.y) ^ 2 := by
      unfold Quadrance.quadrance
      ring1
    _ = line.b ^ 2 * (second.y - first.y) ^ 2 +
        line.a ^ 2 * (second.y - first.y) ^ 2 := by
      rw [squareProductsEqual]
    _ = (line.a ^ 2 + line.b ^ 2) *
        (second.y - first.y) ^ 2 := by ring1
    _ = 0 := by rw [lineNull]; ring1
end

end Purelib.Curves.Plane.Conic

end

end

section
/-!
# Divine Proportions, Exercise 16.6: antipodal quadrance sums

The printed exercise omits a non-null hypothesis.  An executable `F₅`
counterexample below shows that the claim fails on a null circle.  For a
non-null circle, its displayed intersection makes every diameter non-null;
midpoint uniqueness then identifies the two equidistant diameter points as
antipodes, giving an explicit constant quadrance sum.
-/

public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- Nullness is invariant under the project's quotient-free line equivalence. The proof uses the two-dimensional
dot/determinant norm identity. -/
public theorem nonNull_of_equivalent [DecidableEq K]
    (left right : Plane.Line K) (equivalent : left.Equivalent right)
    (rightNonNull : ¬ right.IsNull) :
    ¬ left.IsNull := by
  intro leftNull
  let dot := left.a * right.a + left.b * right.b
  let determinant := left.a * right.b - left.b * right.a
  have determinantZero : determinant = 0 := by
    unfold determinant
    calc
      left.a * right.b - left.b * right.a =
          right.a * left.b - left.b * right.a := by rw [equivalent.1]
      _ = 0 := by ring1
  have dotSquareZero : dot ^ 2 = 0 := by
    calc
      dot ^ 2 = dot ^ 2 + determinant ^ 2 := by
        rw [determinantZero]
        ring1
      _ = (left.a ^ 2 + left.b ^ 2) *
          (right.a ^ 2 + right.b ^ 2) := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [leftNull]; ring1
  have dotZero : dot = 0 := by
    by_cases dotZero : dot = 0
    · exact dotZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero dotZero dotZero)
          (by simpa [pow_two] using dotSquareZero))
  have rightNormNonzero : right.a ^ 2 + right.b ^ 2 ≠ 0 :=
    rightNonNull
  have leftATimesNorm :
      left.a * (right.a ^ 2 + right.b ^ 2) = 0 := by
    calc
      left.a * (right.a ^ 2 + right.b ^ 2) =
          right.a * dot + right.b * determinant := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [dotZero, determinantZero]; ring1
  have leftAZero : left.a = 0 := by
    by_cases leftAZero : left.a = 0
    · exact leftAZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero leftAZero rightNormNonzero)
          leftATimesNorm)
  have leftBTimesNorm :
      left.b * (right.a ^ 2 + right.b ^ 2) = 0 := by
    calc
      left.b * (right.a ^ 2 + right.b ^ 2) =
          right.b * dot - right.a * determinant := by
        unfold dot determinant
        ring1
      _ = 0 := by rw [dotZero, determinantZero]; ring1
  have leftBZero : left.b = 0 := by
    by_cases leftBZero : left.b = 0
    · exact leftBZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero leftBZero rightNormNonzero)
          leftBTimesNorm)
  exact left.direction_nonzero.elim
    (fun nonzero => nonzero leftAZero)
    (fun nonzero => nonzero leftBZero)

end

end Purelib.Curves.Plane.Conic

end

end

section
public section

/-!
# Divine Proportions, Exercises 3.3–3.10

These line relations and coordinate formulas use only the three displayed
coefficients of each line.  Parallel directions are related by an explicit
nonzero scale; no slope quotient or projective representative is selected.
-/

namespace Purelib.Geometry.Plane.Line.Null

variable {K : Type*} [ExplicitField K]

/-- The line with coefficient triple one, root and offset.

It is null when the supplied root squares to minus one; the definition itself accepts any root. -/
@[expose] def positiveNullLine [Nontrivial K] (root offset : K) :
  Plane.Line K where
  a := 1
  b := root
  c := offset
  direction_nonzero := Or.inl one_ne_zero

/-- The line with coefficient triple one, negative root and offset.

It is null when the supplied root squares to minus one; the definition itself accepts any root. -/
@[expose] def negativeNullLine [Nontrivial K] (root offset : K) :
  Plane.Line K where
  a := 1
  b := -root
  c := offset
  direction_nonzero := Or.inl one_ne_zero

/-- The line through the supplied point with coefficients one and root.

The direction is null when the supplied root squares to minus one. -/
@[expose] def positiveNullLineThrough [Nontrivial K]
    (root : K) (point : Plane.Point K) : Plane.Line K :=
  positiveNullLine root (-point.x - root * point.y)

/-- The line through the supplied point with coefficients one and negative root.

The direction is null when the supplied root squares to minus one. -/
@[expose] def negativeNullLineThrough [Nontrivial K]
    (root : K) (point : Plane.Point K) : Plane.Line K :=
  negativeNullLine root (-point.x + root * point.y)

section
open _root_.Purelib.Geometry
/-- The first direction coefficient of a null displayed line is nonzero. -/
private theorem nullLine_first_coefficient_nonzero
    [DecidableEq K] (line : Line K) (nullLine : line.IsNull) :
    line.a ≠ 0 := by
  intro firstZero
  rcases line.direction_nonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · have secondSquareZero : line.b ^ 2 = 0 := by
      unfold IsNull at nullLine
      calc
        line.b ^ 2 = line.a ^ 2 + line.b ^ 2 := by
          rw [firstZero]
          ring1
        _ = 0 := nullLine
    have secondProductZero : line.b * line.b = 0 := by
      calc
        line.b * line.b = line.b ^ 2 := by ring1
        _ = 0 := secondSquareZero
    exact (ExplicitField.mul_ne_zero secondNonzero secondNonzero)
      secondProductZero
end

/-- Any displayed null line constructively supplies a square root of `-1`. The witness is its second direction
coefficient divided by its first. -/
theorem squareRootNegativeOne_of_nullLine [DecidableEq K]
    (line : Plane.Line K) (nullLine : line.IsNull) :
    ∃ root : K, root ^ 2 = -1 := by
  have firstNonzero := nullLine_first_coefficient_nonzero line nullLine
  have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel line.a firstNonzero
  have secondSquare : line.b ^ 2 = -(line.a ^ 2) := by
    unfold Plane.Line.IsNull at nullLine
    calc
      line.b ^ 2 =
          -(line.a ^ 2) + (line.a ^ 2 + line.b ^ 2) := by ring1
      _ = -(line.a ^ 2) := by rw [nullLine]; ring1
  refine ⟨line.b / line.a, ?_⟩
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (line.b * line.a⁻¹) ^ 2 =
        line.b ^ 2 * (line.a⁻¹) ^ 2 := by ring1
    _ = -(line.a ^ 2) * (line.a⁻¹) ^ 2 := by rw [secondSquare]
    _ = -(line.a * line.a⁻¹) ^ 2 := by ring1
    _ = -1 := by rw [firstCancel]; ring1

/-- Every null line through `point` has one of the two displayed null directions. Equality is the project's
quotient-free `Line.Equivalent` relation on coefficient triples. -/
theorem nullLine_through_equivalent_positive_or_negative
    [Nontrivial K] [DecidableEq K]
    (root : K) (rootSquare : root ^ 2 = -1)
    (point : Plane.Point K) (line : Plane.Line K)
    (contains : line.Contains point) (nullLine : line.IsNull) :
    line.Equivalent (positiveNullLineThrough root point) ∨
      line.Equivalent (negativeNullLineThrough root point) := by
  have factorZero :
      (line.b - root * line.a) * (line.b + root * line.a) = 0 := by
    unfold Plane.Line.IsNull at nullLine
    calc
      (line.b - root * line.a) * (line.b + root * line.a) =
          line.b ^ 2 - root ^ 2 * line.a ^ 2 := by ring1
      _ = line.b ^ 2 + line.a ^ 2 := by rw [rootSquare]; ring1
      _ = line.a ^ 2 + line.b ^ 2 := by ring1
      _ = 0 := nullLine
  by_cases positiveFactorZero : line.b - root * line.a = 0
  · have secondCoefficient : line.b = root * line.a := by
      calc
        line.b = (line.b - root * line.a) + root * line.a := by ring1
        _ = root * line.a := by rw [positiveFactorZero]; ring1
    have constantCoefficient :
        line.c = line.a * (-point.x - root * point.y) := by
      unfold Plane.Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
        _ = line.a * (-point.x - root * point.y) := by
          rw [secondCoefficient]
          ring1
    left
    unfold Plane.Line.Equivalent positiveNullLineThrough positiveNullLine
    exact ⟨by rw [secondCoefficient]; ring1,
      by rw [constantCoefficient]; ring1,
      by rw [secondCoefficient, constantCoefficient]; ring1⟩
  · have negativeFactorZero : line.b + root * line.a = 0 := by
      by_cases negativeZero : line.b + root * line.a = 0
      · exact negativeZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero positiveFactorZero negativeZero)
            factorZero)
    have secondCoefficient : line.b = -root * line.a := by
      calc
        line.b = (line.b + root * line.a) - root * line.a := by ring1
        _ = -root * line.a := by rw [negativeFactorZero]; ring1
    have constantCoefficient :
        line.c = line.a * (-point.x + root * point.y) := by
      unfold Plane.Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
        _ = line.a * (-point.x + root * point.y) := by
          rw [secondCoefficient]
          ring1
    right
    unfold Plane.Line.Equivalent negativeNullLineThrough negativeNullLine
    exact ⟨by rw [secondCoefficient]; ring1,
      by rw [constantCoefficient]; ring1,
      by rw [secondCoefficient, constantCoefficient]; ring1⟩

/-- When `2 ≠ 0`, the two displayed null directions are inequivalent. -/
theorem positiveNullLineThrough_not_equivalent_negative
    [Nontrivial K]
    (root : K) (rootSquare : root ^ 2 = -1)
    (point : Plane.Point K) (twoNonzero : (2 : K) ≠ 0) :
    ¬ (positiveNullLineThrough root point).Equivalent
        (negativeNullLineThrough root point) := by
  intro equivalent
  have negativeRootEqualsRoot : -root = root := by
    calc
      -root = (1 : K) * -root := by ring1
      _ = 1 * root := equivalent.1
      _ = root := by ring1
  have twiceRootZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root - (-root) := by ring1
      _ = 0 := by rw [negativeRootEqualsRoot]; ring1
  exact (ExplicitField.mul_ne_zero twoNonzero
    (Purelib.Algebra.Field.Squares.root_ne_zero_of_square_eq_negative_one root rootSquare)) twiceRootZero

/-- Exercise 3.3: from the existence of one null line, construct exactly two inequivalent null lines through any
requested point and classify every other null line through that point into one of those two directions. -/
theorem exercise_3_3 [Nontrivial K] [DecidableEq K]
    (point : Plane.Point K) (witness : Plane.Line K)
    (witnessNull : witness.IsNull) (twoNonzero : (2 : K) ≠ 0) :
    ∃ positive negative : Plane.Line K,
      positive.Contains point ∧ positive.IsNull ∧
        negative.Contains point ∧ negative.IsNull ∧
        ¬ positive.Equivalent negative ∧
        ∀ line : Plane.Line K,
          line.Contains point → line.IsNull →
            line.Equivalent positive ∨ line.Equivalent negative := by
  rcases squareRootNegativeOne_of_nullLine witness witnessNull with
    ⟨root, rootSquare⟩
  let positive := positiveNullLineThrough root point
  let negative := negativeNullLineThrough root point
  refine ⟨positive, negative, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold positive positiveNullLineThrough positiveNullLine Plane.Line.Contains
    ring1
  · unfold positive positiveNullLineThrough positiveNullLine Plane.Line.IsNull
    rw [rootSquare]
    ring1
  · unfold negative negativeNullLineThrough negativeNullLine Plane.Line.Contains
    ring1
  · unfold negative negativeNullLineThrough negativeNullLine Plane.Line.IsNull
    rw [show (-root) ^ 2 = root ^ 2 by ring1, rootSquare]
    ring1
  · unfold positive negative
    exact positiveNullLineThrough_not_equivalent_negative root rootSquare
      point twoNonzero
  · intro line contains nullLine
    unfold positive negative
    exact nullLine_through_equivalent_positive_or_negative
      root rootSquare point line contains nullLine

/-- Exercise 3.6: within either displayed null family, every pair of lines is both parallel and perpendicular. -/
theorem exercise_3_6 [Nontrivial K]
    (root firstOffset secondOffset : K)
    (rootSquare : root ^ 2 = -1) :
    (positiveNullLine root firstOffset).IsNull ∧
      (positiveNullLine root secondOffset).IsNull ∧
      (positiveNullLine root firstOffset).Parallel
        (positiveNullLine root secondOffset) ∧
      (positiveNullLine root firstOffset).Perpendicular
        (positiveNullLine root secondOffset) ∧
      (negativeNullLine root firstOffset).IsNull ∧
      (negativeNullLine root secondOffset).IsNull ∧
      (negativeNullLine root firstOffset).Parallel
        (negativeNullLine root secondOffset) ∧
      (negativeNullLine root firstOffset).Perpendicular
        (negativeNullLine root secondOffset) := by
  have positiveNullIdentity : (1 : K) ^ 2 + root ^ 2 = 0 := by
    rw [rootSquare]
    ring1
  have negativeNullIdentity : (1 : K) ^ 2 + (-root) ^ 2 = 0 := by
    rw [show (-root) ^ 2 = root ^ 2 by ring1, rootSquare]
    ring1
  constructor
  · exact positiveNullIdentity
  constructor
  · exact positiveNullIdentity
  constructor
  · unfold Plane.Line.Parallel positiveNullLine
    ring1
  constructor
  · unfold Plane.Line.Perpendicular positiveNullLine
    calc
      (1 : K) * 1 + root * root = 1 ^ 2 + root ^ 2 := by ring1
      _ = 0 := positiveNullIdentity
  constructor
  · exact negativeNullIdentity
  constructor
  · exact negativeNullIdentity
  constructor
  · unfold Plane.Line.Parallel negativeNullLine
    ring1
  · unfold Plane.Line.Perpendicular negativeNullLine
    calc
      (1 : K) * 1 + -root * -root = 1 ^ 2 + (-root) ^ 2 := by ring1
      _ = 0 := negativeNullIdentity
end Purelib.Geometry.Plane.Line.Null

end

end

section
public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

namespace Purelib.Geometry.Plane.Line.Null

variable {K : Type*} [ExplicitField K]

section
open _root_.Purelib.Geometry
/-- Reversing the endpoints of a non-null displayed line preserves non-nullness. -/
private theorem lineThrough_reverse_nonNull
  [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (forwardNonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    ¬ (Incidence.lineThrough second first distinct.symm).IsNull := by
  intro reverseNull
  apply forwardNonNull
  change Line.Basic.lineNorm (Incidence.lineThrough first second distinct) = 0
  change Line.Basic.lineNorm (Incidence.lineThrough second first distinct.symm) = 0 at reverseNull
  rw [Quadrance.lineThrough_norm_eq_quadrance first second distinct,
    Quadrance.quadrance_symm first second,
    ← Quadrance.lineThrough_norm_eq_quadrance second first distinct.symm]
  exact reverseNull
end

end Purelib.Geometry.Plane.Line.Null

end

section
public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Plane.Line.Null

variable {K : Type*} [ExplicitField K]

/-- A displayed line parallel to a non-null line is itself non-null. The proof uses the explicit nonzero direction scale
rather than selecting a representative of a line quotient. -/
theorem nonNull_of_parallel [DecidableEq K]
    (source target : Plane.Line K) (sourceNonNull : ¬ source.IsNull)
    (parallel : source.Parallel target) : ¬ target.IsNull := by
  rcases Relations.direction_scale_of_parallel source target parallel with
    ⟨scale, scaleNonzero, targetA, targetB⟩
  intro targetNull
  have scaleSquaredNonzero : scale * scale ≠ 0 :=
    ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
  have scaledNormNonzero :
      (scale * scale) * (source.a ^ 2 + source.b ^ 2) ≠ 0 :=
    ExplicitField.mul_ne_zero scaleSquaredNonzero sourceNonNull
  apply scaledNormNonzero
  calc
    (scale * scale) * (source.a ^ 2 + source.b ^ 2) =
        target.a ^ 2 + target.b ^ 2 := by
      rw [targetA, targetB]
      ring1
    _ = 0 := targetNull
end Purelib.Geometry.Plane.Line.Null

end

section
public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace Purelib.Geometry.Plane.Line.Null

variable {K : Type*} [ExplicitField K]

section
open _root_.Purelib.Geometry
/-- Reversing the endpoints of a non-null displayed line preserves non-nullness. -/
theorem reversedLine_nonNull [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    ¬ (Incidence.lineThrough second first distinct.symm).IsNull := by
  intro reversedNull
  apply nonNull
  apply (Quadrance.null_line_iff_quadrance_zero first second distinct).2
  have reversedQuadranceZero :=
    (Quadrance.null_line_iff_quadrance_zero second first distinct.symm).1 reversedNull
  calc
    Quadrance.quadrance first second = Quadrance.quadrance second first :=
      Quadrance.quadrance_symm first second
    _ = 0 := reversedQuadranceZero
end

end Purelib.Geometry.Plane.Line.Null

end

end
