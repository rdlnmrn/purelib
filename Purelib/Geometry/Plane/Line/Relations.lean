module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

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

section
public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace Purelib.Geometry.Plane.Line.Relations

variable {K : Type*}

section Incidence

variable [ExplicitField K]

/-- Equivalent coefficient triples are parallel. -/
theorem line_parallel_of_equivalent {first second : Plane.Line K}
    (equivalent : first.Equivalent second) : first.Parallel second := by
  unfold Plane.Line.Equivalent at equivalent
  unfold Plane.Line.Parallel
  rw [equivalent.1]
  ring1

/-- Equivalent displayed lines differ by one explicit coefficient scale. The scale is selected from a displayed nonzero
direction coordinate, with no quotient or choice of a projective representative. -/
theorem line_coefficient_scale_of_equivalent (source target :
  Plane.Line K)
    (equivalent : source.Equivalent target) :
    ∃ scale : K,
      target.a = scale * source.a ∧
      target.b = scale * source.b ∧
      target.c = scale * source.c := by
  rcases source.direction_nonzero with sourceANonzero | sourceBNonzero
  · let scale := target.a / source.a
    have inverseCancel : source.a⁻¹ * source.a = (1 : K) := by
      calc
        source.a⁻¹ * source.a = source.a * source.a⁻¹ := by ring1
        _ = 1 := ExplicitField.mul_inv_cancel source.a sourceANonzero
    refine ⟨scale, ?_, ?_, ?_⟩
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.a = target.a * 1 := by ring1
        _ = target.a * (source.a⁻¹ * source.a) := by rw [inverseCancel]
        _ = (target.a * source.a⁻¹) * source.a := by ring1
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.b = 1 * target.b := by ring1
        _ = (source.a⁻¹ * source.a) * target.b := by rw [inverseCancel]
        _ = source.a⁻¹ * (source.a * target.b) := by ring1
        _ = source.a⁻¹ * (target.a * source.b) := by rw [equivalent.1]
        _ = (target.a * source.a⁻¹) * source.b := by ring1
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.c = 1 * target.c := by ring1
        _ = (source.a⁻¹ * source.a) * target.c := by rw [inverseCancel]
        _ = source.a⁻¹ * (source.a * target.c) := by ring1
        _ = source.a⁻¹ * (target.a * source.c) := by rw [equivalent.2.1]
        _ = (target.a * source.a⁻¹) * source.c := by ring1
  · let scale := target.b / source.b
    have inverseCancel : source.b⁻¹ * source.b = (1 : K) := by
      calc
        source.b⁻¹ * source.b = source.b * source.b⁻¹ := by ring1
        _ = 1 := ExplicitField.mul_inv_cancel source.b sourceBNonzero
    refine ⟨scale, ?_, ?_, ?_⟩
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.a = target.a * 1 := by ring1
        _ = target.a * (source.b * source.b⁻¹) := by
          rw [ExplicitField.mul_inv_cancel source.b sourceBNonzero]
        _ = source.b⁻¹ * (target.a * source.b) := by ring1
        _ = source.b⁻¹ * (source.a * target.b) := by rw [equivalent.1]
        _ = (target.b * source.b⁻¹) * source.a := by ring1
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.b = target.b * 1 := by ring1
        _ = target.b * (source.b⁻¹ * source.b) := by rw [inverseCancel]
        _ = (target.b * source.b⁻¹) * source.b := by ring1
    · unfold scale
      simp only [ExplicitField.div_eq_mul_inv]
      calc
        target.c = 1 * target.c := by ring1
        _ = (source.b⁻¹ * source.b) * target.c := by rw [inverseCancel]
        _ = source.b⁻¹ * (source.b * target.c) := by ring1
        _ = source.b⁻¹ * (target.b * source.c) := by rw [equivalent.2.2]
        _ = (target.b * source.b⁻¹) * source.c := by ring1

/-- Transitivity of quotient-free line equality. -/
theorem line_equivalent_trans {first second third : Plane.Line K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases line_coefficient_scale_of_equivalent first second firstSecond with
    ⟨firstScale, secondA, secondB, secondC⟩
  rcases line_coefficient_scale_of_equivalent second third secondThird with
    ⟨secondScale, thirdA, thirdB, thirdC⟩
  unfold Plane.Line.Equivalent
  rw [thirdA, thirdB, thirdC, secondA, secondB, secondC]
  constructor
  · ring1
  constructor <;> ring1

/-- Parallelism is transitive for displayed lines. -/
theorem line_parallel_trans {first second third : Plane.Line K}
    (firstSecond : first.Parallel second)
    (secondThird : second.Parallel third) : first.Parallel third := by
  unfold Plane.Line.Parallel at firstSecond secondThird ⊢
  rcases second.direction_nonzero with secondANonzero | secondBNonzero
  · apply ExplicitField.eq_zero_of_mul_eq_zero_left secondANonzero
    calc
      second.a * (first.a * third.b - third.a * first.b) =
          first.a *
              (second.a * third.b - third.a * second.b) +
            third.a *
              (first.a * second.b - second.a * first.b) := by ring1
      _ = 0 := by rw [firstSecond, secondThird]; ring1
  · apply ExplicitField.eq_zero_of_mul_eq_zero_left secondBNonzero
    calc
      second.b * (first.a * third.b - third.a * first.b) =
          third.b *
              (first.a * second.b - second.a * first.b) +
            first.b *
              (second.a * third.b - third.a * second.b) := by ring1
      _ = 0 := by rw [firstSecond, secondThird]; ring1

/-- Parallel direction pairs differ by an explicitly constructed nonzero scale. Constants are intentionally absent
because parallelism depends only on the two direction coefficients. -/
theorem direction_scale_of_parallel [DecidableEq K]
    (source target : Plane.Line K)
    (parallel : source.Parallel target) :
    ∃ scale : K, scale ≠ 0 ∧
      target.a = scale * source.a ∧ target.b = scale * source.b := by
  unfold Plane.Line.Parallel at parallel
  rcases source.direction_nonzero with sourceANonzero | sourceBNonzero
  · have targetANonzero : target.a ≠ 0 := by
      intro targetAZero
      have targetBZero : target.b = 0 := by
        have productZero : source.a * target.b = 0 := by
          calc
            source.a * target.b = target.a * source.b :=
              Group.eq_of_sub_eq_zero parallel
            _ = 0 := by rw [targetAZero]; ring1
        by_cases zero : target.b = 0
        · exact zero
        · exact False.elim
            ((ExplicitField.mul_ne_zero sourceANonzero zero) productZero)
      rcases target.direction_nonzero with targetANonzero | targetBNonzero
      · exact targetANonzero targetAZero
      · exact targetBNonzero targetBZero
    let scale := target.a / source.a
    have scaleNonzero : scale ≠ 0 := by
      unfold scale
      rw [ExplicitField.div_eq_mul_inv]
      exact ExplicitField.mul_ne_zero targetANonzero
        (ExplicitField.inv_ne_zero sourceANonzero)
    refine ⟨scale, scaleNonzero, ?_, ?_⟩
    · exact (ExplicitField.div_mul_cancel target.a sourceANonzero).symm
    · apply (fun {K : Type _} [ExplicitField K] {factor left right : K} (factorNonzero : factor ≠
      0) (productsEqual : factor * left = factor * right) => (ExplicitField.eq_of_mul_eq_mul_left
      (K := K) (left := left) (right := right) (factor := factor) factorNonzero productsEqual : left = right))
        sourceANonzero
      calc
        source.a * target.b = target.a * source.b :=
          Group.eq_of_sub_eq_zero parallel
        _ = source.a * (scale * source.b) := by
          unfold scale
          rw [ExplicitField.div_eq_mul_inv]
          have cancel := ExplicitField.mul_inv_cancel source.a
            sourceANonzero
          calc
            target.a * source.b =
                source.a * source.a⁻¹ * (target.a * source.b) := by
              rw [cancel, one_mul]
            _ = source.a * (target.a * source.a⁻¹ * source.b) := by ring1
  · have targetBNonzero : target.b ≠ 0 := by
      intro targetBZero
      have targetAZero : target.a = 0 := by
        have productZero : target.a * source.b = 0 := by
          calc
            target.a * source.b = source.a * target.b :=
              (Group.eq_of_sub_eq_zero parallel).symm
            _ = 0 := by rw [targetBZero]; ring1
        by_cases zero : target.a = 0
        · exact zero
        · exact False.elim
            ((ExplicitField.mul_ne_zero zero sourceBNonzero) productZero)
      rcases target.direction_nonzero with targetANonzero | targetBNonzero
      · exact targetANonzero targetAZero
      · exact targetBNonzero targetBZero
    let scale := target.b / source.b
    have scaleNonzero : scale ≠ 0 := by
      unfold scale
      rw [ExplicitField.div_eq_mul_inv]
      exact ExplicitField.mul_ne_zero targetBNonzero
        (ExplicitField.inv_ne_zero sourceBNonzero)
    refine ⟨scale, scaleNonzero, ?_, ?_⟩
    · apply (fun {K : Type _} [ExplicitField K] {factor left right : K} (factorNonzero : factor ≠
      0) (productsEqual : factor * left = factor * right) => (ExplicitField.eq_of_mul_eq_mul_left
      (K := K) (left := left) (right := right) (factor := factor) factorNonzero productsEqual : left = right))
        sourceBNonzero
      calc
        source.b * target.a = target.b * source.a := by
          calc
            source.b * target.a = target.a * source.b := by ring1
            _ = source.a * target.b := (Group.eq_of_sub_eq_zero parallel).symm
            _ = target.b * source.a := by ring1
        _ = source.b * (scale * source.a) := by
          unfold scale
          rw [ExplicitField.div_eq_mul_inv]
          have cancel := ExplicitField.mul_inv_cancel source.b
            sourceBNonzero
          calc
            target.b * source.a =
                source.b * source.b⁻¹ * (target.b * source.a) := by
              rw [cancel, one_mul]
            _ = source.b * (target.b * source.b⁻¹ * source.a) := by ring1
    · exact (ExplicitField.div_mul_cancel target.b sourceBNonzero).symm

/-- Equivalent displayed line representatives contain exactly the same points. -/
theorem line_contains_of_equivalent {first second : Plane.Line K}
    (equivalent : first.Equivalent second) (point : Plane.Point K)
    (contains : first.Contains point) : second.Contains point := by
  unfold Plane.Line.Equivalent at equivalent
  unfold Plane.Line.Contains at contains ⊢
  rcases first.direction_nonzero with firstANonzero | firstBNonzero
  · apply ExplicitField.eq_zero_of_mul_eq_zero_left firstANonzero
    calc
      first.a *
          (second.a * point.x + second.b * point.y + second.c) =
        first.a * second.a * point.x +
          (first.a * second.b) * point.y + first.a * second.c := by ring1
      _ = second.a * first.a * point.x +
          (second.a * first.b) * point.y + second.a * first.c := by
            rw [equivalent.1, equivalent.2.1]
            ring1
      _ =
        second.a *
          (first.a * point.x + first.b * point.y + first.c) := by ring1
      _ = 0 := by rw [contains]; ring1
  · apply ExplicitField.eq_zero_of_mul_eq_zero_left firstBNonzero
    have directionSwap : first.b * second.a = second.b * first.a := by
      calc
        first.b * second.a = second.a * first.b := by ring1
        _ = first.a * second.b := equivalent.1.symm
        _ = second.b * first.a := by ring1
    calc
      first.b *
          (second.a * point.x + second.b * point.y + second.c) =
        (first.b * second.a) * point.x +
          first.b * second.b * point.y + first.b * second.c := by ring1
      _ = (second.b * first.a) * point.x +
          second.b * first.b * point.y + second.b * first.c := by
            rw [directionSwap, equivalent.2.2]
            ring1
      _ =
        second.b *
          (first.a * point.x + first.b * point.y + first.c) := by ring1
      _ = 0 := by rw [contains]; ring1

/-- Two parallel displayed lines through one point represent the same ordered proportion. This is the quotient-free
uniqueness principle used by later vertex and conic constructions. -/
theorem line_equivalent_of_parallel_and_common_point
    (first second : Plane.Line K) (point : Plane.Point K)
    (parallel : first.Parallel second)
    (firstContains : first.Contains point)
    (secondContains : second.Contains point) :
    first.Equivalent second := by
  unfold Plane.Line.Parallel at parallel
  have directionCross : first.a * second.b = second.a * first.b := by
    calc
      first.a * second.b =
          (first.a * second.b - second.a * first.b) +
            second.a * first.b := by ring1
      _ = second.a * first.b := by rw [parallel]; ring1
  unfold Plane.Line.Contains at firstContains secondContains
  have firstConstant :
      first.c = -(first.a * point.x + first.b * point.y) := by
    calc
      first.c =
          (first.a * point.x + first.b * point.y + first.c) -
            (first.a * point.x + first.b * point.y) := by ring1
      _ = -(first.a * point.x + first.b * point.y) := by
        rw [firstContains]
        ring1
  have secondConstant :
      second.c = -(second.a * point.x + second.b * point.y) := by
    calc
      second.c =
          (second.a * point.x + second.b * point.y + second.c) -
            (second.a * point.x + second.b * point.y) := by ring1
      _ = -(second.a * point.x + second.b * point.y) := by
        rw [secondContains]
        ring1
  unfold Plane.Line.Equivalent
  refine ⟨directionCross, ?_, ?_⟩
  · rw [firstConstant, secondConstant]
    calc
      first.a * -(second.a * point.x + second.b * point.y) =
          -(first.a * second.a * point.x) -
            (first.a * second.b) * point.y := by ring1
      _ = -(second.a * first.a * point.x) -
            (second.a * first.b) * point.y := by
        rw [directionCross]
        ring1
      _ = second.a * -(first.a * point.x + first.b * point.y) := by
        ring1
  · rw [firstConstant, secondConstant]
    calc
      first.b * -(second.a * point.x + second.b * point.y) =
          -(second.a * first.b * point.x) -
            (first.b * second.b) * point.y := by ring1
      _ = -(first.a * second.b * point.x) -
            (second.b * first.b) * point.y := by
        rw [← directionCross]
        ring1
      _ = second.b * -(first.a * point.x + first.b * point.y) := by
        ring1

end Incidence

end Purelib.Geometry.Plane.Line.Relations

end

end

section
public section

/-!
# Divine Proportions, Exercise 15.6: ribbons

A ribbon is kept as finite coefficient data for the cleared equation
`(ax+by+c)² = K(a²+b²)`.  The presentation retains its arbitrary nonzero
conic scale, while equality of displayed lines remains the quotient-free
relation `Line.Equivalent`.
-/

namespace Purelib.Geometry.Plane.Line.Relations

variable {K : Type*} [ExplicitField K]

/-- Displayed lines containing exactly the same points have equivalent coefficient triples.

Two explicit incident points recover the direction relation and a common point fixes the constant coefficient. -/
public theorem line_equivalent_of_same_contains
    (first second : Line K)
    (sameContains : ∀ point : Point K,
      first.Contains point ↔ second.Contains point) :
    first.Equivalent second := by
  rcases first.direction_nonzero with firstANonzero | firstBNonzero
  · let base : Point K := ⟨-first.c / first.a, 0⟩
    let shifted : Point K := ⟨base.x + first.b, base.y - first.a⟩
    have quotientCancel : (-first.c / first.a) * first.a = -first.c :=
      ExplicitField.div_mul_cancel (-first.c) firstANonzero
    have firstBase : first.Contains base := by
      unfold base Contains
      calc
        first.a * (-first.c / first.a) + first.b * 0 + first.c =
            (-first.c / first.a) * first.a + first.c := by ring1
        _ = 0 := by rw [quotientCancel]; ring1
    have firstShifted : first.Contains shifted := by
      have baseEquation := firstBase
      unfold Contains at baseEquation
      unfold shifted Contains
      calc
        first.a * (base.x + first.b) +
              first.b * (base.y - first.a) + first.c =
            (first.a * base.x + first.b * base.y + first.c) +
              (first.a * first.b - first.b * first.a) := by ring1
        _ = 0 := by rw [baseEquation]; ring1
    have secondBase := (sameContains base).1 firstBase
    have secondShifted := (sameContains shifted).1 firstShifted
    have directionDifference :
        second.a * first.b - second.b * first.a = 0 := by
      have baseEquation := secondBase
      have shiftedEquation := secondShifted
      unfold Contains at baseEquation shiftedEquation
      unfold shifted at shiftedEquation
      calc
        second.a * first.b - second.b * first.a =
            (second.a * (base.x + first.b) +
                second.b * (base.y - first.a) + second.c) -
              (second.a * base.x + second.b * base.y + second.c) := by ring1
        _ = 0 := by rw [shiftedEquation, baseEquation]; ring1
    have parallel : first.Parallel second := by
      unfold Parallel
      calc
        first.a * second.b - second.a * first.b =
            -(second.a * first.b - second.b * first.a) := by ring1
        _ = 0 := by rw [directionDifference]; ring1
    exact line_equivalent_of_parallel_and_common_point first second base
      parallel firstBase secondBase
  · let base : Point K := ⟨0, -first.c / first.b⟩
    let shifted : Point K := ⟨base.x + first.b, base.y - first.a⟩
    have quotientCancel : (-first.c / first.b) * first.b = -first.c :=
      ExplicitField.div_mul_cancel (-first.c) firstBNonzero
    have firstBase : first.Contains base := by
      unfold base Contains
      calc
        first.a * 0 + first.b * (-first.c / first.b) + first.c =
            (-first.c / first.b) * first.b + first.c := by ring1
        _ = 0 := by rw [quotientCancel]; ring1
    have firstShifted : first.Contains shifted := by
      have baseEquation := firstBase
      unfold Contains at baseEquation
      unfold shifted Contains
      calc
        first.a * (base.x + first.b) +
              first.b * (base.y - first.a) + first.c =
            (first.a * base.x + first.b * base.y + first.c) +
              (first.a * first.b - first.b * first.a) := by ring1
        _ = 0 := by rw [baseEquation]; ring1
    have secondBase := (sameContains base).1 firstBase
    have secondShifted := (sameContains shifted).1 firstShifted
    have directionDifference :
        second.a * first.b - second.b * first.a = 0 := by
      have baseEquation := secondBase
      have shiftedEquation := secondShifted
      unfold Contains at baseEquation shiftedEquation
      unfold shifted at shiftedEquation
      calc
        second.a * first.b - second.b * first.a =
            (second.a * (base.x + first.b) +
                second.b * (base.y - first.a) + second.c) -
              (second.a * base.x + second.b * base.y + second.c) := by ring1
        _ = 0 := by rw [shiftedEquation, baseEquation]; ring1
    have parallel : first.Parallel second := by
      unfold Parallel
      calc
        first.a * second.b - second.a * first.b =
            -(second.a * first.b - second.b * first.a) := by ring1
        _ = 0 := by rw [directionDifference]; ring1
    exact line_equivalent_of_parallel_and_common_point first second base
      parallel firstBase secondBase

end Purelib.Geometry.Plane.Line.Relations

end

section
public section

/-!
# Divine Proportions, Exercises 3.3–3.10

These line relations and coordinate formulas use only the three displayed
coefficients of each line.  Parallel directions are related by an explicit
nonzero scale; no slope quotient or projective representative is selected.
-/

namespace Purelib.Geometry.Plane.Line.Relations

variable {K : Type*} [ExplicitField K]

/-- Exercise 3.4: a line parallel to `first` is parallel to every parallel representative of `first`, and a line
perpendicular to `first` is perpendicular to every such representative. -/
theorem exercise_3_4 [DecidableEq K]
    (first second third : Plane.Line K) (firstSecond : first.Parallel second) :
    (third.Parallel first → third.Parallel second) ∧
      (third.Perpendicular first → third.Perpendicular second) := by
  constructor
  · intro thirdFirst
    exact line_parallel_trans thirdFirst firstSecond
  · intro thirdFirst
    rcases direction_scale_of_parallel first second firstSecond with
      ⟨scale, _scaleNonzero, secondA, secondB⟩
    unfold Plane.Line.Perpendicular at thirdFirst ⊢
    rw [secondA, secondB]
    calc
      third.a * (scale * first.a) + third.b * (scale * first.b) =
          scale * (third.a * first.a + third.b * first.b) := by ring1
      _ = 0 := by rw [thirdFirst]; ring1

/-- Exercise 3.5: two lines perpendicular to the same displayed line are parallel. -/
theorem exercise_3_5
    (first second third : Plane.Line K)
    (firstSecond : first.Perpendicular second)
    (secondThird : second.Perpendicular third) :
    first.Parallel third := by
  let origin : Plane.Point K := ⟨0, 0⟩
  let commonAltitude := Construction.altitudeThrough origin second
  have firstAltitude : first.Parallel commonAltitude := by
    unfold Plane.Line.Parallel commonAltitude Construction.altitudeThrough
    unfold Plane.Line.Perpendicular at firstSecond
    calc
      first.a * second.a - -second.b * first.b =
          first.a * second.a + first.b * second.b := by ring1
      _ = 0 := firstSecond
  have altitudeThird : commonAltitude.Parallel third := by
    unfold Plane.Line.Parallel commonAltitude Construction.altitudeThrough
    unfold Plane.Line.Perpendicular at secondThird
    calc
      -second.b * third.b - third.a * second.a =
          -(second.a * third.a + second.b * third.b) := by ring1
      _ = 0 := by rw [secondThird]; ring1
  exact line_parallel_trans firstAltitude altitudeThird

/-- Exercise 3.7: lines that are simultaneously parallel and perpendicular are both null. -/
theorem exercise_3_7 [DecidableEq K]
    (first second : Plane.Line K) (parallel : first.Parallel second)
    (perpendicular : first.Perpendicular second) :
    first.IsNull ∧ second.IsNull := by
  rcases direction_scale_of_parallel first second parallel with
    ⟨scale, scaleNonzero, secondA, secondB⟩
  have scaledFirstNorm : scale * (first.a ^ 2 + first.b ^ 2) = 0 := by
    unfold Plane.Line.Perpendicular at perpendicular
    rw [secondA, secondB] at perpendicular
    calc
      scale * (first.a ^ 2 + first.b ^ 2) =
          first.a * (scale * first.a) +
            first.b * (scale * first.b) := by ring1
      _ = 0 := perpendicular
  have firstNull : first.IsNull := by
    unfold Plane.Line.IsNull
    by_cases normZero : first.a ^ 2 + first.b ^ 2 = 0
    · exact normZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero scaleNonzero normZero)
          scaledFirstNorm)
  constructor
  · exact firstNull
  · unfold Plane.Line.IsNull at firstNull ⊢
    rw [secondA, secondB]
    calc
      (scale * first.a) ^ 2 + (scale * first.b) ^ 2 =
          scale ^ 2 * (first.a ^ 2 + first.b ^ 2) := by ring1
      _ = 0 := by rw [firstNull]; ring1
end Purelib.Geometry.Plane.Line.Relations

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

namespace Purelib.Geometry.Plane.Line.Relations

variable {K : Type*} [ExplicitField K]

/-- Reversing the endpoints only reverses both displayed direction coefficients, so the two line representatives are
parallel. -/
public theorem lineThrough_reverse_parallel
  [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (Incidence.lineThrough first second distinct).Parallel
      (Incidence.lineThrough second first distinct.symm) := by
  unfold Parallel Incidence.lineThrough
  ring1

end Purelib.Geometry.Plane.Line.Relations

end

section
public section

/-!
# Divine Proportions, Chapter 10: the isosceles median

The line in Theorem 67 is represented by its vertex and its displayed
intersection with the opposite side.  This keeps all three conditions—altitude,
median, and equal-spread vertex bisector—finite and executable.
-/

namespace Purelib.Geometry.Plane.Line.Relations

variable {K : Type*} [ExplicitField K]

/-- Replacing the first member of a perpendicular pair by a parallel line preserves perpendicularity. -/
theorem perpendicular_of_parallel_left [DecidableEq K]
    (source target other : Plane.Line K) (parallel : source.Parallel target)
    (sourcePerpendicular : source.Perpendicular other) :
    target.Perpendicular other := by
  rcases direction_scale_of_parallel source target parallel with
    ⟨scale, _scaleNonzero, targetA, targetB⟩
  unfold Plane.Line.Perpendicular at sourcePerpendicular ⊢
  rw [targetA, targetB]
  calc
    scale * source.a * other.a + scale * source.b * other.b =
        scale * (source.a * other.a + source.b * other.b) := by ring1
    _ = 0 := by rw [sourcePerpendicular]; ring1
end Purelib.Geometry.Plane.Line.Relations

end

section
public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Geometry.Plane.Line.Relations

section

variable {K : Type*} [ExplicitField K]

/-- Replacing the first member of a perpendicular pair by a parallel line preserves perpendicularity. -/
public theorem perpendicular_of_parallel_left_direct [DecidableEq K]
    (source target other : Line K) (parallel : source.Parallel target)
    (sourcePerpendicular : source.Perpendicular other) :
    target.Perpendicular other := by
  rcases direction_scale_of_parallel source target parallel with
    ⟨scale, _scaleNonzero, targetA, targetB⟩
  unfold Perpendicular at sourcePerpendicular ⊢
  rw [targetA, targetB]
  calc
    scale * source.a * other.a + scale * source.b * other.b =
        scale * (source.a * other.a + source.b * other.b) := by ring1
    _ = 0 := by rw [sourcePerpendicular]; ring1

end
end Purelib.Geometry.Plane.Line.Relations

end

end
