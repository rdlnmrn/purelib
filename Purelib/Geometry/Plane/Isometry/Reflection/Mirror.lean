module

import Purelib.Algebra.Field.Squares
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Isometry.Reflection
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Point
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

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Isometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, Exercise 13.3: central reflection mirrors

Reflection in a non-null central line has the book's central-reflection
coordinates.  Conversely, a unit parameter pair constructively determines a
central non-null mirror, unique up to the project's quotient-free
`Line.Equivalent` relation.
-/

namespace Purelib.Geometry.Plane.Isometry.Reflection.Mirror

variable {K : Type*} [ExplicitField K]

/-- The first central-reflection parameter associated to a central line. -/
def centralLineReflectionQ (line : Plane.Line K) : K :=
  (line.b ^ 2 - line.a ^ 2) / Line.Basic.lineNorm line

/-- The second central-reflection parameter associated to a central line. -/
def centralLineReflectionR (line : Plane.Line K) : K :=
  (-2 * line.a * line.b) / Line.Basic.lineNorm line

/-- The two parameters extracted from a non-null central line form a unit pair. -/
theorem centralLineReflection_unit (line : Plane.Line K)
    (nonNull : ¬ line.IsNull) :
    centralLineReflectionQ line ^ 2 + centralLineReflectionR line ^ 2 = 1 := by
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ nonNull
  unfold centralLineReflectionQ centralLineReflectionR
  simp only [ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
  calc
    ((line.b ^ 2 - line.a ^ 2) * (Basic.lineNorm line)⁻¹) ^ 2 +
        ((-2 * line.a * line.b) * (Basic.lineNorm line)⁻¹) ^ 2 =
      (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 := by
        unfold Basic.lineNorm
        ring1
    _ = 1 := by rw [normCancel]; ring1

/-- The forward half of Exercise 13.3: reflection in a non-null central line is the central reflection with its
displayed unit parameters. -/
theorem centralLine_reflection_is_central (line :
  Plane.Line K)
    (nonNull : ¬ line.IsNull) (central : line.Contains Point.Basic.planeOrigin)
    (point : Plane.Point K) :
    Reflection.Point.reflectPoint line nonNull point =
      Reflection.centralReflectionPoint
        (centralLineReflectionQ line)
          (centralLineReflectionR line) point := by
  have cZero : line.c = 0 := by
    unfold Plane.Line.Contains Point.Basic.planeOrigin at central
    simpa using central
  rw [Reflection.Point.reflectPoint_formula]
  apply Plane.Point.ext <;>
    unfold Reflection.Point.reflectionFormula Reflection.centralReflectionPoint centralLineReflectionQ
      centralLineReflectionR <;>
    rw [cZero] <;>
    simp only [ExplicitField.div_eq_mul_inv, -eq_self, -iff_self] <;>
    ring1

/-- A concrete central mirror for parameters `[q,r]`. The generic branch is `⟨q-1:r:0⟩`; the exceptional identity-on-x
parameter `q=1` uses `⟨0:1:0⟩`. -/
def centralReflectionMirror [Nontrivial K] [DecidableEq K]
    (q r : K) : Plane.Line K :=
  if qOne : q = 1 then
    { a := 0
      b := 1
      c := 0
      direction_nonzero := Or.inr one_ne_zero }
  else
    { a := q - 1
      b := r
      c := 0
      direction_nonzero := Or.inl (by
        intro differenceZero
        apply qOne
        calc
          q = (q - 1) + 1 := by ring1
          _ = 1 := by rw [differenceZero]; ring1) }

/-- The concrete mirror is non-null for a unit pair outside characteristic two. -/
theorem centralReflectionMirror_nonNull [Nontrivial K]
  [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ (centralReflectionMirror q r).IsNull := by
  by_cases qOne : q = 1
  · unfold centralReflectionMirror
    rewrite [dif_pos qOne]
    simp only [Plane.Line.IsNull, -eq_self, -iff_self]
    intro nullNorm
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  · unfold centralReflectionMirror
    rewrite [dif_neg qOne]
    change ¬ ((q - 1) ^ 2 + r ^ 2 = 0)
    have oneMinusQNonzero : (1 : K) - q ≠ 0 := by
      intro differenceZero
      apply qOne
      calc
        q = 1 - (1 - q) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have normFormula : (q - 1) ^ 2 + r ^ 2 = 2 * (1 - q) := by
      calc
        (q - 1) ^ 2 + r ^ 2 =
            (q ^ 2 + r ^ 2) + 2 * (1 - q) - 1 := by ring1
        _ = 2 * (1 - q) := by rw [unit]; ring1
    rw [normFormula]
    exact ExplicitField.mul_ne_zero twoNonzero oneMinusQNonzero

/-- The concrete mirror realizes the given central reflection. -/
theorem centralReflectionMirror_reflects [Nontrivial K]
  [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) (point : Plane.Point K) :
    Reflection.Point.reflectPoint (centralReflectionMirror q r)
        (centralReflectionMirror_nonNull q r unit twoNonzero) point =
      Reflection.centralReflectionPoint q r point := by
  by_cases qOne : q = 1
  · have rSquareZero : r ^ 2 = 0 := by
      calc
        r ^ 2 = q ^ 2 + r ^ 2 - 1 := by rw [qOne]; ring1
        _ = 0 := by rw [unit]; ring1
    have rZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) (squareZero :
      value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0))
      r rSquareZero
    have oneInverse : (1 : K)⁻¹ = 1 := by
      calc
        (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
        _ = 1 := ExplicitField.mul_inv_cancel 1 one_ne_zero
    rw [Reflection.Point.reflectPoint_formula]
    apply Plane.Point.ext <;>
      simp only [centralReflectionMirror, dif_pos qOne,
        Reflection.Point.reflectionFormula,
        Line.Basic.lineNorm, Reflection.centralReflectionPoint,
        ExplicitField.div_eq_mul_inv, -eq_self, -iff_self] <;>
      rw [rZero] <;>
      rw [show (0 : K) ^ 2 + 1 ^ 2 = 1 by ring1] <;>
      rw [oneInverse, qOne] <;>
      ring1
  · let norm : K := (q - 1) ^ 2 + r ^ 2
    have normFormula : norm = 2 * (1 - q) := by
      unfold norm
      calc
        (q - 1) ^ 2 + r ^ 2 =
            (q ^ 2 + r ^ 2) + 2 * (1 - q) - 1 := by ring1
        _ = 2 * (1 - q) := by rw [unit]; ring1
    have oneMinusQNonzero : (1 : K) - q ≠ 0 := by
      intro differenceZero
      apply qOne
      calc
        q = 1 - (1 - q) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have normNonzero : norm ≠ 0 := by
      rw [normFormula]
      exact ExplicitField.mul_ne_zero twoNonzero oneMinusQNonzero
    have normCancel : norm * norm⁻¹ = 1 :=
      ExplicitField.mul_inv_cancel norm normNonzero
    have qNumerator : r ^ 2 - (q - 1) ^ 2 = q * norm := by
      unfold norm
      calc
        r ^ 2 - (q - 1) ^ 2 =
            q * ((q - 1) ^ 2 + r ^ 2) +
              (1 - q) * (q ^ 2 + r ^ 2 - 1) := by ring1
        _ = q * ((q - 1) ^ 2 + r ^ 2) := by rw [unit]; ring1
    have rNumerator : -2 * (q - 1) * r = r * norm := by
      unfold norm
      calc
        -2 * (q - 1) * r =
            r * ((q - 1) ^ 2 + r ^ 2) -
              r * (q ^ 2 + r ^ 2 - 1) := by ring1
        _ = r * ((q - 1) ^ 2 + r ^ 2) := by rw [unit]; ring1
    have positiveRNumerator : 2 * (q - 1) * r = -(r * norm) := by
      calc
        2 * (q - 1) * r = -(-2 * (q - 1) * r) := by ring1
        _ = -(r * norm) := by rw [rNumerator]
    have negQNumerator : (q - 1) ^ 2 - r ^ 2 = -q * norm := by
      calc
        (q - 1) ^ 2 - r ^ 2 = -(r ^ 2 - (q - 1) ^ 2) := by ring1
        _ = -q * norm := by rw [qNumerator]; ring1
    rw [Reflection.Point.reflectPoint_formula]
    have zeroDifference (amount : K) : amount - 0 = amount := by ring1
    apply Plane.Point.ext
    · simp only [centralReflectionMirror, dif_neg qOne,
        Reflection.Point.reflectionFormula, Line.Basic.lineNorm, Reflection.centralReflectionPoint,
        ExplicitField.div_eq_mul_inv, mul_zero, zeroDifference, -eq_self, -iff_self]
      change
        ((r ^ 2 - (q - 1) ^ 2) * point.x -
            2 * (q - 1) * r * point.y) * norm⁻¹ =
          q * point.x + r * point.y
      rw [qNumerator, positiveRNumerator]
      calc
        (q * norm * point.x - -(r * norm) * point.y) * norm⁻¹ =
            (q * point.x + r * point.y) * (norm * norm⁻¹) := by ring1
        _ = q * point.x + r * point.y := by rw [normCancel]; ring1
    · simp only [centralReflectionMirror, dif_neg qOne,
        Reflection.Point.reflectionFormula, Line.Basic.lineNorm, Reflection.centralReflectionPoint,
        ExplicitField.div_eq_mul_inv, mul_zero, zeroDifference, -eq_self, -iff_self]
      change
        (-2 * (q - 1) * r * point.x +
            ((q - 1) ^ 2 - r ^ 2) * point.y) * norm⁻¹ =
          r * point.x - q * point.y
      rw [rNumerator, negQNumerator]
      calc
        (r * norm * point.x + (-q * norm) * point.y) * norm⁻¹ =
            (r * point.x - q * point.y) * (norm * norm⁻¹) := by ring1
        _ = r * point.x - q * point.y := by rw [normCancel]; ring1

/-- A direction point on a central line. -/
def centralLineDirectionPoint (line : Plane.Line K) :
  Plane.Point K :=
  ⟨line.b, -line.a⟩

/-- Two non-null central lines inducing the same point reflection are the same ordered proportion. -/
theorem centralLine_reflection_unique [Nontrivial K]
    (first second : Plane.Line K) (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (firstCentral : first.Contains Point.Basic.planeOrigin)
    (secondCentral : second.Contains Point.Basic.planeOrigin)
    (sameReflection : ∀ point : Plane.Point K,
      Reflection.Point.reflectPoint first firstNonNull point =
        Reflection.Point.reflectPoint second secondNonNull point) :
    first.Equivalent second := by
  have firstDirectionContains :
      first.Contains (centralLineDirectionPoint first) := by
    have firstCZero : first.c = 0 := by
      unfold Plane.Line.Contains Point.Basic.planeOrigin at firstCentral
      simpa using firstCentral
    unfold Plane.Line.Contains centralLineDirectionPoint
    rw [firstCZero]
    ring1
  have firstDirectionFixed :
      Reflection.Point.reflectPoint first firstNonNull (centralLineDirectionPoint first) =
        centralLineDirectionPoint first :=
    (Reflection.Point.reflectPoint_fixed_iff_contains first firstNonNull twoNonzero
      (centralLineDirectionPoint first)).2 firstDirectionContains
  have secondDirectionFixed :
      Reflection.Point.reflectPoint second secondNonNull (centralLineDirectionPoint first) =
        centralLineDirectionPoint first := by
    rw [← sameReflection]
    exact firstDirectionFixed
  have secondDirectionContains :
      second.Contains (centralLineDirectionPoint first) :=
    (Reflection.Point.reflectPoint_fixed_iff_contains second secondNonNull twoNonzero
      (centralLineDirectionPoint first)).1 secondDirectionFixed
  have parallel : first.Parallel second := by
    have secondCZero : second.c = 0 := by
      unfold Plane.Line.Contains Point.Basic.planeOrigin at secondCentral
      simpa using secondCentral
    unfold Plane.Line.Contains centralLineDirectionPoint at secondDirectionContains
    unfold Line.Parallel
    rw [secondCZero] at secondDirectionContains
    calc
      first.a * second.b - second.a * first.b =
          -(second.a * first.b + second.b * (-first.a) + 0) := by ring1
      _ = 0 := by rw [secondDirectionContains]; ring1
  exact Relations.line_equivalent_of_parallel_and_common_point
    first second Point.Basic.planeOrigin parallel firstCentral secondCentral

/-- Exercise 13.3, converse and uniqueness: every unit central reflection has a displayed non-null central mirror, and
any other such mirror is equivalent to it. -/
theorem centralReflection_has_unique_mirror [Nontrivial K]
  [DecidableEq K]
    (q r : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ∃ mirror : Plane.Line K, ∃ mirrorNonNull : ¬ mirror.IsNull,
      mirror.Contains Point.Basic.planeOrigin ∧
      (∀ point : Plane.Point K,
        Reflection.Point.reflectPoint mirror mirrorNonNull point =
          Reflection.centralReflectionPoint q r point) ∧
      ∀ other : Plane.Line K, ∀ otherNonNull : ¬ other.IsNull,
        other.Contains Point.Basic.planeOrigin →
        (∀ point : Plane.Point K,
          Reflection.Point.reflectPoint other otherNonNull point =
            Reflection.centralReflectionPoint q r point) →
        other.Equivalent mirror := by
  let mirror := centralReflectionMirror q r
  let mirrorNonNull := centralReflectionMirror_nonNull q r unit twoNonzero
  refine ⟨mirror, mirrorNonNull, ?_, ?_, ?_⟩
  · unfold mirror centralReflectionMirror Plane.Line.Contains Point.Basic.planeOrigin
    split <;> ring1
  · exact centralReflectionMirror_reflects q r unit twoNonzero
  · intro other otherNonNull otherCentral otherReflection
    apply centralLine_reflection_unique other mirror
      otherNonNull mirrorNonNull twoNonzero otherCentral
    · unfold mirror centralReflectionMirror Plane.Line.Contains Point.Basic.planeOrigin
      split <;> ring1
    · intro point
      calc
        Reflection.Point.reflectPoint other otherNonNull point =
            Reflection.centralReflectionPoint q r point := otherReflection point
        _ = Reflection.Point.reflectPoint mirror mirrorNonNull point :=
          (centralReflectionMirror_reflects q r unit twoNonzero point).symm

end Purelib.Geometry.Plane.Isometry.Reflection.Mirror

end
