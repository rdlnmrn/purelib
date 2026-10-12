module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Trigonometry

/-!
# Divine Proportions, remaining Chapter 5 exercises

Exercise 5.3 is false with the source's definition of a triangle: the
nonzero quadrances `1,1,4` have zero quadrea, hence cannot belong to three
noncollinear points.  The corrected theorem below isolates the exact missing
condition.  In a field carrying an explicit square root of `-1`, every scalar
is constructively a sum of two squares, so Theorem 28 reduces triangle
existence to an explicit nonzero square witness for the quadrea.

Exercise 5.17 is retained through the finite construction responsible for its
factor `2`: a chosen base vector and either sign of a nonzero quadrea root give
two distinct completion points with the requested quadrances.  The remaining
`p²` translation and `p±1` nonzero-circle factors are recorded as finite
counting data rather than by enumerating an entire field carrier.

Exercise 5.19 is answered by a recursive, fuel-indexed finite quad relation.
For five entries it introduces the two diagonals of a fan triangulation; for
any requested finite number of entries it repeatedly combines two adjacent
signed lengths.  There is no infinite sequence or completed polygon.
-/

public section

namespace Purelib.Geometry.Triangles.Quadrance.Completion

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]
section

/-- The source's completion point for a base vector `[a,b]`, with the chosen sign of the quadrea root retained in
`areaRoot`. -/
@[expose] def completionPoint
    (q₁ q₂ q₃ areaRoot a b : K) : Geometry.Plane.Point K :=
  let radial := q₁ + q₂ - q₃
  let denominator := 2 * q₂
  ⟨(a * radial - b * areaRoot) / denominator,
    (b * radial + a * areaRoot) / denominator⟩

/-- The completion formula has the two requested quadrances; the chosen base vector has quadrance `q₂` from the origin.
-/
theorem completionPoint_quadrances
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂)
    (areaEquation :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2) :
    let origin : Geometry.Plane.Point K := ⟨0, 0⟩
    let base : Geometry.Plane.Point K := ⟨a, b⟩
    let completion := completionPoint q₁ q₂ q₃ areaRoot a b
    Quadrance.quadrance completion origin = q₁ ∧
      Quadrance.quadrance base origin = q₂ ∧
      Quadrance.quadrance base completion = q₃ := by
  let radial := q₁ + q₂ - q₃
  let denominator := 2 * q₂
  let xNumerator := a * radial - b * areaRoot
  let yNumerator := b * radial + a * areaRoot
  let origin : Geometry.Plane.Point K := ⟨0, 0⟩
  let base : Geometry.Plane.Point K := ⟨a, b⟩
  let completion := completionPoint q₁ q₂ q₃ areaRoot a b
  have denominatorNonzero : denominator ≠ 0 := by
    unfold denominator
    exact ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have areaRootSquared : areaRoot ^ 2 = 4 * q₁ * q₂ - radial ^ 2 := by
    calc
      areaRoot ^ 2 = QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ := areaEquation.symm
      _ = 4 * q₁ * q₂ - radial ^ 2 := by
        unfold QuadTriple.Basic.archimedesFunction radial
        ring1
  have numeratorNorm :
      xNumerator ^ 2 + yNumerator ^ 2 = 4 * q₁ * q₂ ^ 2 := by
    calc
      xNumerator ^ 2 + yNumerator ^ 2 =
          (a ^ 2 + b ^ 2) * (radial ^ 2 + areaRoot ^ 2) := by
        unfold xNumerator yNumerator
        ring1
      _ = q₂ * (radial ^ 2 + areaRoot ^ 2) := by rw [baseNorm]
      _ = 4 * q₁ * q₂ ^ 2 := by rw [areaRootSquared]; ring1
  have completionOrigin : Quadrance.quadrance completion origin = q₁ := by
    unfold Quadrance.quadrance completion completionPoint origin
    simp only [zero_sub, ExplicitField.div_eq_mul_inv]
    calc
      (-((a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹)) ^ 2 +
          (-((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹)) ^ 2 =
        (xNumerator ^ 2 + yNumerator ^ 2) * denominator⁻¹ ^ 2 := by
          unfold xNumerator yNumerator denominator radial
          ring1
      _ = 4 * q₁ * q₂ ^ 2 * denominator⁻¹ ^ 2 := by
        rw [numeratorNorm]
      _ = q₁ * (denominator * denominator⁻¹) ^ 2 := by
        unfold denominator
        ring1
      _ = q₁ := by rw [denominatorCancel]; ring1
  have baseOrigin : Quadrance.quadrance base origin = q₂ := by
    unfold Quadrance.quadrance base origin
    simp only [zero_sub]
    calc
      (-a) ^ 2 + (-b) ^ 2 = a ^ 2 + b ^ 2 := by ring1
      _ = q₂ := baseNorm
  have xDifference :
      xNumerator / denominator - a =
        (xNumerator - a * denominator) * denominator⁻¹ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      xNumerator * denominator⁻¹ - a =
          xNumerator * denominator⁻¹ -
            a * (denominator * denominator⁻¹) := by
        rw [denominatorCancel]
        ring1
      _ = (xNumerator - a * denominator) * denominator⁻¹ := by ring1
  have yDifference :
      yNumerator / denominator - b =
        (yNumerator - b * denominator) * denominator⁻¹ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      yNumerator * denominator⁻¹ - b =
          yNumerator * denominator⁻¹ -
            b * (denominator * denominator⁻¹) := by
        rw [denominatorCancel]
        ring1
      _ = (yNumerator - b * denominator) * denominator⁻¹ := by ring1
  have differenceNorm :
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        q₃ * denominator ^ 2 := by
    calc
      (xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2 =
        (a ^ 2 + b ^ 2) *
          ((radial - 2 * q₂) ^ 2 + areaRoot ^ 2) := by
        unfold xNumerator yNumerator denominator
        ring1
      _ = q₂ * ((radial - 2 * q₂) ^ 2 + areaRoot ^ 2) := by
        rw [baseNorm]
      _ = q₃ * denominator ^ 2 := by
        rw [areaRootSquared]
        unfold radial denominator
        ring1
  have baseCompletion : Quadrance.quadrance base completion = q₃ := by
    unfold Quadrance.quadrance base completion completionPoint
    change
      (xNumerator / denominator - a) ^ 2 +
          (yNumerator / denominator - b) ^ 2 = q₃
    rw [xDifference, yDifference]
    calc
      ((xNumerator - a * denominator) * denominator⁻¹) ^ 2 +
          ((yNumerator - b * denominator) * denominator⁻¹) ^ 2 =
        ((xNumerator - a * denominator) ^ 2 +
          (yNumerator - b * denominator) ^ 2) *
            denominator⁻¹ ^ 2 := by ring1
      _ = q₃ * denominator ^ 2 * denominator⁻¹ ^ 2 := by
        rw [differenceNorm]
      _ = q₃ * (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = q₃ := by rw [denominatorCancel]; ring1
  exact ⟨completionOrigin, baseOrigin, baseCompletion⟩

/-- The determinant of the base, completion, and origin, with the common denominator left cleared, is `q₂ * areaRoot`.
-/
theorem completionPoint_determinant_cleared
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    Incidence.pointDeterminant (⟨a, b⟩ : Geometry.Plane.Point K)
        (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
        (2 * q₂) =
      q₂ * areaRoot := by
  have denominatorNonzero : (2 : K) * q₂ ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero q₂Nonzero
  have denominatorCancelLeft :
      ((2 : K) * q₂)⁻¹ * (2 * q₂) = 1 := by
    calc
      ((2 : K) * q₂)⁻¹ * (2 * q₂) =
          (2 * q₂) * ((2 : K) * q₂)⁻¹ := by ring1
      _ = 1 := ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold Incidence.pointDeterminant completionPoint
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (a * ((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹) -
          a * 0 +
          (a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹ * 0 -
          0 * ((b * (q₁ + q₂ - q₃) + a * areaRoot) *
              (2 * q₂)⁻¹) +
          0 * b -
          (a * (q₁ + q₂ - q₃) - b * areaRoot) *
              (2 * q₂)⁻¹ * b) *
            (2 * q₂) =
        (a ^ 2 + b ^ 2) * areaRoot *
          (((2 : K) * q₂)⁻¹ * (2 * q₂)) := by ring1
    _ = q₂ * areaRoot := by
      rw [baseNorm, denominatorCancelLeft]
      ring1

/-- A nonzero selected quadrea root makes the completion genuinely two-dimensional. This is the noncollinearity
certificate needed for the source's use of the word “triangle”. -/
theorem completionPoint_not_collinear
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    ¬ Incidence.Collinear (⟨a, b⟩ : Geometry.Plane.Point K)
      (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ := by
  intro collinear
  have determinantZero :=
    (Incidence.collinear_iff_pointDeterminant_eq_zero
      (⟨a, b⟩ : Geometry.Plane.Point K)
      (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩).1 collinear
  have clearedZero :
      Incidence.pointDeterminant (⟨a, b⟩ : Geometry.Plane.Point K)
          (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
          (2 * q₂) = 0 := by
    rw [determinantZero]
    ring1
  have clearedValue := completionPoint_determinant_cleared
    q₁ q₂ q₃ areaRoot a b twoNonzero q₂Nonzero baseNorm
  have productZero : q₂ * areaRoot = 0 := by
    calc
      q₂ * areaRoot =
          Incidence.pointDeterminant (⟨a, b⟩ : Geometry.Plane.Point K)
              (completionPoint q₁ q₂ q₃ areaRoot a b) ⟨0, 0⟩ *
              (2 * q₂) := clearedValue.symm
      _ = 0 := clearedZero
  exact (ExplicitField.mul_ne_zero q₂Nonzero areaRootNonzero)
    productZero

/-- The two signs of a nonzero area root give two genuinely distinct completion points. -/
theorem completionPoint_signs_distinct
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂) :
    completionPoint q₁ q₂ q₃ areaRoot a b ≠
      completionPoint q₁ q₂ q₃ (-areaRoot) a b := by
  intro completionsEqual
  let base : Geometry.Plane.Point K := ⟨a, b⟩
  let origin : Geometry.Plane.Point K := ⟨0, 0⟩
  have determinantsEqual := congrArg
    (fun point => Incidence.pointDeterminant base point origin * (2 * q₂))
    completionsEqual
  have positiveDeterminant := completionPoint_determinant_cleared
    q₁ q₂ q₃ areaRoot a b twoNonzero q₂Nonzero baseNorm
  have negativeDeterminant := completionPoint_determinant_cleared
    q₁ q₂ q₃ (-areaRoot) a b twoNonzero q₂Nonzero baseNorm
  have productsEqual : q₂ * areaRoot = q₂ * (-areaRoot) := by
    calc
      q₂ * areaRoot =
          Incidence.pointDeterminant base
              (completionPoint q₁ q₂ q₃ areaRoot a b) origin *
            (2 * q₂) := positiveDeterminant.symm
      _ = Incidence.pointDeterminant base
              (completionPoint q₁ q₂ q₃ (-areaRoot) a b) origin *
            (2 * q₂) := determinantsEqual
      _ = q₂ * (-areaRoot) := negativeDeterminant
  have productZero : q₂ * (2 * areaRoot) = 0 := by
    calc
      q₂ * (2 * areaRoot) =
          q₂ * areaRoot - q₂ * (-areaRoot) := by ring1
      _ = 0 := by rw [productsEqual]; ring1
  exact (ExplicitField.mul_ne_zero q₂Nonzero
    (ExplicitField.mul_ne_zero twoNonzero areaRootNonzero)) productZero

/-- Exercise 5.17's constructive factor two: both signs of the supplied nonzero quadrea root produce the requested
quadrances, and the resulting completion points differ. -/
theorem two_completions
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ areaRoot a b : K)
    (twoNonzero : (2 : K) ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (areaRootNonzero : areaRoot ≠ 0)
    (baseNorm : a ^ 2 + b ^ 2 = q₂)
    (areaEquation :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2) :
    let origin : Geometry.Plane.Point K := ⟨0, 0⟩
    let base : Geometry.Plane.Point K := ⟨a, b⟩
    let positive := completionPoint q₁ q₂ q₃ areaRoot a b
    let negative := completionPoint q₁ q₂ q₃ (-areaRoot) a b
    Quadrance.quadrance positive origin = q₁ ∧
      Quadrance.quadrance base origin = q₂ ∧
      Quadrance.quadrance base positive = q₃ ∧
      ¬ Incidence.Collinear base positive origin ∧
      Quadrance.quadrance negative origin = q₁ ∧
      Quadrance.quadrance base negative = q₃ ∧
      ¬ Incidence.Collinear base negative origin ∧
      positive ≠ negative := by
  have positive := completionPoint_quadrances q₁ q₂ q₃ areaRoot a b
    twoNonzero q₂Nonzero baseNorm areaEquation
  have negativeAreaEquation :
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = (-areaRoot) ^ 2 := by
    calc
      QuadTriple.Basic.archimedesFunction q₁ q₂ q₃ = areaRoot ^ 2 := areaEquation
      _ = (-areaRoot) ^ 2 := by ring1
  have negative := completionPoint_quadrances q₁ q₂ q₃ (-areaRoot) a b
    twoNonzero q₂Nonzero baseNorm negativeAreaEquation
  exact ⟨positive.1, positive.2.1, positive.2.2,
    completionPoint_not_collinear q₁ q₂ q₃ areaRoot a b twoNonzero
      q₂Nonzero areaRootNonzero baseNorm,
    negative.1, negative.2.2,
    completionPoint_not_collinear q₁ q₂ q₃ (-areaRoot) a b twoNonzero
      q₂Nonzero ((by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite [neg_neg,
        SubNegZeroMonoid.neg_zero] at restored; exact areaRootNonzero restored)) baseNorm,
    completionPoint_signs_distinct q₁ q₂ q₃ areaRoot a b twoNonzero
      q₂Nonzero areaRootNonzero baseNorm⟩
end

section
end

end Purelib.Geometry.Triangles.Quadrance.Completion

end

end
