module
public import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Reverse
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Polygons.SignedArea.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Polygons

@[expose] public section

/-!
# Divine Proportions, Chapter 9: finite polygon exercises

Exercises 9.6 and 9.7 are finite identities for the cyclic shoelace sum.
Splitting a polygon introduces two oppositely oriented copies of one diagonal;
reversing it reverses every edge.  The proofs operate directly on the supplied
vertex lists.
-/

namespace Purelib.Geometry.Polygons.SignedArea.Operations

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section
/-- Split a cyclic determinant sum at a displayed pivot, retaining the closing diagonal terms. -/
private theorem
  polygonDoubleSignedAreaAux_split
    (first current pivot : Plane.Point K)
    (middle remaining : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedAreaAux first current
        (middle ++ pivot :: remaining) =
      SignedArea.Basic.polygonDoubleSignedAreaAux first current (middle ++ [pivot]) +
        Determinant.positionDeterminant first pivot +
        SignedArea.Basic.polygonDoubleSignedAreaAux first pivot remaining := by
  induction middle generalizing current with
  | nil =>
      simp only [List.nil_append, SignedArea.Basic.polygonDoubleSignedAreaAux]
      unfold Determinant.positionDeterminant
      ring1
  | cons next middle inductionHypothesis =>
      simp only [List.cons_append, SignedArea.Basic.polygonDoubleSignedAreaAux]
      rw [inductionHypothesis]
      ring1
end

/-- Denominator-free form of Exercise 9.6. The list `middle` contains the vertices strictly between the first vertex and
the displayed split vertex. The source's bounds `3 ≤ m < n` merely ensure both printed polygons have the intended sizes;
the algebraic identity itself needs no length premise. -/
theorem polygon_double_signed_area_split
    (first pivot : Plane.Point K) (middle remaining : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedArea
        (first :: (middle ++ pivot :: remaining)) =
      SignedArea.Basic.polygonDoubleSignedArea (first :: (middle ++ [pivot])) +
        SignedArea.Basic.polygonDoubleSignedArea (first :: pivot :: remaining) := by
  change
    SignedArea.Basic.polygonDoubleSignedAreaAux first first
        (middle ++ pivot :: remaining) =
      SignedArea.Basic.polygonDoubleSignedAreaAux first first (middle ++ [pivot]) +
        (Determinant.positionDeterminant first pivot +
          SignedArea.Basic.polygonDoubleSignedAreaAux first pivot remaining)
  rw [Purelib.Geometry.Polygons.SignedArea.Operations.polygonDoubleSignedAreaAux_split]
  ring1

/-- Split a polygon's signed area along a diagonal from its first vertex.

The area is the sum of the two polygons obtained by cutting the supplied vertex list at the pivot, with its order and
signed-area normalization retained (Exercise 9.6). -/
theorem exercise_9_6
    (first pivot : Plane.Point K) (middle remaining : List (Plane.Point K)) :
    SignedArea.Basic.polygonSignedArea (first :: (middle ++ pivot :: remaining)) =
      SignedArea.Basic.polygonSignedArea (first :: (middle ++ [pivot])) +
        SignedArea.Basic.polygonSignedArea (first :: pivot :: remaining) := by
  unfold SignedArea.Basic.polygonSignedArea
  rw [Geometry.Polygons.SignedArea.Operations.polygon_double_signed_area_split]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

section
/-- Move the last vertex into the closing endpoint and retain its determinant contribution. -/
private theorem
  polygonDoubleSignedAreaAux_append_singleton
    (first current last : Plane.Point K) (middle : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedAreaAux first current (middle ++ [last]) =
      SignedArea.Basic.polygonDoubleSignedAreaAux last current middle +
        Determinant.positionDeterminant last first := by
  induction middle generalizing current with
  | nil =>
      simp only [List.nil_append, SignedArea.Basic.polygonDoubleSignedAreaAux, -eq_self, -iff_self] ; rfl
  | cons next middle inductionHypothesis =>
      simp only [List.cons_append, SignedArea.Basic.polygonDoubleSignedAreaAux, -eq_self, -iff_self]
      rw [inductionHypothesis]
      ring1
/-- Reversing the remaining edge sequence and exchanging endpoints negates the determinant sum. -/
private theorem
  polygonDoubleSignedAreaAux_reverse
    (first current : Plane.Point K) (remaining : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedAreaAux first current remaining =
      -SignedArea.Basic.polygonDoubleSignedAreaAux current first remaining.reverse := by
  induction remaining generalizing current with
  | nil =>
      simp only [SignedArea.Basic.polygonDoubleSignedAreaAux, List.reverse_nil]
      unfold Determinant.positionDeterminant
      ring1
  | cons next remaining inductionHypothesis =>
      rw [Data.List.Reverse.reverse_cons]
      rw
        [Purelib.Geometry.Polygons.SignedArea.Operations.polygonDoubleSignedAreaAux_append_singleton]
      simp only [SignedArea.Basic.polygonDoubleSignedAreaAux]
      rw [inductionHypothesis]
      unfold Determinant.positionDeterminant
      ring1
/-- Moving the final vertex to the front preserves the cyclic doubled signed area. -/
private theorem
  polygonDoubleSignedArea_rotate_last
    (first : Plane.Point K) (initial : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedArea (initial ++ [first]) =
      SignedArea.Basic.polygonDoubleSignedArea (first :: initial) := by
  cases initial with
  | nil =>
      rfl
  | cons next remaining =>
      change
        SignedArea.Basic.polygonDoubleSignedAreaAux next next (remaining ++ [first]) =
          Determinant.positionDeterminant first next +
            SignedArea.Basic.polygonDoubleSignedAreaAux first next remaining
      rw
        [Purelib.Geometry.Polygons.SignedArea.Operations.polygonDoubleSignedAreaAux_append_singleton]
      ring1
end

/-- Denominator-free orientation-reversal identity underlying Exercise 9.7. -/
theorem polygon_double_signed_area_reverse (vertices : List (Plane.Point K)) :
    SignedArea.Basic.polygonDoubleSignedArea vertices.reverse =
      -SignedArea.Basic.polygonDoubleSignedArea vertices := by
  cases vertices with
  | nil =>
      simp only [List.reverse_nil, SignedArea.Basic.polygonDoubleSignedArea, SubtractionMonoid.neg_eq_of_add (0 : K) 0
        (AddZeroClass.add_zero 0), -eq_self, -iff_self]; rfl
  | cons first remaining =>
      rw [Data.List.Reverse.reverse_cons]
      rw [Purelib.Geometry.Polygons.SignedArea.Operations.polygonDoubleSignedArea_rotate_last]
      change
        SignedArea.Basic.polygonDoubleSignedAreaAux first first remaining.reverse =
          -SignedArea.Basic.polygonDoubleSignedAreaAux first first remaining
      simpa only [Data.List.Reverse.reverse_reverse] using
        Purelib.Geometry.Polygons.SignedArea.Operations.polygonDoubleSignedAreaAux_reverse first
          first remaining.reverse

/-- Exercise 9.7: reversing the supplied finite vertex list negates its signed area. -/
theorem exercise_9_7 (vertices : List (Plane.Point K)) :
    SignedArea.Basic.polygonSignedArea vertices.reverse = -SignedArea.Basic.polygonSignedArea vertices := by
  unfold SignedArea.Basic.polygonSignedArea
  rw [Geometry.Polygons.SignedArea.Operations.polygon_double_signed_area_reverse]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  ring1

end Purelib.Geometry.Polygons.SignedArea.Operations
