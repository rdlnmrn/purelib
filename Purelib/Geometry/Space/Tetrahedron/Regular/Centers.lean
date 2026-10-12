module
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Space.Box.Metric
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Space.Box

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Geometry.Space.Tetrahedron.Regular.Centers

section

variable {K : Type*} [ExplicitField K]

/-- Displacement from one tetrahedron vertex to the centroid of its opposite face, expressed in its three outgoing edge
vectors. -/
def oppositeFaceCentroidDisplacement
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale ((1 : K) / 3) (Metric.boxLongDiagonal first second third)

/-- Displacement from one tetrahedron vertex to the tetrahedron center. -/
def tetrahedronCenterDisplacement
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.scale ((1 : K) / 4) (Metric.boxLongDiagonal first second third)

/-- Three equal outgoing edges whose pairwise endpoint distances are also `Q` have triple-sum quadrance `6Q`. -/
theorem regular_tetrahedron_triple_sum_quadrance
    (first second third : Coordinates3.Vector K) (Q : K)
    (firstQuadrance : Coordinates3.Vector.quadrance first = Q)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = Q)
    (firstSecondDot : 2 * Coordinates3.Vector.dot first second = Q)
    (firstThirdDot : 2 * Coordinates3.Vector.dot first third = Q)
    (secondThirdDot : 2 * Coordinates3.Vector.dot second third = Q) :
    Coordinates3.Vector.quadrance (Metric.boxLongDiagonal first second third) = 6 * Q := by
  unfold Metric.boxLongDiagonal
  calc
    Coordinates3.Vector.quadrance (Coordinates3.Vector.add (Coordinates3.Vector.add first second) third) =
        Coordinates3.Vector.quadrance first + Coordinates3.Vector.quadrance second +
          Coordinates3.Vector.quadrance third +
          2 * Coordinates3.Vector.dot first second + 2 * Coordinates3.Vector.dot first third +
          2 * Coordinates3.Vector.dot second third := by
            rw [Coordinates3.Vector.quadrance_add, Coordinates3.Vector.quadrance_add, Coordinates3.Vector.dot_add_left]
            ring1
    _ = 6 * Q := by
      rw [firstQuadrance, secondQuadrance, thirdQuadrance,
        firstSecondDot, firstThirdDot, secondThirdDot]
      ring1

/-- Exercise 26.1. The two displayed quotient formulas are kept in their stronger cleared forms `3Q(A,G)=2Q` and
`8Q(A,P)=3Q`. -/
theorem exercise_26_1
    (first second third : Coordinates3.Vector K) (Q : K)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (firstQuadrance : Coordinates3.Vector.quadrance first = Q)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = Q)
    (firstSecondDot : 2 * Coordinates3.Vector.dot first second = Q)
    (firstThirdDot : 2 * Coordinates3.Vector.dot first third = Q)
    (secondThirdDot : 2 * Coordinates3.Vector.dot second third = Q) :
    3 * Coordinates3.Vector.quadrance
        (oppositeFaceCentroidDisplacement first second third) =
        2 * Q ∧
      8 * Coordinates3.Vector.quadrance
        (tetrahedronCenterDisplacement first second third) =
        3 * Q := by
  have sumQuadrance := regular_tetrahedron_triple_sum_quadrance
    first second third Q firstQuadrance secondQuadrance thirdQuadrance
    firstSecondDot firstThirdDot secondThirdDot
  have oneThirdCancel : ((1 : K) / 3) * 3 = 1 :=
    ExplicitField.div_mul_cancel 1 threeNonzero
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have oneFourthCancel : ((1 : K) / 4) * 4 = 1 :=
    ExplicitField.div_mul_cancel 1 fourNonzero
  constructor
  · unfold oppositeFaceCentroidDisplacement
    rw [Coordinates3.Vector.quadrance_scale, sumQuadrance]
    calc
      3 * (((1 : K) / 3) ^ 2 * (6 * Q)) =
          2 * ((((1 : K) / 3) * 3) ^ 2) * Q := by ring1
      _ = 2 * Q := by rw [oneThirdCancel]; ring1
  · unfold tetrahedronCenterDisplacement
    rw [Coordinates3.Vector.quadrance_scale, sumQuadrance]
    calc
      8 * (((1 : K) / 4) ^ 2 * (6 * Q)) =
          3 * ((((1 : K) / 4) * 4) ^ 2) * Q := by ring1
      _ = 3 * Q := by rw [oneFourthCancel]; ring1
end
end Purelib.Geometry.Space.Tetrahedron.Regular.Centers

end
