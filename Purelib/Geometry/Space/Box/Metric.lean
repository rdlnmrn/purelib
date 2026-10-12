module
import Purelib.Algebra.Field.Ratio
public import Purelib.Geometry.Space.Metric
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Space.Metric.DirectionSpread.Residual
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Space

open Purelib.Geometry.Space.Metric

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

namespace Purelib.Geometry.Space.Box.Metric

section

variable {K : Type*} [ExplicitField K]

/-! ## Exercise 26.1: centroid and center -/

/-- The sum of the three displayed edge vectors. -/
def boxLongDiagonal (first second third : Coordinates3.Vector K) :
  Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add first second) third
end
end Purelib.Geometry.Space.Box.Metric

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.Box.Metric

section

variable {K : Type*} [ExplicitField K]

/-- The diagonal with the first edge reversed and the other two retained. -/
def boxOppositeFirstDiagonal
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add (Coordinates3.Vector.neg first) second) third

/-- The diagonal with the second edge reversed and the other two retained. -/
def boxOppositeSecondDiagonal
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add first (Coordinates3.Vector.neg second)) third

/-- The diagonal with the third edge reversed and the other two retained. -/
def boxOppositeThirdDiagonal
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add first second) (Coordinates3.Vector.neg third)

/-- The finite dot-product calculation behind a rectangular box: all four long diagonals have quadrance `P+Q+R`, and
their three possible dot products with a fixed diagonal are obtained by changing one sign. -/
theorem box_long_diagonal_metrics
    (first second third : Coordinates3.Vector K) (P Q R : K)
    (firstQuadrance : Coordinates3.Vector.quadrance first = P)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = R)
    (firstSecond : Coordinates3.Vector.Perpendicular first second)
    (firstThird : Coordinates3.Vector.Perpendicular first third)
    (secondThird : Coordinates3.Vector.Perpendicular second third) :
    Coordinates3.Vector.quadrance (boxLongDiagonal first second third) = P + Q + R ∧
    Coordinates3.Vector.quadrance (boxOppositeFirstDiagonal first second third) = P + Q + R ∧
    Coordinates3.Vector.quadrance (boxOppositeSecondDiagonal first second third) = P + Q + R ∧
    Coordinates3.Vector.quadrance (boxOppositeThirdDiagonal first second third) = P + Q + R ∧
    Coordinates3.Vector.dot (boxLongDiagonal first second third)
        (boxOppositeFirstDiagonal first second third) = -P + Q + R ∧
    Coordinates3.Vector.dot (boxLongDiagonal first second third)
        (boxOppositeSecondDiagonal first second third) = P - Q + R ∧
    Coordinates3.Vector.dot (boxLongDiagonal first second third)
        (boxOppositeThirdDiagonal first second third) = P + Q - R := by
  have secondFirst : Coordinates3.Vector.dot second first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact firstSecond
  have thirdFirst : Coordinates3.Vector.dot third first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact firstThird
  have thirdSecond : Coordinates3.Vector.dot third second = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact secondThird
  change Coordinates3.Vector.dot first first = P at firstQuadrance
  change Coordinates3.Vector.dot second second = Q at secondQuadrance
  change Coordinates3.Vector.dot third third = R at thirdQuadrance
  unfold boxLongDiagonal boxOppositeFirstDiagonal
    boxOppositeSecondDiagonal boxOppositeThirdDiagonal
      Coordinates3.Vector.quadrance
  simp only [Coordinates3.Vector.dot_add_left, Coordinates3.Vector.dot_add_right, Coordinates3.Vector.dot_neg_left,
    Coordinates3.Vector.dot_neg_right]
  rw [firstQuadrance, secondQuadrance, thirdQuadrance,
    firstSecond, firstThird, secondThird,
    secondFirst, thirdFirst, thirdSecond]
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- Exercise 22.1. These are exactly the three spreads formed by pairs of long diagonals of a rectangular box with edge
quadrances `P,Q,R`. -/
theorem exercise_22_1
    (first second third : Coordinates3.Vector K) (P Q R : K)
    (firstQuadrance : Coordinates3.Vector.quadrance first = P)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = R)
    (firstSecond : Coordinates3.Vector.Perpendicular first second)
    (firstThird : Coordinates3.Vector.Perpendicular first third)
    (secondThird : Coordinates3.Vector.Perpendicular second third)
    (totalNonzero : P + Q + R ≠ 0) :
    Coordinates3.Vector.spread
        (boxLongDiagonal first second third)
        (boxOppositeFirstDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.1]
          exact totalNonzero) =
      4 * P * (Q + R) / (P + Q + R) ^ 2 ∧
    Coordinates3.Vector.spread
        (boxLongDiagonal first second third)
        (boxOppositeSecondDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.2.1]
          exact totalNonzero) =
      4 * Q * (R + P) / (P + Q + R) ^ 2 ∧
    Coordinates3.Vector.spread
        (boxLongDiagonal first second third)
        (boxOppositeThirdDiagonal first second third)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).1]
          exact totalNonzero)
        (by
          rw [(box_long_diagonal_metrics first second third P Q R
            firstQuadrance secondQuadrance thirdQuadrance firstSecond
            firstThird secondThird).2.2.2.1]
          exact totalNonzero) =
      4 * R * (P + Q) / (P + Q + R) ^ 2 := by
  let metrics := box_long_diagonal_metrics first second third P Q R
    firstQuadrance secondQuadrance thirdQuadrance firstSecond firstThird
    secondThird
  have firstFormula := DirectionSpread.Residual.directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeFirstDiagonal first second third)
    (P + Q + R) (-P + Q + R) totalNonzero metrics.1 metrics.2.1
    metrics.2.2.2.2.1
  have secondFormula := DirectionSpread.Residual.directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeSecondDiagonal first second third)
    (P + Q + R) (P - Q + R) totalNonzero metrics.1 metrics.2.2.1
    metrics.2.2.2.2.2.1
  have thirdFormula := DirectionSpread.Residual.directionSpread_metric_formula
    (boxLongDiagonal first second third)
    (boxOppositeThirdDiagonal first second third)
    (P + Q + R) (P + Q - R) totalNonzero metrics.1 metrics.2.2.2.1
    metrics.2.2.2.2.2.2
  constructor
  · calc
      Coordinates3.Vector.spread _ _ _ _ =
          ((P + Q + R) ^ 2 - (-P + Q + R) ^ 2) /
            (P + Q + R) ^ 2 := firstFormula
      _ = 4 * P * (Q + R) / (P + Q + R) ^ 2 := by
        congr 1
        ring1
  constructor
  · calc
      Coordinates3.Vector.spread _ _ _ _ =
          ((P + Q + R) ^ 2 - (P - Q + R) ^ 2) /
            (P + Q + R) ^ 2 := secondFormula
      _ = 4 * Q * (R + P) / (P + Q + R) ^ 2 := by
        congr 1
        ring1
  · calc
      Coordinates3.Vector.spread _ _ _ _ =
          ((P + Q + R) ^ 2 - (P + Q - R) ^ 2) /
            (P + Q + R) ^ 2 := thirdFormula
      _ = 4 * R * (P + Q) / (P + Q + R) ^ 2 := by
        congr 1
        ring1

/-- The scalar reduction of Exercise 22.2. The normal to `ABP` has squared quadrance `QR(Q+R)`, while a direction of
`PF` has quadrance `P+Q+R` and dot product `-2QR`; hence the line-plane spread has this value. -/
def boxCenterPlaneLineSpread (P Q R : K) : K :=
  4 * Q * R / ((P + Q + R) * (Q + R))

/-- The displayed center-to-opposite direction `first - second + third`. -/
def boxCenterToOppositeDirection
    (first second third : Coordinates3.Vector K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.add first (Coordinates3.Vector.neg second)) third

/-- The displayed plane normal `R*second - Q*third`. -/
def boxCenterPlaneNormal
    (second third : Coordinates3.Vector K) (Q R : K) : Coordinates3.Vector K :=
  Coordinates3.Vector.add (Coordinates3.Vector.scale R second) (Coordinates3.Vector.neg (Coordinates3.Vector.scale Q
    third))

/-- The line through the origin with the retained center-to-opposite direction. -/
def boxCenterToOppositeLine
    (first second third : Coordinates3.Vector K) : Metric.Line3 K :=
  ⟨⟨0, 0, 0⟩, boxCenterToOppositeDirection first second third⟩

/-- The plane through the origin with normal `R*second - Q*third`. -/
def boxCenterPlane
    (second third : Coordinates3.Vector K) (Q R : K) : Metric.Plane3 K :=
  ⟨boxCenterPlaneNormal second third Q R, 0⟩

/-- The three metric values used in Exercise 22.2. Multiplying the midpoint directions by two removes every coordinate
denominator. -/
theorem box_center_plane_line_metrics
    (first second third : Coordinates3.Vector K) (P Q R : K)
    (firstQuadrance : Coordinates3.Vector.quadrance first = P)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = R)
    (firstSecond : Coordinates3.Vector.Perpendicular first second)
    (firstThird : Coordinates3.Vector.Perpendicular first third)
    (secondThird : Coordinates3.Vector.Perpendicular second third) :
    Coordinates3.Vector.quadrance
        (boxCenterToOppositeDirection first second third) = P + Q + R ∧
      Coordinates3.Vector.quadrance (boxCenterPlaneNormal second third Q R) =
        Q * R * (Q + R) ∧
      Coordinates3.Vector.dot (boxCenterToOppositeDirection first second third)
          (boxCenterPlaneNormal second third Q R) = -2 * Q * R := by
  have secondFirst : Coordinates3.Vector.dot second first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact firstSecond
  have thirdFirst : Coordinates3.Vector.dot third first = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact firstThird
  have thirdSecond : Coordinates3.Vector.dot third second = 0 := by
    rw [Coordinates3.Vector.dot_comm]
    exact secondThird
  change Coordinates3.Vector.dot first first = P at firstQuadrance
  change Coordinates3.Vector.dot second second = Q at secondQuadrance
  change Coordinates3.Vector.dot third third = R at thirdQuadrance
  unfold boxCenterToOppositeDirection boxCenterPlaneNormal Coordinates3.Vector.quadrance
  simp only [Coordinates3.Vector.dot_add_left, Coordinates3.Vector.dot_add_right,
    Coordinates3.Vector.dot_neg_left, Coordinates3.Vector.dot_neg_right,
    Coordinates3.Vector.dot_scale_left, Coordinates3.Vector.dot_scale_right]
  rw [firstQuadrance, secondQuadrance, thirdQuadrance,
    firstSecond, firstThird, secondThird,
    secondFirst, thirdFirst, thirdSecond]
  constructor
  · ring1
  constructor <;> ring1

/-- Exercise 22.2 in spatial coordinates. The displayed normal is `R·BC-Q·CG`; the displayed line direction is twice
`PF`. -/
theorem exercise_22_2_geometric
    (first second third : Coordinates3.Vector K) (P Q R : K)
    (firstQuadrance : Coordinates3.Vector.quadrance first = P)
    (secondQuadrance : Coordinates3.Vector.quadrance second = Q)
    (thirdQuadrance : Coordinates3.Vector.quadrance third = R)
    (firstSecond : Coordinates3.Vector.Perpendicular first second)
    (firstThird : Coordinates3.Vector.Perpendicular first third)
    (secondThird : Coordinates3.Vector.Perpendicular second third)
    (totalNonzero : P + Q + R ≠ 0)
    (QNonzero : Q ≠ 0) (RNonzero : R ≠ 0)
    (sumNonzero : Q + R ≠ 0)
    (lineNonNull :
      ¬ (boxCenterToOppositeLine first second third).IsNull)
    (planeNonNull : ¬ (boxCenterPlane second third Q R).IsNull) :
    Metric.linePlaneSpread
        (boxCenterToOppositeLine first second third)
        (boxCenterPlane second third Q R)
        lineNonNull planeNonNull = boxCenterPlaneLineSpread P Q R := by
  let metrics := box_center_plane_line_metrics first second third P Q R
    firstQuadrance secondQuadrance thirdQuadrance firstSecond firstThird
    secondThird
  have QRNonzero : Q * R ≠ 0 :=
    ExplicitField.mul_ne_zero QNonzero RNonzero
  have normalMetricNonzero : Q * R * (Q + R) ≠ 0 :=
    ExplicitField.mul_ne_zero QRNonzero sumNonzero
  have leftDenominatorNonzero :
      (P + Q + R) * (Q * R * (Q + R)) ≠ 0 :=
    ExplicitField.mul_ne_zero totalNonzero normalMetricNonzero
  have rightDenominatorNonzero :
      (P + Q + R) * (Q + R) ≠ 0 :=
    ExplicitField.mul_ne_zero totalNonzero sumNonzero
  unfold Metric.linePlaneSpread boxCenterToOppositeLine boxCenterPlane
  change
    Coordinates3.Vector.dot (boxCenterToOppositeDirection first second third)
          (boxCenterPlaneNormal second third Q R) ^ 2 /
        (Coordinates3.Vector.quadrance
            (boxCenterToOppositeDirection first second third) *
          Coordinates3.Vector.quadrance (boxCenterPlaneNormal second third Q R)) = _
  rw [metrics.1, metrics.2.1, metrics.2.2]
  unfold boxCenterPlaneLineSpread
  apply Ratio.ratio_eq_of_cross_product
    leftDenominatorNonzero rightDenominatorNonzero
  ring1
end
end Purelib.Geometry.Space.Box.Metric

end
