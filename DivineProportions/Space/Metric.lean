import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ExplicitField

/-!
# Finite three-dimensional metric algebra

This is the coordinate layer used by Chapter 22.  It deliberately contains
only three displayed coordinates and finite polynomial operations: no vector
space basis, dimension cardinality, completion, norm, or square-root
construction is imported.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed vector in three-dimensional Cartesian coordinates.  Points
use the same three-coordinate data, with displacement written explicitly. -/
structure Vector3 (K : Type*) where
  x : K
  y : K
  z : K

abbrev Point3 (K : Type*) := Vector3 K

namespace Vector3

def add (left right : Vector3 K) : Vector3 K :=
  ⟨left.x + right.x, left.y + right.y, left.z + right.z⟩

def neg (vector : Vector3 K) : Vector3 K :=
  ⟨-vector.x, -vector.y, -vector.z⟩

def sub (left right : Vector3 K) : Vector3 K :=
  ⟨left.x - right.x, left.y - right.y, left.z - right.z⟩

def scale (scalar : K) (vector : Vector3 K) : Vector3 K :=
  ⟨scalar * vector.x, scalar * vector.y, scalar * vector.z⟩

/-- The finite Cartesian dot product. -/
def dot (left right : Vector3 K) : K :=
  left.x * right.x + left.y * right.y + left.z * right.z

/-- Quadrance of a displayed vector. -/
def quadrance (vector : Vector3 K) : K := dot vector vector

def Orthogonal (left right : Vector3 K) : Prop := dot left right = 0

def Parallel (left right : Vector3 K) : Prop :=
  ∃ scalar : K, scalar ≠ 0 ∧ left = scale scalar right

@[simp] theorem dot_add_left (first second third : Vector3 K) :
    dot (add first second) third = dot first third + dot second third := by
  unfold dot add
  ring1

@[simp] theorem dot_add_right (first second third : Vector3 K) :
    dot first (add second third) = dot first second + dot first third := by
  unfold dot add
  ring1

@[simp] theorem dot_neg_left (first second : Vector3 K) :
    dot (neg first) second = -dot first second := by
  unfold dot neg
  ring1

@[simp] theorem dot_neg_right (first second : Vector3 K) :
    dot first (neg second) = -dot first second := by
  unfold dot neg
  ring1

@[simp] theorem dot_scale_left (scalar : K) (first second : Vector3 K) :
    dot (scale scalar first) second = scalar * dot first second := by
  unfold dot scale
  ring1

@[simp] theorem dot_scale_right (scalar : K) (first second : Vector3 K) :
    dot first (scale scalar second) = scalar * dot first second := by
  unfold dot scale
  ring1

theorem dot_comm (first second : Vector3 K) :
    dot first second = dot second first := by
  unfold dot
  ring1

theorem quadrance_add (first second : Vector3 K) :
    quadrance (add first second) =
      quadrance first + quadrance second + 2 * dot first second := by
  unfold quadrance dot add
  ring1

/-- Three-dimensional Pythagoras for two explicitly orthogonal vectors. -/
theorem quadrance_add_of_orthogonal (first second : Vector3 K)
    (orthogonal : Orthogonal first second) :
    quadrance (add first second) = quadrance first + quadrance second := by
  rw [quadrance_add, orthogonal]
  ring1

@[simp] theorem quadrance_neg (vector : Vector3 K) :
    quadrance (neg vector) = quadrance vector := by
  unfold quadrance dot neg
  ring1

theorem quadrance_scale (scalar : K) (vector : Vector3 K) :
    quadrance (scale scalar vector) = scalar ^ 2 * quadrance vector := by
  unfold quadrance dot scale
  ring1

end Vector3

/-- A displayed affine plane `n·x+c=0`. -/
structure Plane3 (K : Type*) where
  normal : Vector3 K
  constant : K

namespace Plane3

def Contains (plane : Plane3 K) (point : Point3 K) : Prop :=
  Vector3.dot plane.normal point + plane.constant = 0

def IsNull (plane : Plane3 K) : Prop :=
  Vector3.quadrance plane.normal = 0

end Plane3

/-- A displayed affine line with one point and one direction. -/
structure Line3 (K : Type*) where
  point : Point3 K
  direction : Vector3 K

namespace Line3

def Contains (line : Line3 K) (point : Point3 K) : Prop :=
  ∃ scalar : K,
    point = Vector3.add line.point (Vector3.scale scalar line.direction)

def IsNull (line : Line3 K) : Prop :=
  Vector3.quadrance line.direction = 0

/-- A line is perpendicular to a plane when its displayed direction is a
nonzero scalar multiple of the displayed normal. -/
def Perpendicular (line : Line3 K) (plane : Plane3 K) : Prop :=
  Vector3.Parallel line.direction plane.normal

end Line3

/-- Spread between two displayed, non-null spatial directions. -/
def directionSpread (first second : Vector3 K)
    (_firstNonNull : Vector3.quadrance first ≠ 0)
    (_secondNonNull : Vector3.quadrance second ≠ 0) : K :=
  1 - Vector3.dot first second ^ 2 /
    (Vector3.quadrance first * Vector3.quadrance second)

/-- Chapter 22.1's spread between two planes, computed from their normals. -/
def planeSpread (first second : Plane3 K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) : K :=
  directionSpread first.normal second.normal firstNonNull secondNonNull

/-- Chapter 22.1's spread between a line and a plane.  It is the complement
of the spread between the line direction and the plane normal. -/
def linePlaneSpread (line : Line3 K) (plane : Plane3 K)
    (_lineNonNull : ¬ line.IsNull) (_planeNonNull : ¬ plane.IsNull) : K :=
  Vector3.dot line.direction plane.normal ^ 2 /
    (Vector3.quadrance line.direction *
      Vector3.quadrance plane.normal)

/-- The two spatial spread definitions are complementary by construction. -/
theorem linePlaneSpread_add_directionSpread
    (line : Line3 K) (plane : Plane3 K)
    (_lineNonNull : ¬ line.IsNull) (_planeNonNull : ¬ plane.IsNull) :
    linePlaneSpread line plane _lineNonNull _planeNonNull +
        directionSpread line.direction plane.normal
          _lineNonNull _planeNonNull = 1 := by
  unfold linePlaneSpread directionSpread
  ring1

end DivineProportions
