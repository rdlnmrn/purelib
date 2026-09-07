import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.Quadrea

/-!
# Divine Proportions, Chapter 9: finite oriented areas

An oriented polygon is represented by a finite `List` of points.  The
denominator-free primitive is twice its signed area; the book's signed area is
obtained by dividing that finite sum by two.  This keeps the cancellation and
characteristic assumptions visible while the core shoelace and
Bretschneider identities remain polynomial.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Oriented determinant of two position vectors. -/
def positionDeterminant (first second : Point K) : K :=
  first.x * second.y - second.x * first.y

/-- Twice the signed area of an oriented triangle. -/
def triangleDoubleSignedArea (first second third : Point K) : K :=
  positionDeterminant first second + positionDeterminant second third +
    positionDeterminant third first

/-- The book's signed area of an oriented triangle. -/
def triangleSignedArea (first second third : Point K) : K :=
  triangleDoubleSignedArea first second third / 2

/-- Shoelace recursion from `current` through the remaining vertices and
back to `first`. -/
def polygonDoubleSignedAreaAux (first current : Point K) :
    List (Point K) → K
  | [] => positionDeterminant current first
  | next :: remaining =>
      positionDeterminant current next +
        polygonDoubleSignedAreaAux first next remaining

/-- Twice the signed area of a finite oriented polygon. -/
def polygonDoubleSignedArea : List (Point K) → K
  | [] => 0
  | first :: remaining =>
      polygonDoubleSignedAreaAux first first remaining

/-- The book's signed area of a finite oriented polygon. -/
def polygonSignedArea (vertices : List (Point K)) : K :=
  polygonDoubleSignedArea vertices / 2

/-- Finite fan triangulation about `center`. -/
def fanDoubleSignedAreaAux (center first current : Point K) :
    List (Point K) → K
  | [] => triangleDoubleSignedArea center current first
  | next :: remaining =>
      triangleDoubleSignedArea center current next +
        fanDoubleSignedAreaAux center first next remaining

/-- Sum of the doubled signed areas of the triangles from `center` to every
cyclic edge of the finite polygon. -/
def fanDoubleSignedArea (center : Point K) : List (Point K) → K
  | [] => 0
  | first :: remaining => fanDoubleSignedAreaAux center first first remaining

/-- The corresponding sum in the book's signed-area normalization. -/
def fanSignedArea (center : Point K) (vertices : List (Point K)) : K :=
  fanDoubleSignedArea center vertices / 2

/-- The telescoping identity underlying Theorem 62. -/
private theorem fanDoubleSignedAreaAux_eq
    (center first current : Point K) (remaining : List (Point K)) :
    fanDoubleSignedAreaAux center first current remaining =
      polygonDoubleSignedAreaAux first current remaining +
        positionDeterminant center current + positionDeterminant first center := by
  induction remaining generalizing current with
  | nil =>
      unfold fanDoubleSignedAreaAux polygonDoubleSignedAreaAux
        triangleDoubleSignedArea positionDeterminant
      ring1
  | cons next remaining inductionHypothesis =>
      unfold fanDoubleSignedAreaAux polygonDoubleSignedAreaAux
      rw [inductionHypothesis]
      unfold triangleDoubleSignedArea positionDeterminant
      ring1

/-- Denominator-cleared Theorem 62: the fan sum is independent of its center
and equals the finite cyclic shoelace sum. -/
theorem fan_double_signed_area
    (center : Point K) (vertices : List (Point K)) :
    fanDoubleSignedArea center vertices = polygonDoubleSignedArea vertices := by
  cases vertices with
  | nil => rfl
  | cons first remaining =>
      change fanDoubleSignedAreaAux center first first remaining =
        polygonDoubleSignedAreaAux first first remaining
      rw [fanDoubleSignedAreaAux_eq]
      unfold positionDeterminant
      ring1

/-- Theorem 62 (Signed area), in the book's `/2` normalization. -/
theorem signed_area (center : Point K) (vertices : List (Point K)) :
    fanSignedArea center vertices = polygonSignedArea vertices := by
  unfold fanSignedArea polygonSignedArea
  rw [fan_double_signed_area]

/-- The explicit independence-of-`P` statement from Theorem 62. -/
theorem fan_signed_area_independent
    (firstCenter secondCenter : Point K) (vertices : List (Point K)) :
    fanSignedArea firstCenter vertices = fanSignedArea secondCenter vertices := by
  rw [signed_area, signed_area]

/-- The triangle quadrea is sixteen times the square of its signed area. -/
theorem triangle_quadrea_eq_sixteen_signed_area_square
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrea first second third =
      16 * triangleSignedArea first second third ^ 2 := by
  have doubled :
      2 * triangleSignedArea first second third =
        triangleDoubleSignedArea first second third := by
    unfold triangleSignedArea
    calc
      2 * (triangleDoubleSignedArea first second third / 2) =
          (triangleDoubleSignedArea first second third / 2) * 2 := by ring1
      _ = triangleDoubleSignedArea first second third :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  calc
    quadrea first second third =
        4 * triangleDoubleSignedArea first second third ^ 2 := by
      rw [quadrea_coordinate_formula]
      unfold pointDeterminant triangleDoubleSignedArea positionDeterminant
      ring1
    _ = 16 * triangleSignedArea first second third ^ 2 := by
      rw [← doubled]
      ring1

/-- Quadrea of a finite oriented polygon in denominator-free form. -/
def polygonQuadrea (vertices : List (Point K)) : K :=
  4 * polygonDoubleSignedArea vertices ^ 2

/-- The finite polygon definition agrees with `16a²` when two is invertible. -/
theorem polygon_quadrea_eq_sixteen_signed_area_square
    (vertices : List (Point K)) (twoNonzero : (2 : K) ≠ 0) :
    polygonQuadrea vertices = 16 * polygonSignedArea vertices ^ 2 := by
  have doubled : 2 * polygonSignedArea vertices =
      polygonDoubleSignedArea vertices := by
    unfold polygonSignedArea
    calc
      2 * (polygonDoubleSignedArea vertices / 2) =
          (polygonDoubleSignedArea vertices / 2) * 2 := by ring1
      _ = polygonDoubleSignedArea vertices :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  unfold polygonQuadrea
  rw [← doubled]
  ring1

/-- Exercise 9.4: exact signed area of the displayed quadrilateral. -/
theorem exercise_9_4 (k l m n : K) :
    let first : Point K := ⟨k, 0⟩
    let second : Point K := ⟨l, 0⟩
    let third : Point K := ⟨l, n⟩
    let fourth : Point K := ⟨k, m⟩
    polygonSignedArea [first, second, third, fourth] =
      (m + n) * (l - k) / 2 := by
  dsimp only
  simp only [polygonSignedArea, polygonDoubleSignedArea,
    polygonDoubleSignedAreaAux, positionDeterminant]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Exercise 9.5, strengthened to a fan based at any displayed point: a
finite polygon's signed area is the sum of its oriented fan triangles. -/
theorem exercise_9_5 (center : Point K) (vertices : List (Point K)) :
    polygonSignedArea vertices = fanSignedArea center vertices :=
  (signed_area center vertices).symm

/-- Theorem 63 (Bretschneider's formula), as a direct finite polynomial
identity for four displayed points. -/
theorem bretschneider_formula
    (first second third fourth : Point K) :
    polygonQuadrea [first, second, third, fourth] =
      4 * quadrance first third * quadrance second fourth -
        (quadrance first second + quadrance third fourth -
          quadrance second third - quadrance first fourth) ^ 2 := by
  simp only [polygonQuadrea, polygonDoubleSignedArea,
    polygonDoubleSignedAreaAux, positionDeterminant, quadrance]
  ring1

end DivineProportions
