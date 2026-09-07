import DivineProportions.Oriented.SignedArea

/-!
# Divine Proportions, Chapter 9: finite polygon exercises

Exercises 9.6 and 9.7 are finite identities for the cyclic shoelace sum.
Splitting a polygon introduces two oppositely oriented copies of one diagonal;
reversing it reverses every edge.  The proofs operate directly on the supplied
vertex lists.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem polygonDoubleSignedAreaAux_split
    (first current pivot : Point K)
    (middle remaining : List (Point K)) :
    polygonDoubleSignedAreaAux first current
        (middle ++ pivot :: remaining) =
      polygonDoubleSignedAreaAux first current (middle ++ [pivot]) +
        positionDeterminant first pivot +
        polygonDoubleSignedAreaAux first pivot remaining := by
  induction middle generalizing current with
  | nil =>
      simp only [List.nil_append, polygonDoubleSignedAreaAux]
      unfold positionDeterminant
      ring1
  | cons next middle inductionHypothesis =>
      simp only [List.cons_append, polygonDoubleSignedAreaAux]
      rw [inductionHypothesis]
      ring1

/-- Denominator-free form of Exercise 9.6.  The list `middle` contains the
vertices strictly between the first vertex and the displayed split vertex.
The source's bounds `3 ≤ m < n` merely ensure both printed polygons have the
intended sizes; the algebraic identity itself needs no length premise. -/
theorem polygon_double_signed_area_split
    (first pivot : Point K) (middle remaining : List (Point K)) :
    polygonDoubleSignedArea
        (first :: (middle ++ pivot :: remaining)) =
      polygonDoubleSignedArea (first :: (middle ++ [pivot])) +
        polygonDoubleSignedArea (first :: pivot :: remaining) := by
  change
    polygonDoubleSignedAreaAux first first
        (middle ++ pivot :: remaining) =
      polygonDoubleSignedAreaAux first first (middle ++ [pivot]) +
        (positionDeterminant first pivot +
          polygonDoubleSignedAreaAux first pivot remaining)
  rw [polygonDoubleSignedAreaAux_split]
  ring1

/-- Exercise 9.6 in the book's signed-area normalization. -/
theorem exercise_9_6
    (first pivot : Point K) (middle remaining : List (Point K)) :
    polygonSignedArea (first :: (middle ++ pivot :: remaining)) =
      polygonSignedArea (first :: (middle ++ [pivot])) +
        polygonSignedArea (first :: pivot :: remaining) := by
  unfold polygonSignedArea
  rw [polygon_double_signed_area_split]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

private theorem polygonDoubleSignedAreaAux_append_singleton
    (first current last : Point K) (middle : List (Point K)) :
    polygonDoubleSignedAreaAux first current (middle ++ [last]) =
      polygonDoubleSignedAreaAux last current middle +
        positionDeterminant last first := by
  induction middle generalizing current with
  | nil =>
      simp only [List.nil_append, polygonDoubleSignedAreaAux]
  | cons next middle inductionHypothesis =>
      simp only [List.cons_append, polygonDoubleSignedAreaAux]
      rw [inductionHypothesis]
      ring1

private theorem polygonDoubleSignedAreaAux_reverse
    (first current : Point K) (remaining : List (Point K)) :
    polygonDoubleSignedAreaAux first current remaining =
      -polygonDoubleSignedAreaAux current first remaining.reverse := by
  induction remaining generalizing current with
  | nil =>
      simp only [polygonDoubleSignedAreaAux, List.reverse_nil]
      unfold positionDeterminant
      ring1
  | cons next remaining inductionHypothesis =>
      rw [List.reverse_cons]
      rw [polygonDoubleSignedAreaAux_append_singleton]
      simp only [polygonDoubleSignedAreaAux]
      rw [inductionHypothesis]
      unfold positionDeterminant
      ring1

private theorem polygonDoubleSignedArea_rotate_last
    (first : Point K) (initial : List (Point K)) :
    polygonDoubleSignedArea (initial ++ [first]) =
      polygonDoubleSignedArea (first :: initial) := by
  cases initial with
  | nil =>
      rfl
  | cons next remaining =>
      change
        polygonDoubleSignedAreaAux next next (remaining ++ [first]) =
          positionDeterminant first next +
            polygonDoubleSignedAreaAux first next remaining
      rw [polygonDoubleSignedAreaAux_append_singleton]
      ring1

/-- Denominator-free orientation-reversal identity underlying Exercise 9.7. -/
theorem polygon_double_signed_area_reverse (vertices : List (Point K)) :
    polygonDoubleSignedArea vertices.reverse =
      -polygonDoubleSignedArea vertices := by
  cases vertices with
  | nil =>
      simp only [List.reverse_nil, polygonDoubleSignedArea, neg_zero]
  | cons first remaining =>
      rw [List.reverse_cons]
      rw [polygonDoubleSignedArea_rotate_last]
      change
        polygonDoubleSignedAreaAux first first remaining.reverse =
          -polygonDoubleSignedAreaAux first first remaining
      simpa only [List.reverse_reverse] using
        polygonDoubleSignedAreaAux_reverse first first remaining.reverse

/-- Exercise 9.7: reversing the supplied finite vertex list negates its
signed area. -/
theorem exercise_9_7 (vertices : List (Point K)) :
    polygonSignedArea vertices.reverse = -polygonSignedArea vertices := by
  unfold polygonSignedArea
  rw [polygon_double_signed_area_reverse]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

end DivineProportions
