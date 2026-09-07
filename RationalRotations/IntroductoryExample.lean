import RationalRotations.RayProportions

/-!
# The introductory `(2:1:2:3)` rotation

The worked example preceding Section 2 is checked exactly over the
repository's canonical rational carrier.
-/

namespace RationalRotations.IntroductoryExample

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def axis : Vector Scalar := ⟨1, 2, 3⟩

theorem axis_quadrance : axis.quadrance = 14 := by
  unfold axis Vector.quadrance Vector.dot
  ring1

/-- The displayed proportion `(2:1:2:3)`. -/
def proportion : NonNullProportion Scalar where
  scalar := 2
  vector := axis
  normNonzero := by
    change (18 : Scalar) ≠ 0
    decide

theorem proportion_norm : proportion.toProportion.norm = 18 := by
  unfold proportion Proportion.norm
  rw [axis_quadrance]
  ring1

def displayed : Matrix3 Scalar :=
  ⟨(-4 : Scalar) / 9, 8 / 9, -1 / 9,
    -4 / 9, -1 / 9, 8 / 9,
    7 / 9, 4 / 9, 4 / 9⟩

theorem rotation_matrix : proportion.rotationMatrix = displayed := by
  decide

theorem displayed_isOrthogonal : displayed.IsOrthogonal := by
  rw [← rotation_matrix]
  exact proportion.rotation.orthogonal

theorem displayed_determinant : displayed.determinant = 1 := by
  rw [← rotation_matrix]
  exact proportion.rotation.determinantOne

theorem axis_fixed : Matrix3.rowMul axis displayed = axis := by
  decide

theorem halfSpread_value :
    halfSpread proportion.rotation = (7 : Scalar) / 9 := by
  rw [NonNullProportion.halfSpread_rotation proportion (by decide)]
  change axis.quadrance / proportion.toProportion.norm = (7 : Scalar) / 9
  rw [axis_quadrance, proportion_norm]
  decide

theorem trace_value : Matrix3.trace displayed = (-1 : Scalar) / 9 := by
  decide

theorem halfSpread_from_trace :
    (3 - Matrix3.trace displayed) / 4 = (7 : Scalar) / 9 := by
  rw [trace_value]
  decide

/-- Negating the vector part of the proportion gives the transpose inverse
matrix exactly. -/
theorem conjugate_matrix :
    (NonNullProportion.conjugate proportion).rotationMatrix =
      Matrix3.transpose displayed := by
  decide

end RationalRotations.IntroductoryExample
