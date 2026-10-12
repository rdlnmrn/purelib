module
import Purelib.Data.Rat.Fraction.ExplicitOrder.Sign
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector

import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Geometry.Rotations.Projective.Action
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

/-!
# The introductory `(2:1:2:3)` rotation

The worked example preceding Section 2 is checked exactly over the
repository's canonical rational carrier.
-/

namespace formalisations.RationalRotations.Chapters.IntroductoryExample

open Purelib.LinearAlgebra.Coordinates3

/-- The canonical constructive rational coefficient type for the introductory rotation. -/
abbrev Scalar := Fraction.Rational

/-- The rotation axis (1, 2, 3). -/
def axis : Vector Fraction.Rational := ⟨1, 2, 3⟩

/-- The displayed axis has quadrance fourteen. -/
theorem axis_quadrance : axis.quadrance = 14 := by
  unfold axis Vector3.quadrance Vector3.dot
  ring1

/-- The displayed proportion `(2:1:2:3)`. -/
def proportion : Algebra.Quaternion.Projective.Basic.NonNullProportion Fraction.Rational where
  scalar := 2
  vector := axis
  normNonzero := by
    change (18 : Fraction.Rational) ≠ 0
    decide

/-- The displayed proportion (2:1:2:3) has norm eighteen. -/
theorem proportion_norm : proportion.toProportion.norm = 18 := by
  unfold formalisations.RationalRotations.Chapters.IntroductoryExample.proportion
    Algebra.Quaternion.Projective.Basic.Proportion.norm
  rw [formalisations.RationalRotations.Chapters.IntroductoryExample.axis_quadrance]
  ring1

/-- The exact rational rotation matrix of the proportion (2:1:2:3).

Its rows retain the nine displayed entries with common denominator nine. -/
def displayed : Matrix3 Fraction.Rational :=
  ⟨(-4 : Fraction.Rational) / 9, 8 / 9, -1 / 9,
    -4 / 9, -1 / 9, 8 / 9,
    7 / 9, 4 / 9, 4 / 9⟩

/-- The projective quaternion action yields exactly the displayed rational matrix. -/
theorem rotation_matrix : (Rotations.Projective.Action.NonNullProportion.rotationMatrix
  formalisations.RationalRotations.Chapters.IntroductoryExample.proportion) =
  formalisations.RationalRotations.Chapters.IntroductoryExample.displayed := by
  decide

/-- The displayed rational matrix is orthogonal. -/
theorem displayed_isOrthogonal : displayed.IsOrthogonal := by
  rw [← formalisations.RationalRotations.Chapters.IntroductoryExample.rotation_matrix]
  exact (Rotations.Projective.Action.NonNullProportion.rotation
    formalisations.RationalRotations.Chapters.IntroductoryExample.proportion).orthogonal

/-- The displayed rational matrix has determinant one. -/
theorem displayed_determinant : displayed.determinant = 1 := by
  rw [← formalisations.RationalRotations.Chapters.IntroductoryExample.rotation_matrix]
  exact (Rotations.Projective.Action.NonNullProportion.rotation
    formalisations.RationalRotations.Chapters.IntroductoryExample.proportion).determinantOne

/-- The displayed matrix fixes its axis (1, 2, 3) under row multiplication. -/
theorem axis_fixed : Matrix3.rowMul axis formalisations.RationalRotations.Chapters.IntroductoryExample.displayed = axis
  := by
  decide

/-- The displayed rotation has half-spread 7/9. -/
theorem halfSpread_value :
    Rotations.Spread.halfSpread (Rotations.Projective.Action.NonNullProportion.rotation
      formalisations.RationalRotations.Chapters.IntroductoryExample.proportion) = (7 : Fraction.Rational) / 9 := by
  rw [Rotations.Projective.Action.NonNullProportion.halfSpread_rotation
    formalisations.RationalRotations.Chapters.IntroductoryExample.proportion (by decide)]
  change axis.quadrance / proportion.toProportion.norm = (7 : Fraction.Rational) / 9
  rw [formalisations.RationalRotations.Chapters.IntroductoryExample.axis_quadrance,
    formalisations.RationalRotations.Chapters.IntroductoryExample.proportion_norm]
  decide

/-- The displayed rotation matrix has trace −1/9. -/
theorem trace_value : Matrix3.trace formalisations.RationalRotations.Chapters.IntroductoryExample.displayed = (-1 :
  Fraction.Rational) / 9 := by
  decide

/-- The trace formula recovers the displayed half-spread 7/9. -/
theorem halfSpread_from_trace :
    (3 - Matrix3.trace formalisations.RationalRotations.Chapters.IntroductoryExample.displayed) / 4 = (7 :
      Fraction.Rational) / 9 := by
  rw [formalisations.RationalRotations.Chapters.IntroductoryExample.trace_value]
  decide

/-- Negating the vector part of the proportion gives the transpose inverse
matrix exactly. -/
theorem conjugate_matrix :
    Rotations.Projective.Action.NonNullProportion.rotationMatrix
      (Algebra.Quaternion.Projective.Basic.NonNullProportion.conjugate
        formalisations.RationalRotations.Chapters.IntroductoryExample.proportion) =
      Matrix3.transpose formalisations.RationalRotations.Chapters.IntroductoryExample.displayed := by
  decide

end formalisations.RationalRotations.Chapters.IntroductoryExample
