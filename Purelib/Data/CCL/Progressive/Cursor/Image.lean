module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Data.CCL.Progressive.Cursor.Refinement
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
public section

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace Purelib.Data.CCL.Progressive.Cursor.Image

namespace Mode

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Represent the retained mode's parser-tail normalization by its exact projective matrix.

Initial mode uses the identity; low and loop use inverse and forward gamma powers at their retained counts. Residual
mode uses the gamma inversion matrix, including tails represented homogeneously at zero. -/
@[expose] def tailMatrix :
    Transducer.Mode → LinearAlgebra.Coordinates2.Matrix.GaussianMatrix
  | .initial _ => Matrix2.identityMatrix
  | .low current =>
      Line.Matrix.scale
        (Power.natPow Basic.Canonical.gamma current.count)⁻¹
  | .loop current =>
      Line.Matrix.scale
        (Power.natPow Basic.Canonical.gamma current.count)
  | .residual _ => Line.Matrix.invert Basic.Canonical.gamma

section
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
/-- Acting on a value's affine point by the exact mode tail matrix gives its retained parser tail. -/
theorem tailMatrix_act (mode : Transducer.Mode) (value : Basic.Canonical) :
    Line.Matrix.act (Cursor.Image.Mode.tailMatrix mode) (Line.Proj.affine value) =
      Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail mode value := by
  cases mode with
  | initial current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Matrix2.identityMatrix,
          Line.Matrix.act, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl
  | low current | loop current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Line.Matrix.act, Line.Matrix.scale, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl
  | residual current =>
      apply Line.Proj.ext <;>
        simp [Cursor.Image.Mode.tailMatrix, Line.Matrix.act, Line.Matrix.invert, Line.Proj.affine,
          Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail, -eq_self, -iff_self ] <;> rfl

/-- Every retained mode's exact tail matrix has nonzero determinant. -/
theorem tailMatrix_det_ne (mode : Transducer.Mode) :
    Matrix2.Matrix2.determinant (Cursor.Image.Mode.tailMatrix mode) ≠ 0 := by
  cases mode with
  | initial current =>
      dsimp only [tailMatrix, Matrix2.identityMatrix, Matrix2.Matrix2.determinant]
      rw [Basic.mul_one, Basic.zero_mul, Basic.sub_zero]
      decide
  | low current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.scale,
        Matrix2.Matrix2.determinant,
        Basic.mul_one,
        Basic.zero_mul,
        Basic.sub_zero]
      exact Field.inv_ne_zero_direct
        (Power.natPow_ne_zero_direct Basic.Canonical.gamma
          (by decide) current.count)
  | loop current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.scale,
        Matrix2.Matrix2.determinant,
        Basic.mul_one,
        Basic.zero_mul,
        Basic.sub_zero]
      exact Power.natPow_ne_zero_direct Basic.Canonical.gamma
        (by decide) current.count
  | residual current =>
      simp only [Cursor.Image.Mode.tailMatrix, Line.Matrix.invert,
        Matrix2.Matrix2.determinant,
        Basic.zero_mul,
        Basic.one_mul]
      exact Field.neg_ne_zero_direct
        (show Basic.Canonical.gamma ≠ 0 by decide)

end

open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Refining a mode leaves its exact tail matrix unchanged. -/
@[simp] theorem refine_tailMatrix
    (mode : Transducer.Mode) (target : Fraction.Rational) (positive : 0 < target) :
    Cursor.Image.Mode.tailMatrix (Cursor.Refinement.Mode.refine mode target positive) = Cursor.Image.Mode.tailMatrix
      mode := by
  cases mode <;> rfl

end Mode

namespace Machine

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiply the committed parser matrix by the exact retained mode tail matrix. -/
@[expose] def imageMatrix (machine : Transducer.Machine) :
  LinearAlgebra.Coordinates2.Matrix.GaussianMatrix :=
  Matrix2.mul
    (Parser.State.parse
      (Transducer.Machine.committed
        machine)).matrix
    (Cursor.Image.Mode.tailMatrix machine.mode)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Apply the exact committed parser matrix to the retained mode's parser tail at the supplied value. -/
@[expose] def image (machine : Transducer.Machine) (value : Basic.Canonical) :
  Line.GaussianLine :=
  Line.Matrix.act
    (Parser.State.parse
      (Transducer.Machine.committed
        machine)).matrix
    (Purelib.Data.CCL.Transducer.Mode.Semantics.SemanticMode.parserTail machine.mode value)

open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The retained machine image equals its combined image-matrix action on the value's affine point. -/
theorem image_eq_act_imageMatrix (machine : Transducer.Machine) (value : Basic.Canonical)
  :
    Cursor.Image.Machine.image machine value =
      Line.Matrix.act (Cursor.Image.Machine.imageMatrix machine) (Line.Proj.affine value) := by
  rw [Cursor.Image.Machine.image, Cursor.Image.Machine.imageMatrix, Line.Matrix.act_mul,
    Cursor.Image.Mode.tailMatrix_act]

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The exact combined image matrix of every retained machine has nonzero determinant. -/
theorem imageMatrix_det_ne (machine : Transducer.Machine) :
    Matrix2.Matrix2.determinant (Cursor.Image.Machine.imageMatrix machine) ≠ 0 := by
  rw [Cursor.Image.Machine.imageMatrix, Matrix2.det_mul]
  exact Field.mul_ne_zero_direct
    (Parser.State.parse_det_ne
      (Transducer.Machine.committed machine))
    (Cursor.Image.Mode.tailMatrix_det_ne machine.mode)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Refining a machine leaves its exact combined image matrix unchanged. -/
@[simp] theorem refine_imageMatrix
    (machine : Transducer.Machine) (target : Fraction.Rational) (positive : 0 < target) :
    Cursor.Image.Machine.imageMatrix (Cursor.Refinement.Machine.refine machine target positive) =
      (Cursor.Image.Machine.imageMatrix machine) := by
  change Matrix2.mul
      (Parser.State.parse
        (Transducer.Machine.committed
          machine)).matrix
      (Cursor.Image.Mode.tailMatrix (Cursor.Refinement.Mode.refine machine.mode target positive)) =
    Matrix2.mul
      (Parser.State.parse
        (Transducer.Machine.committed
          machine)).matrix
      (Cursor.Image.Mode.tailMatrix machine.mode)
  rw [Cursor.Image.Mode.refine_tailMatrix]
end Machine

end Purelib.Data.CCL.Progressive.Cursor.Image

end
