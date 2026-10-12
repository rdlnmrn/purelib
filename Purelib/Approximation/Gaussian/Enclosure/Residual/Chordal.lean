module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Enclosure.Residual.Projective
public import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.DyadicTail
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Geometry.Projective.Chordal.Triangle
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Matrix.Gaussian
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Residual

open Purelib.Data.CCL.Encoding.Padding

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Matrix

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Residual.Chordal

/-- Pairwise transported diameter of a small residual chart. This is the productive exact-result case: even if no later
sector ever occurs, increasing unary padding count drives the explicit rational bound to zero. -/
theorem residualSmall_pair_chordalSq_act_le
    (count : Nat) (ball : Approximation.Gaussian.Enclosure.Ball)
    (small : Residual.SmallBall ball
      (Residual.paddingTarget count))
    (matrix : GaussianMatrix)
    (determinantNonzero :
      BoundaryAdjugate.determinant matrix ≠ 0)
    {left right : Canonical}
    (leftInside : ball.Contains left) (rightInside : ball.Contains right) :
    Chordal.Basic.chordalSq
        (Line.Matrix.act matrix ⟨1, Canonical.gamma * left⟩)
        (Line.Matrix.act matrix ⟨1, Canonical.gamma * right⟩) ≤
      4 * (Transport.terminalCoefficient matrix /
        (1 + (2 : Fraction.Rational) ^ count)) := by
  let leftTail := Residual.loopTailOfSmall
    small left leftInside
  let rightTail := Residual.loopTailOfSmall
    small right rightInside
  let leftHomogeneous : GaussianLine := ⟨1, Canonical.gamma * left⟩
  let rightHomogeneous : GaussianLine := ⟨1, Canonical.gamma * right⟩
  let omegaImage := Line.Matrix.act matrix (Proj.omega : GaussianLine)
  let bound := Transport.terminalCoefficient matrix /
    (1 + (2 : Fraction.Rational) ^ count)
  have leftEquivalent : leftTail.point.Equivalent leftHomogeneous :=
    Projective.loopTailOfSmall_point_equivalent_homogeneous small left leftInside
  have rightEquivalent : rightTail.point.Equivalent rightHomogeneous :=
    Projective.loopTailOfSmall_point_equivalent_homogeneous small right rightInside
  have leftTailValid := leftTail.valid
  have rightTailValid := rightTail.valid
  have leftHomogeneousValid :
      Proj.HasNonzeroCoordinate leftHomogeneous := by
    change (1 : Canonical) ≠ 0 ∨ _
    exact Or.inl one_ne_zero
  have rightHomogeneousValid :
      Proj.HasNonzeroCoordinate rightHomogeneous := by
    change (1 : Canonical) ≠ 0 ∨ _
    exact Or.inl one_ne_zero
  have omegaValid := Proj.omega_hasNonzeroCoordinate
  have leftTailImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftTailValid
  have rightTailImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightTailValid
  have leftImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftHomogeneousValid
  have rightImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightHomogeneousValid
  have omegaImageValid :=
    Gaussian.Mat2.act_hasNonzeroCoordinate
      determinantNonzero omegaValid
  have leftImageEquivalent :=
    Line.Matrix.act_respects_equivalent matrix leftEquivalent
  have rightImageEquivalent :=
    Line.Matrix.act_respects_equivalent matrix rightEquivalent
  have leftDistance :
      Chordal.Basic.chordalSq
          (Line.Matrix.act matrix leftHomogeneous) omegaImage ≤ bound := by
    calc
      Chordal.Basic.chordalSq
          (Line.Matrix.act matrix leftHomogeneous) omegaImage =
          Chordal.Basic.chordalSq
            (Line.Matrix.act matrix leftTail.point) omegaImage :=
        (Equivalence.chordalSq_eq_of_equivalent_left
          leftTailImageValid leftImageValid leftImageEquivalent omegaImage).symm
      _ ≤ bound :=
        DyadicTail.chordalSq_act_loopTail_le
          matrix determinantNonzero leftTail
  have rightDistance :
      Chordal.Basic.chordalSq omegaImage
          (Line.Matrix.act matrix rightHomogeneous) ≤ bound := by
    calc
      Chordal.Basic.chordalSq omegaImage
          (Line.Matrix.act matrix rightHomogeneous) =
          Chordal.Basic.chordalSq
            (Line.Matrix.act matrix rightHomogeneous) omegaImage :=
        Chordal.Basic.chordalSq_comm _ _
      _ = Chordal.Basic.chordalSq
          (Line.Matrix.act matrix rightTail.point) omegaImage :=
        (Equivalence.chordalSq_eq_of_equivalent_left
          rightTailImageValid rightImageValid rightImageEquivalent
            omegaImage).symm
      _ ≤ bound :=
        DyadicTail.chordalSq_act_loopTail_le
          matrix determinantNonzero rightTail
  calc
    Chordal.Basic.chordalSq
        (Line.Matrix.act matrix leftHomogeneous)
        (Line.Matrix.act matrix rightHomogeneous) ≤
        2 * (Chordal.Basic.chordalSq
              (Line.Matrix.act matrix leftHomogeneous) omegaImage +
            Chordal.Basic.chordalSq omegaImage
              (Line.Matrix.act matrix rightHomogeneous)) :=
      Triangle.chordalSq_triangle_two
        leftImageValid omegaImageValid rightImageValid
    _ ≤ 2 * (bound + bound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftDistance rightDistance) (by decide)
    _ = 4 * (Transport.terminalCoefficient matrix /
        (1 + (2 : Fraction.Rational) ^ count)) := by
      dsimp only [bound]
      ring1
end Purelib.Approximation.Gaussian.Enclosure.Residual.Chordal

end
