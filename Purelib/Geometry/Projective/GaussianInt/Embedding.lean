module

public import Purelib.Data.GaussianInt.Embedding
public import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.Line.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Projective embedding of Gaussian integers

The original rational embedding acts coordinatewise on matrices and projective
pairs. Its addition and multiplication laws preserve matrix action and
cross-multiplication equivalence.
-/

namespace Purelib.Geometry.Projective.GaussianInt.Embedding

open Purelib
open Purelib.Data
open Purelib.Geometry.Projective
open Purelib.Geometry.Projective.Line
open Purelib.LinearAlgebra

public section

/-- Coordinatewise embedding of an integral decoder matrix.

The four original matrix entries are embedded independently in their retained
positions, with no change to the source matrix or scalar selection. -/
@[expose] def mapMat (matrix : Coordinates2.Matrix.SourceCCFEncoderIntegralMat2Alias) :
  Coordinates2.Matrix.SourceCCFEncoderMat2Alias :=
  ⟨GaussianInt.toGaussian matrix.a, GaussianInt.toGaussian matrix.b,
    GaussianInt.toGaussian matrix.c, GaussianInt.toGaussian matrix.d⟩

/-- Coordinatewise embedding of an integral projective pair.

The original numerator and denominator occupy the same homogeneous positions
in the rational Gaussian pair. -/
@[expose] def mapProj (point : Line.Basic.SourceCCFEncoderIntegralProjAlias) : Line.Basic.SourceCCFEncoderProjAlias :=
  ⟨GaussianInt.toGaussian point.p, GaussianInt.toGaussian point.q⟩

/-- Embedding Gaussian integer coordinates commutes with matrix action.

Addition and multiplication are transported in each retained homogeneous
coordinate separately, with the original matrix and pair unchanged. -/
@[simp] theorem mapProj_act (matrix : Coordinates2.Matrix.SourceCCFEncoderIntegralMat2Alias) (point :
  Line.Basic.SourceCCFEncoderIntegralProjAlias) :
    mapProj (Line.Matrix.act matrix point) =
      Line.Matrix.act (mapMat matrix) (mapProj point) := by
  apply Proj.ext
  · change GaussianInt.toGaussian (matrix.a * point.p + matrix.b * point.q) =
      GaussianInt.toGaussian matrix.a * GaussianInt.toGaussian point.p +
        GaussianInt.toGaussian matrix.b * GaussianInt.toGaussian point.q
    rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul,
      GaussianInt.toGaussian_mul]
    exact Eq.refl _
  · change GaussianInt.toGaussian (matrix.c * point.p + matrix.d * point.q) =
      GaussianInt.toGaussian matrix.c * GaussianInt.toGaussian point.p +
        GaussianInt.toGaussian matrix.d * GaussianInt.toGaussian point.q
    rewrite [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul,
      GaussianInt.toGaussian_mul]
    exact Eq.refl _

/-- Coordinatewise embedding preserves homogeneous cross-multiplication equivalence.

The original cross-product equality is carried by the injective scalar embedding,
whose multiplication law retains both homogeneous coordinate owners. -/
theorem mapProj_equivalent {left right : Line.Basic.SourceCCFEncoderIntegralProjAlias}
    (equivalent : Proj.Equivalent left right) :
    Proj.Equivalent (mapProj left) (mapProj right) := by
  dsimp only [Proj.Equivalent, mapProj] at equivalent ⊢
  simpa only [GaussianInt.toGaussian_mul] using congrArg GaussianInt.toGaussian equivalent

/-- Embedding the integral pole gives the Gaussian rational pole. -/
@[simp] theorem mapProj_omega :
    mapProj (Proj.omega : Line.Basic.SourceCCFEncoderIntegralProjAlias) =
      (Proj.omega : Line.Basic.SourceCCFEncoderProjAlias) := rfl

end

end Purelib.Geometry.Projective.GaussianInt.Embedding
