module
public import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.GaussianInt.Embedding
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Constants
import Purelib.Data.Gaussian.Power
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Power
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the integral diagonal initial-low scale matrix using the retained gamma exponent. -/
def lowScaleInt (exponent : Nat) :
  Matrix2.SourceCCFEncoderIntegralMat2Alias :=
  ⟨1, 0, 0, GaussianInt.natPow GaussianInt.gammaInt exponent⟩
end Purelib.Data.CCL.Encoding.Block.Integral

end

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Multiply integral sector translation by the integer-gamma inversion matrix. -/
def sectorMatrixInt (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias) : Matrix2.SourceCCFEncoderIntegralMat2Alias :=
  Matrix2.mul (Line.Matrix.translate (Sector.Integral.sectorInt sector))
    (Line.Matrix.invert GaussianInt.gammaInt)
end Purelib.Data.CCL.Encoding.Block.Integral

end

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the initial-low integral block matrix from its exact scale and sector matrices. -/
def lowBlockInt (exponent : Nat) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias) : Matrix2.SourceCCFEncoderIntegralMat2Alias :=
  Matrix2.mul (lowScaleInt exponent) (sectorMatrixInt sector)
end Purelib.Data.CCL.Encoding.Block.Integral

end

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Embedding the integral initial-low block matrix recovers its canonical Gaussian block matrix. -/
theorem map_lowBlockInt (exponent : Nat) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias) :
    GaussianInt.Embedding.mapMat (lowBlockInt exponent sector) =
      Block.Matrix.lowBlock exponent sector := by
  apply Matrix2.ext <;>
    simp only [GaussianInt.Embedding.mapMat, lowBlockInt, lowScaleInt,
      sectorMatrixInt,
      Block.Matrix.lowBlock, Matrix2.mul,
      Line.Matrix.translate, Line.Matrix.invert, GaussianInt.toGaussian_add,
      GaussianInt.toGaussian_mul, GaussianInt.toGaussian_zero, GaussianInt.toGaussian_one,
      GaussianInt.toGaussian_gammaInt_pow, GaussianInt.toGaussian_gammaInt,
      Sector.Integral.toGaussian_sectorInt,
      Power.natPow_succ] <;>
    ring1
end Purelib.Data.CCL.Encoding.Block.Integral

end

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the regular integral block matrix from gamma-power scaling and the retained sector matrix. -/
def regularBlockInt (exponent : Nat) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias) : Matrix2.SourceCCFEncoderIntegralMat2Alias :=
  Matrix2.mul (Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt exponent))
    (sectorMatrixInt sector)
end Purelib.Data.CCL.Encoding.Block.Integral

end

section
@[expose] public section
namespace Purelib.Data.CCL.Encoding.Block.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Embedding the integral regular block matrix recovers its canonical Gaussian block matrix. -/
theorem map_regularBlockInt (exponent : Nat) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias) :
    GaussianInt.Embedding.mapMat (regularBlockInt exponent sector) =
      Block.Matrix.regularBlock exponent sector := by
  apply Matrix2.ext <;>
    simp only [GaussianInt.Embedding.mapMat, regularBlockInt, sectorMatrixInt,
      Block.Matrix.regularBlock, Matrix2.mul, Line.Matrix.scale,
      Line.Matrix.translate, Line.Matrix.invert, GaussianInt.toGaussian_add,
      GaussianInt.toGaussian_mul, GaussianInt.toGaussian_zero, GaussianInt.toGaussian_one,
      GaussianInt.toGaussian_gammaInt_pow, GaussianInt.toGaussian_gammaInt,
      Sector.Integral.toGaussian_sectorInt,
      Power.natPow_succ] <;>
    ring1
end Purelib.Data.CCL.Encoding.Block.Integral

end
