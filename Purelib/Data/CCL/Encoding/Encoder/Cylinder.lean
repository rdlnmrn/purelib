module
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Syntax
import Purelib.Data.List.Append
import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.CCL.Encoding.Encoder.Normalization
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian

import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Geometry.Projective.SectorBlock.Tail.Projective
import Purelib.Data.Gaussian.Constants
import Purelib.Data.GaussianInt.Power
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Encoding.Block.Integral
import Purelib.Data.GaussianInt.Constants
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Encoder.Annulus
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Power
import Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Cylinder

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Equal retained block encodings bound the source values' squared chordal distance by one half to their common block
count.

Both displayed fractions have nonzero numerators. The estimate uses their separately retained points, realizations and
reconstruction witnesses before transporting to the original affine values. -/
theorem chordalSq_le_of_encodeBlocks_eq (left right : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (leftNumeratorNonzero : left.numerator ≠ 0)
    (rightNumeratorNonzero : right.numerator ≠ 0)
    (blocksEqual :
      (Encoder.Blocks.encodeBlocks left leftNumeratorNonzero).blocks =
        (Encoder.Blocks.encodeBlocks right rightNumeratorNonzero).blocks) :
    Chordal.Basic.chordalSq
        (Line.Proj.affine left.value) (Line.Proj.affine right.value) ≤
      (1 / 2 : Fraction.Basic.Rational) ^
        (Encoder.Blocks.encodeBlocks left leftNumeratorNonzero).blocks.length := by
  let leftEncoding := Encoder.Blocks.encodeBlocks left leftNumeratorNonzero
  let rightEncoding := Encoder.Blocks.encodeBlocks right rightNumeratorNonzero
  have rightRealizes : Cylinder.Projective.SourceEncodingEncoderProjectiveRealizesAlias leftEncoding.blocks
      rightEncoding.point := by
    rw [blocksEqual]
    exact rightEncoding.realizes
  have encodedBound :
      Chordal.Basic.chordalSq
          leftEncoding.point rightEncoding.point ≤
        (1 / 2 : Fraction.Basic.Rational) ^ leftEncoding.blocks.length :=
    Cylinder.Projective.ProjectiveRealizes.chordalSq_le_half_pow
      leftEncoding.realizes rightRealizes
  calc
    Chordal.Basic.chordalSq
        (Line.Proj.affine left.value) (Line.Proj.affine right.value) =
        Chordal.Basic.chordalSq
          leftEncoding.point (Line.Proj.affine right.value) :=
      (Chordal.Equivalence.chordalSq_eq_of_equivalent_left
        leftEncoding.realizes.valid
        (Line.Gaussian.Proj.affine_hasNonzeroCoordinate left.value)
        leftEncoding.reconstruct (Line.Proj.affine right.value)).symm
    _ = Chordal.Basic.chordalSq
        leftEncoding.point rightEncoding.point :=
      (Chordal.Equivalence.chordalSq_eq_of_equivalent_right
        rightEncoding.realizes.valid
        (Line.Gaussian.Proj.affine_hasNonzeroCoordinate right.value)
        rightEncoding.reconstruct leftEncoding.point).symm
    _ ≤ (1 / 2 : Fraction.Basic.Rational) ^ leftEncoding.blocks.length := encodedBound

end Purelib.Data.CCL.Encoding.Encoder.Cylinder

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Cylinder

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
/-- The integral bit encoder word equals the raw word of its completed blocks.

The high or low normalization branch retains the same header, selected sector
and annulus continuation on both sides of this equality. -/
theorem encode_eq_rawWord (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    Encoder.Integral.encode fraction numeratorNonzero =
      Block.Basic.rawWord (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks := by
  rw [Encoder.Integral.encode, Encoder.Integral.encodeResult, Encoder.Blocks.encodeBlocks]
  split
  · rename_i highBranch
    dsimp only
    rw [Encoder.Integral.encodeTail_word_eq]
    dsimp only [Encoder.Normalization.initialHigh]
    rw [Block.Basic.rawWord_cons]
    dsimp only [Block.word, Block.Syntax.regularWord]
    repeat first
      | rw [List.cons_append]
      | rw [List.nil_append]
      | rw [List.Append.append_assoc]
  · rename_i highBranch
    dsimp only
    rw [Encoder.Integral.encodeTail_word_eq]
    dsimp only [Encoder.Normalization.initialLow]
    rw [Block.Basic.rawWord_cons]
    dsimp only [Block.word, Block.Syntax.lowWord, Block.Syntax.regularWord]
    repeat first
      | rw [List.cons_append]
      | rw [List.nil_append]
      | rw [List.Append.append_assoc]
end Purelib.Data.CCL.Encoding.Encoder.Cylinder

end
