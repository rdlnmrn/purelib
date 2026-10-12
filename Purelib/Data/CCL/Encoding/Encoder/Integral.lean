module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Integral
import Purelib.Data.CCL.Encoding.Encoder.Annulus
public import Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Normalization
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Projective
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Projective.GaussianInt.Embedding
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Power
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Tactic.Ring

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
set_option genInjectivity false in
/-- Retain a finite bit word and integral matrix with exact projective reconstruction of the displayed source fraction.

The reconstruction witness belongs to the stored matrix acting on infinity and the original numerator-denominator pair.
The word and matrix remain the exact outputs of the retained encoder. -/
structure CompleteEncoding (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) where
  /-- The exact finite bit word returned by this encoding. -/ word : BinaryPrefix.Basic.SourceEncodingEncoderWordAlias
  /-- The retained integral matrix associated with the encoding. -/ matrix :
    Matrix2.SourceEncodingEncoderIntegralMat2Alias
  /-- The retained matrix sends infinity to a point equivalent to the original displayed fraction pair. -/ reconstruct :
    Line.Proj.Equivalent
      (Line.Matrix.act matrix (Line.Proj.omega : Line.Basic.SourceEncodingEncoderIntegralProjAlias))
      ⟨fraction.numerator, fraction.denominator⟩

constructive_injectivity CompleteEncoding
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
set_option genInjectivity false in
/-- Retain an annulus bit word and integral matrix reconstructing the original displayed annulus pair.

The matrix action on infinity is projectively equivalent to the exact stored annulus numerator and denominator,
preserving their integer representation. -/
structure TailEncoding (annulus : Annulus) where
  /-- The exact finite bit word returned by this encoding. -/ word : BinaryPrefix.Basic.SourceEncodingEncoderWordAlias
  /-- The retained integral matrix associated with the encoding. -/ matrix :
    Matrix2.SourceEncodingEncoderIntegralMat2Alias
  /-- The retained matrix sends infinity to a point equivalent to the original displayed fraction pair. -/ reconstruct :
    Line.Proj.Equivalent
      (Line.Matrix.act matrix (Line.Proj.omega : Line.Basic.SourceEncodingEncoderIntegralProjAlias))
      ⟨annulus.frac.numerator, annulus.frac.denominator⟩

constructive_injectivity TailEncoding
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Compute an annulus encoding with an integral reconstruction matrix and the exact certified continuation word.

The matrix and reconstruction witness come from the original well-founded recursion on denominator norm. The returned
word uses the selected sector code followed by the separately computed annulus block continuation; terminal residuals
and nonterminal normalizations retain their original branches. -/
@[expose] def encodeTail (annulus : Annulus) : Encoder.Integral.TailEncoding annulus :=
  let core := coreHere annulus
  { word := (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value).code ++
      Block.Basic.rawWord (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation
    matrix := core.matrix
    reconstruct := core.reconstruct }
where
  coreHere (current : Annulus) : Encoder.Integral.TailEncoding current :=
    let sector := ComplexContinuedFraction.Encoding.Sector.select current.frac.value
    let residual := current.frac.numerator - Sector.Integral.sectorInt sector * current.frac.denominator
    if residualZero : residual = 0 then
      ⟨sector.code, Block.Integral.sectorMatrixInt sector, by
        have numeratorIdentity :
            current.frac.numerator = Sector.Integral.sectorInt sector * current.frac.denominator :=
          by
            apply GaussianInt.ext
            · have coordinate := congrArg GaussianInt.re residualZero
              change _ - _ = (0 : Int) at coordinate
              omega0
            · have coordinate := congrArg GaussianInt.im residualZero
              change _ - _ = (0 : Int) at coordinate
              omega0
        rw [numeratorIdentity]
        dsimp only [Line.Proj.Equivalent,
          Block.Integral.sectorMatrixInt, Line.Matrix.act,
          Matrix2.mul,
          Line.Matrix.translate,
          Line.Matrix.invert,
          Line.Proj.omega]
        ring1⟩
    else
      let post := Encoder.Annulus.postInversion current (by
        simpa only [residual, sector] using residualZero)
      let normalized := Encoder.Annulus.normalizeLoop post.frac (GaussianInt.normNat current.frac.denominator)
        post.den_descent rfl
      let tail := coreHere normalized.annulus
      let factor := Matrix2.mul (Block.Integral.sectorMatrixInt sector)
        (Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt normalized.exponent))
      let matrix := Matrix2.mul factor tail.matrix
      ⟨sector.code ++ List.replicate normalized.exponent true ++
          [false] ++ tail.word,
        matrix, by
          dsimp only [matrix]
          rw [Line.Matrix.act_mul]
          have acted := Line.Matrix.act_respects_equivalent
            factor tail.reconstruct
          have stepReconstruct :
              Line.Proj.Equivalent
                (Line.Matrix.act factor
                  ⟨normalized.annulus.frac.numerator,
                    normalized.annulus.frac.denominator⟩)
                ⟨current.frac.numerator, current.frac.denominator⟩ := by
            rw [normalized.num_eq, normalized.den_eq, post.num_eq, post.den_eq]
            dsimp only [factor, Line.Proj.Equivalent,
              Block.Integral.sectorMatrixInt, Line.Matrix.act,
              Matrix2.mul,
              Line.Matrix.translate,
              Line.Matrix.invert,
              Line.Matrix.scale]
            rw [GaussianInt.sub_eq_add_neg]
            ring1
          have stepDenNonzero :
              (Line.Matrix.act factor
                ⟨normalized.annulus.frac.numerator,
                  normalized.annulus.frac.denominator⟩).q ≠ 0 := by
            rw [normalized.num_eq, normalized.den_eq, post.num_eq]
            dsimp only [factor, Block.Integral.sectorMatrixInt,
              Line.Matrix.act,
              Matrix2.mul,
              Line.Matrix.translate,
              Line.Matrix.invert,
              Line.Matrix.scale]
            simpa only [GaussianInt.zero_add, GaussianInt.one_mul,
              GaussianInt.mul_zero, GaussianInt.add_zero,
              GaussianInt.zero_mul] using
              GaussianInt.mul_ne_zero
                (GaussianInt.mul_ne_zero (show GaussianInt.gammaInt ≠ 0 by decide)
                  (GaussianInt.natPow_ne_zero GaussianInt.gammaInt (by decide) normalized.exponent))
                current.frac.denominatorNonzero
          exact GaussianInt.equivalent_trans_of_mid_q acted
            stepReconstruct stepDenNonzero⟩
  termination_by GaussianInt.normNat current.frac.denominator
  decreasing_by
    all_goals
      change GaussianInt.normNat normalized.annulus.frac.denominator < GaussianInt.normNat current.frac.denominator
      exact normalized.measure_lt
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Compute the integral word and reconstruction matrix for a displayed fraction with nonzero numerator.

The exact norm comparison selects high or low normalization. Retain the selected initial header and radial matrix, then
compose with the annulus tail matrix and its original reconstruction witness. -/
@[expose] def encodeResult (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero :
  fraction.numerator ≠ 0) :
    Encoder.Integral.CompleteEncoding fraction :=
  let finishHere : {current : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias} →
    Encoder.Normalization.InitialResult current →
      Encoder.Integral.CompleteEncoding current := fun {current} initial =>
    let tail := Encoder.Integral.encodeTail initial.annulus
    let matrix := Matrix2.mul initial.radial tail.matrix
    ⟨initial.header ++ tail.word, matrix, by
      dsimp only [matrix]
      rw [Line.Matrix.act_mul]
      have acted := Line.Matrix.act_respects_equivalent
        initial.radial tail.reconstruct
      exact GaussianInt.equivalent_trans_of_mid_q acted
        initial.radial_reconstruct initial.radial_den_ne⟩
  if highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator then
    finishHere (Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch)
  else
    finishHere (Encoder.Normalization.initialLow fraction numeratorNonzero
      (Nat.lt_of_not_ge highBranch))
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
/-- Read the exact finite bit word computed for a displayed fraction with nonzero numerator. -/
@[expose] def encode (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero :
  fraction.numerator ≠ 0) : BinaryPrefix.Basic.SourceEncodingEncoderWordAlias :=
  (Encoder.Integral.encodeResult fraction numeratorNonzero).word
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The annulus word is its selected sector code followed by the raw word of its retained block continuation.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
theorem encodeTail_word_eq (annulus : Annulus) :
    (Encoder.Integral.encodeTail annulus).word =
      (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value).code ++
        Block.Basic.rawWord (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation := rfl
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The embedded integral encoding matrix sends infinity to a point equivalent to the original fraction's affine value.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
theorem encode_reconstruct (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    Line.Proj.Equivalent
      (Line.Matrix.act (GaussianInt.Embedding.mapMat (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix)
        (Line.Proj.omega : Line.Basic.SourceEncodingEncoderProjAlias))
      (Line.Proj.affine fraction.value) := by
  have mapped := GaussianInt.Embedding.mapProj_equivalent
    (Encoder.Integral.encodeResult fraction numeratorNonzero).reconstruct
  rw [GaussianInt.Embedding.mapProj_act, GaussianInt.Embedding.mapProj_omega] at mapped
  dsimp only [Line.Proj.Equivalent, GaussianInt.Embedding.mapProj, Line.Proj.affine] at mapped ⊢
  rw [Basic.mul_one]
  apply Field.mul_right_cancel_of_ne
    fraction.denominatorGaussianNonzero
  calc
    (Line.Matrix.act (GaussianInt.Embedding.mapMat (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix)
        (Line.Proj.omega : Line.Basic.SourceEncodingEncoderProjAlias)).p * GaussianInt.toGaussian fraction.denominator =
        GaussianInt.toGaussian fraction.numerator *
          (Line.Matrix.act
            (GaussianInt.Embedding.mapMat (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix)
            (Line.Proj.omega : Line.Basic.SourceEncodingEncoderProjAlias)).q := mapped
    _ = (fraction.value * GaussianInt.toGaussian fraction.denominator) *
        (Line.Matrix.act
          (GaussianInt.Embedding.mapMat (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix)
          (Line.Proj.omega : Line.Basic.SourceEncodingEncoderProjAlias)).q := by rw [fraction.value_mul_denominator]
    _ = (fraction.value *
        (Line.Matrix.act
          (GaussianInt.Embedding.mapMat (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix)
          (Line.Proj.omega : Line.Basic.SourceEncodingEncoderProjAlias)).q) * GaussianInt.toGaussian
            fraction.denominator := by
      ring1
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- The integral encoding matrix sends infinity to a point equivalent to the original displayed numerator-denominator
pair.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
theorem encode_reconstruct_pair (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Encoder.Integral.encodeResult fraction numeratorNonzero).matrix
        (Line.Proj.omega : Line.Basic.SourceEncodingEncoderIntegralProjAlias))
      ⟨fraction.numerator, fraction.denominator⟩ :=
  (Encoder.Integral.encodeResult fraction numeratorNonzero).reconstruct
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Complete a retained initial normalization by composing its header and radial matrix with the exact annulus tail
encoding. -/
private def finishInitial {fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias}
    (initial : Encoder.Normalization.InitialResult fraction) : Encoder.Integral.CompleteEncoding fraction :=
  let tail := Encoder.Integral.encodeTail initial.annulus
  let matrix := Matrix2.mul initial.radial tail.matrix
  ⟨initial.header ++ tail.word, matrix, by
    dsimp only [matrix]
    rw [Line.Matrix.act_mul]
    have acted := Line.Matrix.act_respects_equivalent
      initial.radial tail.reconstruct
    exact GaussianInt.equivalent_trans_of_mid_q acted
      initial.radial_reconstruct initial.radial_den_ne⟩
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The normalized annulus denominator is nonzero after the retained sector-and-scale matrix action.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
private theorem normalized_step_den_ne (annulus : Annulus)
    (post : Encoder.Annulus.PostInversion annulus)
    (normalized : Encoder.Annulus.LoopResult post.frac (GaussianInt.normNat annulus.frac.denominator)) :
    (Line.Matrix.act
      (Matrix2.mul
        (Block.Integral.sectorMatrixInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value))
        (Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt normalized.exponent)))
      ⟨normalized.annulus.frac.numerator, normalized.annulus.frac.denominator⟩).q ≠ 0 := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq]
  dsimp only [Block.Integral.sectorMatrixInt, Line.Matrix.act, Matrix2.mul,
    Line.Matrix.translate, Line.Matrix.invert, Line.Matrix.scale]
  simpa only [GaussianInt.zero_add, GaussianInt.one_mul, GaussianInt.mul_zero, GaussianInt.add_zero,
    GaussianInt.zero_mul] using
    GaussianInt.mul_ne_zero
      (GaussianInt.mul_ne_zero (show GaussianInt.gammaInt ≠ 0 by decide)
        (GaussianInt.natPow_ne_zero GaussianInt.gammaInt (by decide) normalized.exponent))
      annulus.frac.denominatorNonzero
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- The retained sector-and-scale matrix reconstructs the original annulus pair from the exact loop-normalized pair.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
private theorem normalized_step_reconstruct (annulus : Annulus)
    (post : Encoder.Annulus.PostInversion annulus)
    (normalized : Encoder.Annulus.LoopResult post.frac (GaussianInt.normNat annulus.frac.denominator)) :
    Line.Proj.Equivalent
      (Line.Matrix.act
        (Matrix2.mul
          (Block.Integral.sectorMatrixInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value))
          (Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt normalized.exponent)))
        ⟨normalized.annulus.frac.numerator, normalized.annulus.frac.denominator⟩)
      ⟨annulus.frac.numerator, annulus.frac.denominator⟩ := by
  rw [normalized.num_eq, normalized.den_eq, post.num_eq, post.den_eq]
  dsimp only [Line.Proj.Equivalent, Block.Integral.sectorMatrixInt, Line.Matrix.act,
    Matrix2.mul, Line.Matrix.translate, Line.Matrix.invert, Line.Matrix.scale]
  rw [GaussianInt.sub_eq_add_neg]
  ring1
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- At zero selected residual, the retained integral sector matrix sends infinity to the original annulus pair.

The displayed fraction, selected annulus and retained integral matrix remain fixed. The claim transports their explicit
coordinate identities and reconstruction evidence. -/
private theorem terminal_reconstruct (annulus : Annulus) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias)
    (residualZero :
      annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator = 0) :
    Line.Proj.Equivalent
      (Line.Matrix.act (Block.Integral.sectorMatrixInt sector)
        (Line.Proj.omega : Line.Basic.SourceEncodingEncoderIntegralProjAlias))
      ⟨annulus.frac.numerator, annulus.frac.denominator⟩ := by
  have numeratorIdentity :
      annulus.frac.numerator = Sector.Integral.sectorInt sector * annulus.frac.denominator :=
    by
      apply GaussianInt.ext
      · have coordinate := congrArg GaussianInt.re residualZero
        change _ - _ = (0 : Int) at coordinate
        omega0
      · have coordinate := congrArg GaussianInt.im residualZero
        change _ - _ = (0 : Int) at coordinate
        omega0
  rw [numeratorIdentity]
  dsimp only [Line.Proj.Equivalent, Block.Integral.sectorMatrixInt, Line.Matrix.act,
    Matrix2.mul, Line.Matrix.translate, Line.Matrix.invert, Line.Proj.omega]
  ring1
end Purelib.Data.CCL.Encoding.Encoder.Integral

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Compute the integral annulus encoding by strict denominator-norm descent using retained reconstruction helpers.

A zero selected residual returns its sector code and sector matrix. Otherwise retain the post-inversion fraction, loop
normalization and recursive tail, then compose the exact word and matrices with the original projective reconstruction
witness. -/
private def encodeTailCore (annulus : Annulus) : Encoder.Integral.TailEncoding annulus :=
  let sector := ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value
  let residual :=
    annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator
  if residualZero : residual = 0 then
    ⟨sector.code, Block.Integral.sectorMatrixInt sector,
      Encoder.Integral.terminal_reconstruct annulus sector (by
        simpa only [residual, sector] using residualZero)⟩
  else
    let post := Encoder.Annulus.postInversion annulus (by
      simpa only [residual, sector] using residualZero)
    let normalized := Encoder.Annulus.normalizeLoop post.frac (GaussianInt.normNat annulus.frac.denominator)
      post.den_descent rfl
    let tail := Purelib.Data.CCL.Encoding.Encoder.Integral.encodeTailCore normalized.annulus
    let factor := Matrix2.mul (Block.Integral.sectorMatrixInt sector)
      (Line.Matrix.scale (GaussianInt.natPow GaussianInt.gammaInt normalized.exponent))
    let matrix := Matrix2.mul factor tail.matrix
    ⟨sector.code ++ List.replicate normalized.exponent true ++
        [false] ++ tail.word,
      matrix, by
        dsimp only [matrix]
        rw [Line.Matrix.act_mul]
        have acted := Line.Matrix.act_respects_equivalent factor tail.reconstruct
        exact GaussianInt.equivalent_trans_of_mid_q acted
          (Encoder.Integral.normalized_step_reconstruct annulus post normalized)
          (Encoder.Integral.normalized_step_den_ne annulus post normalized)⟩
termination_by GaussianInt.normNat annulus.frac.denominator
decreasing_by exact normalized.measure_lt
end Purelib.Data.CCL.Encoding.Encoder.Integral

end
