module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Block.Semantics
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.CCL.Encoding.Encoder.Annulus
public import Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks
public import Purelib.Data.CCL.Encoding.Encoder.Normalization
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import all Purelib.Data.GaussianInt.Fraction.Scale

import Purelib.Data.Nat.BinaryNormalization
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix

import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Power
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Basic
import Purelib.Geometry.Projective.SectorBlock.Tail.Projective
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a finite block list, its realized projective point and exact source reconstruction.

The projective realization belongs to the same stored blocks and point. Reconstruction relates that point to the affine
value of the original displayed fraction. -/
structure BlockEncoding (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) where
  /-- The retained finite encoded block list. -/ blocks : List Block.Basic.SourceEncodingEncoderBlockAlias
  /-- The retained projective point represented by these exact blocks. -/ point :
    Line.Basic.SourceEncodingEncoderProjAlias
  /-- The exact block list realizes the retained point. -/ realizes :
    Cylinder.Projective.SourceEncodingEncoderProjectiveRealizesAlias blocks point
  /-- The retained point is equivalent to the original source fraction's affine value. -/ reconstruct : point.Equivalent
    (Line.Proj.affine fraction.value)

constructive_injectivity BlockEncoding

end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data.CCL.Encoding in
set_option genInjectivity false in
/-- Retain the initial block and exact normalized annulus selected for a source fraction. -/
structure InitialBlockStep where
  /-- The exact initial block selected by the normalization branch. -/ block :
    Block.Basic.SourceEncodingEncoderBlockAlias
  /-- The exact normalized annulus associated with that initial block. -/ annulus : Annulus

constructive_injectivity InitialBlockStep

end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The next annulus step emits a regular block with its retained exponent and next annulus's selected sector.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem annulusStep_block_eq (annulus : Annulus)
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0) :
    (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).block =
      ⟨.regular,
        (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).block.exponent,
        ComplexContinuedFraction.Encoding.Sector.select (Encoder.Annulus.Blocks.annulusStep annulus
          residualNonzero).next.frac.value⟩ := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- The exact loop normalization exponent equals any candidate satisfying its strict lower and weak upper power-of-two
bounds.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem annulusStep_exponent_eq_of_bounds (annulus : Annulus)
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0)
    (candidate : Nat)
    (candidateLower :
      2 ^ candidate * GaussianInt.normNat (GaussianInt.gammaInt * Encoder.Annulus.Blocks.annulusResidual annulus) <
        GaussianInt.normNat annulus.frac.denominator)
    (candidateUpper :
      GaussianInt.normNat annulus.frac.denominator ≤
        2 ^ (candidate + 1) *
          GaussianInt.normNat (GaussianInt.gammaInt * Encoder.Annulus.Blocks.annulusResidual annulus)) :
    (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).block.exponent = candidate := by
  let directNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0 := by
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using residualNonzero
  let post := Encoder.Annulus.postInversion annulus directNonzero
  let normalized := Encoder.Annulus.normalizeLoop post.frac
    (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
  change normalized.exponent = candidate
  dsimp only [normalized, Encoder.Annulus.normalizeLoop]
  apply (BinaryNormalization.loop
    (GaussianInt.normNat post.frac.numerator) (GaussianInt.normNat post.frac.denominator)
    (GaussianInt.normNat_pos post.frac.denominatorNonzero) post.den_descent).exponent_eq_of_bounds
  · rw [post.num_eq, post.den_eq]
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using candidateLower
  · rw [post.num_eq, post.den_eq]
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using candidateUpper
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- The next annulus denominator is the retained gamma power times the gamma-scaled original integer residual.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem annulusStep_next_den_eq (annulus : Annulus)
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0) :
    (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).next.frac.denominator =
      GaussianInt.natPow GaussianInt.gammaInt (Encoder.Annulus.Blocks.annulusStep annulus
        residualNonzero).block.exponent *
        (GaussianInt.gammaInt * Encoder.Annulus.Blocks.annulusResidual annulus) := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data.CCL.Encoding in
/-- The next annulus numerator is the original annulus denominator.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem annulusStep_next_num_eq (annulus : Annulus)
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0) :
    (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).next.frac.numerator =
      annulus.frac.denominator := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Geometry.Projective in
/-- Compute a certified finite block encoding of a displayed fraction with nonzero numerator.

The exact numerator and denominator norms select the high or low initial branch. Retain that branch's normalization and
annulus continuation, then construct the projective point, realization and affine reconstruction from those same blocks.
-/
@[expose] def encodeBlocks (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero :
  fraction.numerator ≠ 0) :
    Encoder.Blocks.BlockEncoding fraction :=
  let highHere : (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) →
      Encoder.Blocks.BlockEncoding fraction := fun highBranch => by
    let scan := BinaryNormalization.high
      (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
      (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
    let initial := Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch
    let suffix := Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus
    let block : Block :=
      ⟨.regular, scan.exponent,
        ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
    let point := Line.Matrix.act block.matrix suffix.tail.point
    have numeratorIdentity : initial.annulus.frac.numerator = fraction.numerator := by
      rfl
    have denominatorIdentity : initial.annulus.frac.denominator =
        GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.denominator := by
      rfl
    have scaledValue :
        Power.natPow
            Basic.Canonical.gamma scan.exponent *
          initial.annulus.frac.value = fraction.value := by
      apply Field.mul_right_cancel_of_ne
        fraction.denominatorGaussianNonzero
      calc
        (Power.natPow
              Basic.Canonical.gamma scan.exponent *
            initial.annulus.frac.value) * GaussianInt.toGaussian fraction.denominator =
            initial.annulus.frac.value *
              (Power.natPow
                Basic.Canonical.gamma scan.exponent *
                  GaussianInt.toGaussian fraction.denominator) := by
          apply Basic.ext <;>
            simp only [Basic.mul_re,
              Basic.mul_im] <;>
            ring1
        _ = initial.annulus.frac.value *
              GaussianInt.toGaussian initial.annulus.frac.denominator := by
          rw [denominatorIdentity, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_gammaInt_pow]
        _ = GaussianInt.toGaussian initial.annulus.frac.numerator :=
          initial.annulus.frac.value_mul_denominator
        _ = GaussianInt.toGaussian fraction.numerator := by rw [numeratorIdentity]
        _ = fraction.value * GaussianInt.toGaussian fraction.denominator :=
          fraction.value_mul_denominator.symm
    refine
      ⟨block :: suffix.continuation, point,
        Cylinder.Projective.ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
    have acted : point.Equivalent
        (Line.Matrix.act block.matrix suffix.tail.model.point) :=
      Line.Matrix.act_respects_equivalent
        block.matrix suffix.tail.equivalent
    have modeled :
        (Line.Matrix.act block.matrix suffix.tail.model.point).Equivalent
          (Line.Proj.affine fraction.value) := by
      dsimp only [block, Block.matrix]
      exact Block.Semantics.Tail.regularBlock_act_equivalent
        scan.exponent suffix.tail.model initial.annulus.frac.value
        fraction.value suffix.models scaledValue
    exact Line.Gaussian.Proj.equivalent_trans acted modeled
      (block.act_model_valid suffix.tail)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate fraction.value)
  let lowHere : (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) →
      Encoder.Blocks.BlockEncoding fraction := fun lowBranch => by
    let scan := BinaryNormalization.low
      (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
      (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero) lowBranch
    let initial := Encoder.Normalization.initialLow fraction numeratorNonzero lowBranch
    let suffix := Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus
    let block : Block :=
      ⟨.initialLow, scan.exponent,
        ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
    let point := Line.Matrix.act block.matrix suffix.tail.point
    have numeratorIdentity : initial.annulus.frac.numerator =
        GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.numerator := by
      rfl
    have denominatorIdentity : initial.annulus.frac.denominator = fraction.denominator := by
      rfl
    have scaledValue : initial.annulus.frac.value =
        Power.natPow
          Basic.Canonical.gamma scan.exponent * fraction.value := by
      apply Field.mul_right_cancel_of_ne
        fraction.denominatorGaussianNonzero
      calc
        initial.annulus.frac.value * GaussianInt.toGaussian fraction.denominator =
            initial.annulus.frac.value *
              GaussianInt.toGaussian initial.annulus.frac.denominator := by
          rw [denominatorIdentity]
        _ = GaussianInt.toGaussian initial.annulus.frac.numerator :=
          initial.annulus.frac.value_mul_denominator
        _ = GaussianInt.toGaussian (GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.numerator) := by
          rw [numeratorIdentity]
        _ = Power.natPow
              Basic.Canonical.gamma scan.exponent *
            GaussianInt.toGaussian fraction.numerator := by
          rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_gammaInt_pow]
        _ = Power.natPow
              Basic.Canonical.gamma scan.exponent *
            (fraction.value * GaussianInt.toGaussian fraction.denominator) := by
          rw [fraction.value_mul_denominator]
        _ = (Power.natPow
              Basic.Canonical.gamma scan.exponent * fraction.value) *
            GaussianInt.toGaussian fraction.denominator := by
          apply Basic.ext <;>
            simp only [Basic.mul_re,
              Basic.mul_im] <;>
            ring1
    refine
      ⟨block :: suffix.continuation, point,
        Cylinder.Projective.ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
    have acted : point.Equivalent
        (Line.Matrix.act block.matrix suffix.tail.model.point) :=
      Line.Matrix.act_respects_equivalent
        block.matrix suffix.tail.equivalent
    have modeled :
        (Line.Matrix.act block.matrix suffix.tail.model.point).Equivalent
          (Line.Proj.affine fraction.value) := by
      dsimp only [block, Block.matrix]
      exact Block.Semantics.Tail.lowBlock_act_equivalent
        scan.exponent suffix.tail.model initial.annulus.frac.value
        fraction.value suffix.models scaledValue
    exact Line.Gaussian.Proj.equivalent_trans acted modeled
      (block.act_model_valid suffix.tail)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate fraction.value)
  if highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator then
    highHere highBranch
  else
    lowHere (Nat.lt_of_not_ge highBranch)
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- The computed block list follows the exact retained high-versus-low normalization branch.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_blocks_eq (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks =
      if highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator then
        let scan := BinaryNormalization.high
          (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
          (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
        let initial := Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch
        let block : Block :=
          ⟨.regular, scan.exponent,
            ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
        block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus).continuation
      else
        let lowBranch := Nat.lt_of_not_ge highBranch
        let scan := BinaryNormalization.low
          (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
          (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero)
          lowBranch
        let initial := Encoder.Normalization.initialLow fraction numeratorNonzero lowBranch
        let block : Block :=
          ⟨.initialLow, scan.exponent,
            ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
        block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus).continuation := by
  unfold Encoder.Blocks.encodeBlocks
  split <;> rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- The high branch emits its exact regular initial block followed by the normalized annulus continuation.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_blocks_of_high (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks =
      let scan := BinaryNormalization.high
        (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
        (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
      let initial := Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch
      let block : Block :=
        ⟨.regular, scan.exponent,
          ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
      block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus).continuation := by
  rw [Encoder.Blocks.encodeBlocks_blocks_eq]
  rw [dif_pos highBranch]
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- The low branch emits its exact initial-low block followed by the normalized annulus continuation.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_blocks_of_low (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks =
      let scan := BinaryNormalization.low
        (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
        (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero)
        lowBranch
      let initial := Encoder.Normalization.initialLow fraction numeratorNonzero lowBranch
      let block : Block :=
        ⟨.initialLow, scan.exponent,
          ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
      block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus).continuation := by
  rw [Encoder.Blocks.encodeBlocks_blocks_eq]
  rw [dif_neg (Nat.not_le_of_lt lowBranch)]
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- Read the exact projective realization stored with the computed block encoding. -/
@[expose] def encodeBlocks_realizes (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    Cylinder.Projective.SourceEncodingEncoderProjectiveRealizesAlias
      (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
      (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).point :=
  (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).realizes
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- The computed block point is projectively equivalent to the original fraction's affine value.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_reconstruct (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).point.Equivalent
      (Line.Proj.affine fraction.value) :=
  (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).reconstruct
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Geometry.Projective in
/-- Construct the high-branch block encoding using the retained denominator scaling and annulus continuation. -/
private def encodeHighBlocks (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    Encoder.Blocks.BlockEncoding fraction := by
  let scan := BinaryNormalization.high
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
  let initial := Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch
  let suffix := Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus
  let block : Block :=
    ⟨.regular, scan.exponent,
      ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
  let point := Line.Matrix.act block.matrix suffix.tail.point
  have numeratorIdentity : initial.annulus.frac.numerator = fraction.numerator := by
    rfl
  have denominatorIdentity : initial.annulus.frac.denominator =
      GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.denominator := by
    rfl
  have scaledValue :
      Power.natPow
          Basic.Canonical.gamma scan.exponent *
        initial.annulus.frac.value = fraction.value :=
    GaussianInt.Fraction.Scale.value_of_scaled_den fraction initial.annulus.frac scan.exponent
      numeratorIdentity denominatorIdentity
  refine
    ⟨block :: suffix.continuation, point,
      Cylinder.Projective.ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
  have acted : point.Equivalent
      (Line.Matrix.act block.matrix suffix.tail.model.point) :=
    Line.Matrix.act_respects_equivalent block.matrix suffix.tail.equivalent
  have modeled :
      (Line.Matrix.act block.matrix suffix.tail.model.point).Equivalent
        (Line.Proj.affine fraction.value) := by
    dsimp only [block, Block.matrix]
    exact Block.Semantics.Tail.regularBlock_act_equivalent
      scan.exponent suffix.tail.model initial.annulus.frac.value
      fraction.value suffix.models scaledValue
  exact Line.Gaussian.Proj.equivalent_trans acted modeled
    (block.act_model_valid suffix.tail)
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate fraction.value)
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Geometry.Projective in
/-- Construct the low-branch block encoding using the retained numerator scaling and annulus continuation. -/
private def encodeLowBlocks (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    Encoder.Blocks.BlockEncoding fraction := by
  let scan := BinaryNormalization.low
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero) lowBranch
  let initial := Encoder.Normalization.initialLow fraction numeratorNonzero lowBranch
  let suffix := Encoder.Annulus.Blocks.encodeAnnulusBlocks initial.annulus
  let block : Block :=
    ⟨.initialLow, scan.exponent,
      ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩
  let point := Line.Matrix.act block.matrix suffix.tail.point
  have numeratorIdentity : initial.annulus.frac.numerator =
      GaussianInt.natPow GaussianInt.gammaInt scan.exponent * fraction.numerator := by
    rfl
  have denominatorIdentity : initial.annulus.frac.denominator = fraction.denominator := by
    rfl
  have scaledValue : initial.annulus.frac.value =
      Power.natPow
          Basic.Canonical.gamma scan.exponent *
        fraction.value :=
    GaussianInt.Fraction.Scale.value_of_scaled_num fraction initial.annulus.frac scan.exponent
      numeratorIdentity denominatorIdentity
  refine
    ⟨block :: suffix.continuation, point,
      Cylinder.Projective.ProjectiveRealizes.step block suffix.tail suffix.realizes, ?_⟩
  have acted : point.Equivalent
      (Line.Matrix.act block.matrix suffix.tail.model.point) :=
    Line.Matrix.act_respects_equivalent block.matrix suffix.tail.equivalent
  have modeled :
      (Line.Matrix.act block.matrix suffix.tail.model.point).Equivalent
        (Line.Proj.affine fraction.value) := by
    dsimp only [block, Block.matrix]
    exact Block.Semantics.Tail.lowBlock_act_equivalent
      scan.exponent suffix.tail.model initial.annulus.frac.value
      fraction.value suffix.models scaledValue
  exact Line.Gaussian.Proj.equivalent_trans acted modeled
    (block.act_model_valid suffix.tail)
    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate fraction.value)
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- Retain the regular initial block and annulus computed by the exact high normalization. -/
@[expose] def initialHighBlockStep (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    Encoder.Blocks.InitialBlockStep :=
  let scan := BinaryNormalization.high
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch
  let initial := Encoder.Normalization.initialHigh fraction numeratorNonzero highBranch
  ⟨⟨.regular, scan.exponent,
      ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩,
    initial.annulus⟩
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- The high-branch block list is the retained initialHighBlockStep block followed by its annulus continuation.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_blocks_of_high_step (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks =
      (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).block ::
        (Encoder.Annulus.Blocks.encodeAnnulusBlocks
          (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).annulus).continuation := by
  simpa only [Encoder.Blocks.initialHighBlockStep] using
    Encoder.Blocks.encodeBlocks_blocks_of_high fraction numeratorNonzero highBranch
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The retained high initial block is regular and uses its exact exponent and normalized sector.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem initialHighBlockStep_block_eq (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).block =
      ⟨.regular,
        (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent,
        ComplexContinuedFraction.Encoding.Sector.select
          (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.value⟩ := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- The high normalized denominator is the retained integer gamma power times the source denominator.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem initialHighBlockStep_den_eq (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.denominator =
      GaussianInt.natPow GaussianInt.gammaInt
          (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent *
        fraction.denominator := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Nat in
/-- A candidate satisfying the high scan's weak lower and strict upper bounds equals its retained exponent.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem initialHighBlockStep_exponent_eq_of_bounds (fraction :
  GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator)
    (candidate : Nat)
    (candidateLower :
      2 ^ candidate * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator)
    (candidateUpper :
      GaussianInt.normNat fraction.numerator <
        2 ^ (candidate + 1) * GaussianInt.normNat fraction.denominator) :
    (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).block.exponent =
      candidate := by
  unfold Encoder.Blocks.initialHighBlockStep
  dsimp only
  exact (BinaryNormalization.high
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos fraction.denominatorNonzero) highBranch).exponent_eq_of_bounds
      candidateLower candidateUpper
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- The high normalization preserves the exact source numerator.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem initialHighBlockStep_num_eq (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (highBranch : 2 * GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator) :
    (Encoder.Blocks.initialHighBlockStep fraction numeratorNonzero highBranch).annulus.frac.numerator =
      fraction.numerator := by
  rfl
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Nat in
/-- Retain the initial-low block and annulus computed by the exact low normalization. -/
@[expose] def initialLowBlockStep (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    Encoder.Blocks.InitialBlockStep :=
  let scan := BinaryNormalization.low
    (GaussianInt.normNat fraction.numerator) (GaussianInt.normNat fraction.denominator)
    (GaussianInt.normNat_pos numeratorNonzero) (GaussianInt.normNat_pos fraction.denominatorNonzero) lowBranch
  let initial := Encoder.Normalization.initialLow fraction numeratorNonzero lowBranch
  ⟨⟨.initialLow, scan.exponent,
      ComplexContinuedFraction.Encoding.Sector.select initial.annulus.frac.value⟩,
    initial.annulus⟩
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- The low-branch block list is the retained initialLowBlockStep block followed by its annulus continuation.

The supplied high or low norm comparison selects the displayed initial block and retained annulus continuation. No
normalization exponent or sector is replaced. -/
theorem encodeBlocks_blocks_of_low_step (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (lowBranch : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks =
      (Encoder.Blocks.initialLowBlockStep fraction numeratorNonzero lowBranch).block ::
        (Encoder.Annulus.Blocks.encodeAnnulusBlocks
          (Encoder.Blocks.initialLowBlockStep fraction numeratorNonzero lowBranch).annulus).continuation := by
  simpa only [Encoder.Blocks.initialLowBlockStep] using
    Encoder.Blocks.encodeBlocks_blocks_of_low fraction numeratorNonzero lowBranch
end Purelib.Data.CCL.Encoding.Encoder.Blocks

end
