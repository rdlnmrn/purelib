module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Block.Semantics
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Data.CCL.Encoding.Encoder.Annulus

import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Fraction.Scale

import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Projective.SectorBlock.Tail
import Purelib.Geometry.Projective.SectorBlock.Tail.Projective
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Tactic.NormNum.Integer
import Purelib.Data.Gaussian.Constants
import Purelib.Data.GaussianInt.Power
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.CCL.Encoding.Block.Contraction
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Purelib.Tactic.Ring

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain the continuation blocks and projective tail of an annulus fraction.

The tail belongs to the fraction's exact selected sector, realizes the retained continuation list and models the same
original annulus value through its compatible model. -/
structure AnnulusBlockEncoding (annulus : Annulus) where
  /-- The retained finite continuation block list. -/ continuation : List Block.Basic.SourceEncodingEncoderBlockAlias
  /-- The retained projective tail for the original annulus's selected sector. -/ tail :
    SectorBlock.Tail.SourceEncodingEncoderProjectiveTailAlias
      (Sector.select
        annulus.frac.value)
  /-- The exact continuation realizes the retained tail point. -/ realizes :
    Cylinder.Projective.SourceEncodingEncoderProjectiveRealizesAlias continuation tail.point
  /-- The retained tail model represents the original annulus fraction value. -/ models : tail.model.ModelsValue
    annulus.frac.value

constructive_injectivity AnnulusBlockEncoding

end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
set_option genInjectivity false in
/-- Retain one emitted regular block and the exact next normalized annulus. -/
structure AnnulusStep where
  /-- The computed regular block for the next normalization. -/ block : Block.Basic.SourceEncodingEncoderBlockAlias
  /-- The exact next normalized annulus. -/ next : Annulus

constructive_injectivity AnnulusStep

end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Subtract the selected integral sector representative times denominator from the retained annulus numerator. -/
@[expose] def annulusResidual (annulus : Annulus) : GaussianInt :=
  annulus.frac.numerator -
    Sector.Integral.sectorInt (Sector.select annulus.frac.value) *
      annulus.frac.denominator
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Compute the post-inversion fraction and exact loop normalization for a nonzero annulus residual.

The output block retains the normalization exponent and next selected sector, and the next annulus is that same computed
normalization result. -/
@[expose] def annulusStep (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) : AnnulusStep :=
  let post := postInversion annulus (by
    simpa only [annulusResidual] using residualNonzero)
  let normalized := normalizeLoop post.frac
    (GaussianInt.normNat annulus.frac.denominator)
            (by rewrite [post.num_eq]; exact post.den_descent)
            (congrArg GaussianInt.normNat post.num_eq)
  ⟨⟨.regular, normalized.exponent,
      Sector.select normalized.annulus.frac.value⟩,
    normalized.annulus⟩
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective

/-- Construct the original terminal annulus realization at a zero selected integral residual. -/
@[expose] def ofTerminal (annulus : Annulus)
    (residualZero : annulus.frac.numerator -
      Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator = 0) :
    AnnulusBlockEncoding annulus :=
  let sector := Sector.select annulus.frac.value
  let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector := .omega
  let tail := SectorBlock.Tail.ProjectiveTail.ofTail model
  ⟨[], tail, Cylinder.Projective.ProjectiveRealizes.done tail.point tail.valid,
    Annulus.terminal_value_eq_rep annulus sector residualZero⟩

/-- Prepend the original normalized regular block and retain the same computed next realization.

The original inverse fraction and normalization certificates identify its affine
model. The constructor consumes the exact next point, model, ordered block
list and realization data; it performs no recursive encoding or fuel search.
-/
@[expose] def prepend (annulus : Annulus) (post : PostInversion annulus)
    (normalized : LoopResult post.frac (GaussianInt.normNat annulus.frac.denominator))
    (next : AnnulusBlockEncoding normalized.annulus) : AnnulusBlockEncoding annulus :=
  let sector := Sector.select annulus.frac.value
  let block : Block := ⟨.regular, normalized.exponent, Sector.select normalized.annulus.frac.value⟩
  let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector :=
    .affine post.frac.value annulus.frac.value (Annulus.post_compatible annulus post)
  let point := Line.Matrix.act block.matrix next.tail.point
  let tail : SectorBlock.Tail.SourceEncodingEncoderProjectiveTailAlias sector :=
    { point := point
      valid := block.act_projectiveTail_valid next.tail
      model := model
      equivalent := by
        have acted : point.Equivalent (Line.Matrix.act block.matrix next.tail.model.point) :=
          Line.Matrix.act_respects_equivalent block.matrix next.tail.equivalent
        have modeled : (Line.Matrix.act block.matrix next.tail.model.point).Equivalent
            (Line.Proj.affine post.frac.value) := by
          dsimp only [block, Block.matrix]
          exact Block.Semantics.Tail.regularBlock_act_equivalent normalized.exponent next.tail.model
            normalized.annulus.frac.value post.frac.value next.models
            (GaussianInt.Fraction.Scale.value_of_scaled_den post.frac normalized.annulus.frac
              normalized.exponent normalized.num_eq normalized.den_eq)
        exact Line.Gaussian.Proj.equivalent_trans acted modeled (block.act_model_valid next.tail)
          (Line.Gaussian.Proj.affine_hasNonzeroCoordinate post.frac.value) }
  ⟨block :: next.continuation, tail,
    Cylinder.Projective.ProjectiveRealizes.step block next.tail next.realizes, rfl⟩

namespace encodeAnnulusBlocks

/-- Evaluate the original sufficient-fuel recurrence and retain its complete realization data.

Each surplus fuel unit is discarded before the original annulus transition.
Shared terminal and nonterminal constructors retain its complete values; direct
norm descent below agrees with this original finite algorithm on every input.
-/
@[expose] def fuelHere :
    (fuel : Nat) → (annulus : Annulus) →
      GaussianInt.normNat annulus.frac.denominator < fuel → AnnulusBlockEncoding annulus
  | 0, _annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound =>
      if slack : GaussianInt.normNat annulus.frac.denominator < fuel then
        fuelHere fuel annulus slack
      else
        let residual := annulus.frac.numerator -
          Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator
        if residualZero : residual = 0 then ofTerminal annulus residualZero
        else
          let post := postInversion annulus residualZero
          let normalized := normalizeLoop post.frac
            (GaussianInt.normNat annulus.frac.denominator)
            (by rewrite [post.num_eq]; exact post.den_descent)
            (congrArg GaussianInt.normNat post.num_eq)
          have measureEq : GaussianInt.normNat annulus.frac.denominator = fuel :=
            Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt slack)
          let next := fuelHere fuel normalized.annulus (measureEq ▸ normalized.measure_lt)
          prepend annulus post normalized next

end encodeAnnulusBlocks

/-- Compute the original finite annulus continuation by direct strict denominator-norm descent.

Each nonterminal step retains its original sector, inverse fraction, selected
normalization and exact next realization. No loop discards old excess fuel;
all returned data agree with the original sufficient-fuel recurrence.
-/
@[expose] def encodeAnnulusBlocks (annulus : Annulus) : AnnulusBlockEncoding annulus :=
  let residual := annulus.frac.numerator -
    Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator
  if residualZero : residual = 0 then ofTerminal annulus residualZero
  else
    let post := postInversion annulus residualZero
    let normalized := normalizeLoop post.frac
      (GaussianInt.normNat annulus.frac.denominator)
      (by rewrite [post.num_eq]; exact post.den_descent)
      (congrArg GaussianInt.normNat post.num_eq)
    let next := encodeAnnulusBlocks normalized.annulus
    prepend annulus post normalized next
termination_by GaussianInt.normNat annulus.frac.denominator
decreasing_by exact normalized.measure_lt

end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding

/-- Every sufficient original fuel produces the same complete cached annulus realization as direct norm descent.

Equality covers the ordered block list, retained projective point, affine or
infinity model and all realization certificates. It establishes preservation
of the original finite algorithm's complete values, not only its word or
projective reading.
-/
theorem fuelHere_eq : ∀ fuel annulus bound,
    encodeAnnulusBlocks.fuelHere fuel annulus bound = encodeAnnulusBlocks annulus
  | 0, _annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound => by
      rewrite [encodeAnnulusBlocks.fuelHere]
      split
      · rename_i slack
        exact fuelHere_eq fuel annulus slack
      · rename_i noSlack
        have measureEq : GaussianInt.normNat annulus.frac.denominator = fuel :=
          Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt noSlack)
        rewrite [encodeAnnulusBlocks]
        dsimp only
        by_cases residualZero : annulus.frac.numerator -
            Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator = 0
        · rewrite [dif_pos residualZero, dif_pos residualZero]
          rfl
        · rewrite [dif_neg residualZero, dif_neg residualZero]
          let post := postInversion annulus residualZero
          let normalized := normalizeLoop post.frac
            (GaussianInt.normNat annulus.frac.denominator)
            (by rewrite [post.num_eq]; exact post.den_descent)
            (congrArg GaussianInt.normNat post.num_eq)
          have nextBound : GaussianInt.normNat normalized.annulus.frac.denominator < fuel :=
            measureEq ▸ normalized.measure_lt
          change prepend annulus post normalized
            (encodeAnnulusBlocks.fuelHere fuel normalized.annulus nextBound) =
              prepend annulus post normalized (encodeAnnulusBlocks normalized.annulus)
          exact congrArg (prepend annulus post normalized) (fuelHere_eq fuel normalized.annulus nextBound)
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The exact continuation is empty at zero residual and otherwise begins with the computed normalized regular block.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and the exact next
realization are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_eq (annulus : Annulus) :
    (encodeAnnulusBlocks annulus).continuation =
      let sector := Sector.select annulus.frac.value
      let residual :=
        annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator
      if residualZero : residual = 0 then
        []
      else
        let post := postInversion annulus (by
          simpa only [residual, sector] using residualZero)
        let normalized := normalizeLoop post.frac
          (GaussianInt.normNat annulus.frac.denominator)
            (by rewrite [post.num_eq]; exact post.den_descent)
            (congrArg GaussianInt.normNat post.num_eq)
        let block : Block :=
          ⟨.regular, normalized.exponent,
            Sector.select normalized.annulus.frac.value⟩
        block :: (encodeAnnulusBlocks normalized.annulus).continuation := by
  rewrite [encodeAnnulusBlocks]
  dsimp only
  by_cases residualZero : annulus.frac.numerator -
      Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator = 0
  · rewrite [dif_pos residualZero, dif_pos residualZero]
    rfl
  · rewrite [dif_neg residualZero, dif_neg residualZero]
    rfl
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A zero selected annulus residual gives an empty retained continuation.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and the exact next
realization are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_eq (annulus : Annulus)
    (residualZero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (Sector.select annulus.frac.value) *
            annulus.frac.denominator =
        0) :
    (encodeAnnulusBlocks annulus).continuation = [] := by
  rw [encodeAnnulusBlocks_continuation_eq]
  rw [dif_pos residualZero]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A nonzero residual gives the exact normalized regular block followed by the next annulus continuation.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and the exact next
realization are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_ne (annulus : Annulus)
    (residualNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0) :
    (encodeAnnulusBlocks annulus).continuation =
      let post := postInversion annulus residualNonzero
      let normalized := normalizeLoop post.frac
        (GaussianInt.normNat annulus.frac.denominator)
            (by rewrite [post.num_eq]; exact post.den_descent)
            (congrArg GaussianInt.normNat post.num_eq)
      let block : Block :=
        ⟨.regular, normalized.exponent,
          Sector.select normalized.annulus.frac.value⟩
      block :: (encodeAnnulusBlocks normalized.annulus).continuation := by
  rw [encodeAnnulusBlocks_continuation_eq]
  rw [dif_neg residualNonzero]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A nonzero residual exposes the continuation through the exact retained annulusStep result.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and the exact next
realization are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_ne_step (annulus : Annulus)
    (residualNonzero : annulusResidual annulus ≠ 0) :
    (encodeAnnulusBlocks annulus).continuation =
      (annulusStep annulus residualNonzero).block ::
        (encodeAnnulusBlocks
          (annulusStep annulus residualNonzero).next).continuation := by
  let directNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0 := by
    simpa only [annulusResidual] using residualNonzero
  simpa only [annulusStep] using
    encodeAnnulusBlocks_continuation_of_ne annulus directNonzero
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
/-- A zero annulusResidual gives an empty retained continuation list.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and the exact next
realization are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_residual_eq (annulus : Annulus)
    (residualZero : annulusResidual annulus = 0) :
    (encodeAnnulusBlocks annulus).continuation = [] :=
  encodeAnnulusBlocks_continuation_of_eq annulus (by
    simpa only [annulusResidual] using residualZero)
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end
