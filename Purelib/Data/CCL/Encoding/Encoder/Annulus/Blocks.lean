module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Block.Matrix
public import Purelib.Data.CCL.Encoding.Block.Semantics
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Data.CCL.Encoding.Encoder.Annulus
import all Purelib.Data.CCL.Encoding.Encoder.Annulus

import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import all Purelib.Data.GaussianInt.Fraction.Scale

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
    Geometry.Projective.SectorBlock.Tail.SourceEncodingEncoderProjectiveTailAlias
      (ComplexContinuedFraction.Encoding.Sector.select
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
@[expose] def annulusResidual (annulus : Annulus) : Data.GaussianInt :=
  annulus.frac.numerator -
    Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
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
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0) : Encoder.Annulus.Blocks.AnnulusStep :=
  let post := Encoder.Annulus.postInversion annulus (by
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using residualNonzero)
  let normalized := Encoder.Annulus.normalizeLoop post.frac
    (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
  ⟨⟨.regular, normalized.exponent,
      ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩,
    normalized.annulus⟩
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Compute the finite continuation blocks of a retained annulus together with exact projective realization.

Use fuel one greater than the denominator norm, discard excess fuel without changing the annulus, and terminate at a
zero selected residual. Each nonterminal step retains the post-inversion and normalized fractions, recurs using strict
measure descent, and constructs the same compatible model and projective tail. -/
@[expose] def encodeAnnulusBlocks (annulus : Annulus) : Encoder.Annulus.Blocks.AnnulusBlockEncoding
  annulus :=
  fuelHere (Nat.succ (GaussianInt.normNat annulus.frac.denominator)) annulus (Nat.lt_succ_self _)
where
  fuelHere :
      (fuel : Nat) → (annulus : Annulus) →
        GaussianInt.normNat annulus.frac.denominator < fuel → Encoder.Annulus.Blocks.AnnulusBlockEncoding annulus
    | 0, annulus, bound => False.elim (Nat.not_lt_zero _ bound)
    | fuel + 1, annulus, bound =>
        if slack : GaussianInt.normNat annulus.frac.denominator < fuel then
          fuelHere fuel annulus slack
        else
          let sector := ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value
          let residual :=
            annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator
          if residualZero : residual = 0 then
            let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector := .omega
            let tail := Geometry.Projective.SectorBlock.Tail.ProjectiveTail.ofTail model
            ⟨[], tail,
              Cylinder.Projective.ProjectiveRealizes.done tail.point tail.valid,
              by
                change annulus.frac.value = sector.rep
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
                apply Field.mul_right_cancel_of_ne
                  annulus.frac.denominatorGaussianNonzero
                calc
                  annulus.frac.value * GaussianInt.toGaussian annulus.frac.denominator =
                      GaussianInt.toGaussian annulus.frac.numerator := annulus.frac.value_mul_denominator
                  _ = GaussianInt.toGaussian (Sector.Integral.sectorInt sector * annulus.frac.denominator) := by
                    rw [numeratorIdentity]
                  _ = sector.rep * GaussianInt.toGaussian annulus.frac.denominator := by
                    rw [GaussianInt.toGaussian_mul, Sector.Integral.toGaussian_sectorInt]
              ⟩
          else
            let post := Encoder.Annulus.postInversion annulus (by
              simpa only [residual, sector] using residualZero)
            let normalized := Encoder.Annulus.normalizeLoop post.frac (GaussianInt.normNat annulus.frac.denominator)
              post.den_descent rfl
            have measureEq : GaussianInt.normNat annulus.frac.denominator = fuel :=
              Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt slack)
            let next := fuelHere fuel normalized.annulus (by
              simpa only [measureEq] using normalized.measure_lt)
            let block : Block :=
              ⟨.regular, normalized.exponent,
                ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
            let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector :=
              .affine post.frac.value annulus.frac.value
                (by
                  let sector := ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value
                  have postNumerator : GaussianInt.toGaussian post.frac.numerator =
                      GaussianInt.toGaussian annulus.frac.denominator := by rw [post.num_eq]
                  have postDenominator : GaussianInt.toGaussian post.frac.denominator =
                      Basic.Canonical.gamma *
                        (GaussianInt.toGaussian annulus.frac.numerator - sector.rep *
                          GaussianInt.toGaussian annulus.frac.denominator) := by
                    rw [post.den_eq]
                    dsimp only [sector]
                    rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul,
                      GaussianInt.toGaussian_gammaInt, Sector.Integral.toGaussian_sectorInt]
                  have leftScaled :
                      (Basic.Canonical.gamma * post.frac.value *
                          annulus.frac.value) * GaussianInt.toGaussian post.frac.denominator =
                        Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.numerator := by
                    calc
                      (Basic.Canonical.gamma * post.frac.value *
                          annulus.frac.value) * GaussianInt.toGaussian post.frac.denominator =
                          Basic.Canonical.gamma *
                            (post.frac.value * GaussianInt.toGaussian post.frac.denominator) *
                              annulus.frac.value := by
                        apply Basic.ext <;>
                          simp only [Basic.mul_re,
                            Basic.mul_im] <;>
                          ring1
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian post.frac.numerator * annulus.frac.value := by
                        rw [post.frac.value_mul_denominator]
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.denominator * annulus.frac.value := by
                        rw [postNumerator]
                      _ = Basic.Canonical.gamma *
                          (annulus.frac.value * GaussianInt.toGaussian annulus.frac.denominator) := by
                        apply Basic.ext <;>
                          simp only [Basic.mul_re,
                            Basic.mul_im] <;>
                          ring1
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.numerator := by
                        rw [annulus.frac.value_mul_denominator]
                  have rightScaled :
                      (Basic.Canonical.gamma * post.frac.value *
                          sector.rep + 1) * GaussianInt.toGaussian post.frac.denominator =
                        Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.numerator := by
                    calc
                      (Basic.Canonical.gamma * post.frac.value *
                          sector.rep + 1) * GaussianInt.toGaussian post.frac.denominator =
                          Basic.Canonical.gamma *
                              (post.frac.value * GaussianInt.toGaussian post.frac.denominator) * sector.rep +
                            GaussianInt.toGaussian post.frac.denominator := by
                        apply Basic.ext <;>
                          simp only [Basic.add_re,
                            Basic.add_im,
                            Basic.mul_re,
                            Basic.mul_im,
                            Basic.one_re,
                            Basic.one_im] <;>
                          ring1
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian post.frac.numerator * sector.rep +
                            GaussianInt.toGaussian post.frac.denominator := by
                        rw [post.frac.value_mul_denominator]
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.denominator * sector.rep +
                            GaussianInt.toGaussian post.frac.denominator := by
                        rw [postNumerator]
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.denominator * sector.rep +
                            Basic.Canonical.gamma *
                              (GaussianInt.toGaussian annulus.frac.numerator - sector.rep *
                                GaussianInt.toGaussian annulus.frac.denominator) := by
                        rw [postDenominator]
                      _ = Basic.Canonical.gamma *
                          GaussianInt.toGaussian annulus.frac.numerator := by
                        apply Basic.ext <;>
                          simp only [Basic.add_re,
                            Basic.add_im,
                            Basic.sub_re,
                            Basic.sub_im,
                            Basic.mul_re,
                            Basic.mul_im] <;>
                          ring1
                  refine
                    { equation := ?_
                      band := annulus.band
                      holds := ComplexContinuedFraction.Encoding.Sector.select_spec annulus.frac.value annulus.band.1 }
                  apply Field.mul_right_cancel_of_ne
                    post.frac.denominatorGaussianNonzero
                  exact leftScaled.trans rightScaled.symm)
            let point := Line.Matrix.act block.matrix next.tail.point
            let tail : Geometry.Projective.SectorBlock.Tail.SourceEncodingEncoderProjectiveTailAlias sector :=
              { point := point
                valid := block.act_projectiveTail_valid next.tail
                model := model
                equivalent := by
                  have acted : point.Equivalent
                      (Line.Matrix.act block.matrix next.tail.model.point) :=
                    Line.Matrix.act_respects_equivalent block.matrix
                      next.tail.equivalent
                  have modeled :
                      (Line.Matrix.act block.matrix next.tail.model.point).Equivalent
                        (Line.Proj.affine post.frac.value) := by
                    dsimp only [block, Block.matrix]
                    exact Block.Semantics.Tail.regularBlock_act_equivalent
                      normalized.exponent next.tail.model
                      normalized.annulus.frac.value post.frac.value next.models
                      (by
                        apply Field.mul_right_cancel_of_ne
                          post.frac.denominatorGaussianNonzero
                        calc
                          (Power.natPow
                                Basic.Canonical.gamma normalized.exponent *
                              normalized.annulus.frac.value) *
                              GaussianInt.toGaussian post.frac.denominator =
                              normalized.annulus.frac.value *
                                (Power.natPow
                                  Basic.Canonical.gamma normalized.exponent *
                                    GaussianInt.toGaussian post.frac.denominator) := by
                            apply Basic.ext <;>
                              simp only [Basic.mul_re,
                                Basic.mul_im] <;>
                              ring1
                          _ = normalized.annulus.frac.value *
                                GaussianInt.toGaussian normalized.annulus.frac.denominator := by
                            rw [normalized.den_eq, GaussianInt.toGaussian_mul,
                              GaussianInt.toGaussian_gammaInt_pow]
                          _ = GaussianInt.toGaussian normalized.annulus.frac.numerator :=
                            normalized.annulus.frac.value_mul_denominator
                          _ = GaussianInt.toGaussian post.frac.numerator := by
                            rw [normalized.num_eq]
                          _ = post.frac.value * GaussianInt.toGaussian post.frac.denominator :=
                            post.frac.value_mul_denominator.symm)
                  exact Line.Gaussian.Proj.equivalent_trans acted modeled
                    (block.act_model_valid next.tail)
                    (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
                      post.frac.value) }
            ⟨block :: next.continuation, tail,
              Cylinder.Projective.ProjectiveRealizes.step block next.tail next.realizes,
              rfl⟩
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- Every sufficient internal fuel produces the same continuation list as the annulus encoder.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
private theorem encodeAnnulusBlocksFuel_continuation_eq :
    ∀ fuel annulus bound,
      (Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere fuel annulus bound).continuation =
        (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation
  | 0, annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound => by
      rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere]
      split
      · rename_i slack
        exact Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel_continuation_eq fuel annulus
          slack
      · rename_i noSlack
        have measureEq : GaussianInt.normNat annulus.frac.denominator = fuel :=
          Nat.le_antisymm (Nat.le_of_lt_succ bound)
            (Nat.le_of_not_gt noSlack)
        subst fuel
        unfold Encoder.Annulus.Blocks.encodeAnnulusBlocks
        rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere]
        rw [dif_neg (Nat.lt_irrefl _)]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The exact continuation is empty at zero residual and otherwise begins with the computed normalized regular block.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_eq (annulus : Annulus) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation =
      let sector := ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value
      let residual :=
        annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator
      if residualZero : residual = 0 then
        []
      else
        let post := Encoder.Annulus.postInversion annulus (by
          simpa only [residual, sector] using residualZero)
        let normalized := Encoder.Annulus.normalizeLoop post.frac
          (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
        let block : Block :=
          ⟨.regular, normalized.exponent,
            ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
        block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks normalized.annulus).continuation := by
  by_cases residualZero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator = 0
  · simp only [dif_pos residualZero]
    rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks, Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere]
    rw [dif_neg (Nat.lt_irrefl _), dif_pos residualZero]
  · simp only [dif_neg residualZero]
    let post := Encoder.Annulus.postInversion annulus residualZero
    let normalized := Encoder.Annulus.normalizeLoop post.frac
      (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
    let block : Block :=
      ⟨.regular, normalized.exponent,
        ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
    change (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation =
      block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks normalized.annulus).continuation
    calc
      (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation =
          block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere (GaussianInt.normNat annulus.frac.denominator)
            normalized.annulus normalized.measure_lt).continuation := by
        rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks, Encoder.Annulus.Blocks.encodeAnnulusBlocks.fuelHere]
        rw [dif_neg (Nat.lt_irrefl _), dif_neg residualZero]
      _ = block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks normalized.annulus).continuation :=
        congrArg (List.cons block)
          (by
            simpa only using
              Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel_continuation_eq
                (GaussianInt.normNat annulus.frac.denominator) normalized.annulus
                normalized.measure_lt)
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A zero selected annulus residual gives an empty retained continuation.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_eq (annulus : Annulus)
    (residualZero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator =
        0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation = [] := by
  rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks_continuation_eq]
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

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_ne (annulus : Annulus)
    (residualNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation =
      let post := Encoder.Annulus.postInversion annulus residualNonzero
      let normalized := Encoder.Annulus.normalizeLoop post.frac
        (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
      let block : Block :=
        ⟨.regular, normalized.exponent,
          ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
      block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocks normalized.annulus).continuation := by
  rw [Encoder.Annulus.Blocks.encodeAnnulusBlocks_continuation_eq]
  rw [dif_neg residualNonzero]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- A nonzero residual exposes the continuation through the exact retained annulusStep result.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_ne_step (annulus : Annulus)
    (residualNonzero : Encoder.Annulus.Blocks.annulusResidual annulus ≠ 0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation =
      (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).block ::
        (Encoder.Annulus.Blocks.encodeAnnulusBlocks
          (Encoder.Annulus.Blocks.annulusStep annulus residualNonzero).next).continuation := by
  let directNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0 := by
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using residualNonzero
  simpa only [Encoder.Annulus.Blocks.annulusStep] using
    Encoder.Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne annulus directNonzero
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data.CCL.Encoding in
/-- A zero annulusResidual gives an empty retained continuation list.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
theorem encodeAnnulusBlocks_continuation_of_residual_eq (annulus : Annulus)
    (residualZero : Encoder.Annulus.Blocks.annulusResidual annulus = 0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocks annulus).continuation = [] :=
  Encoder.Annulus.Blocks.encodeAnnulusBlocks_continuation_of_eq annulus (by
    simpa only [Encoder.Annulus.Blocks.annulusResidual] using residualZero)
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- The loop-normalized value times its retained gamma power recovers the post-inversion fraction value.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
private theorem normalized_scaled_value (post : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (oldMeasure :
  Nat)
    (postStrict : GaussianInt.normNat post.denominator < GaussianInt.normNat post.numerator)
    (numeratorMeasure : GaussianInt.normNat post.numerator = oldMeasure) :
    Power.natPow
        Basic.Canonical.gamma
        (Encoder.Annulus.normalizeLoop post oldMeasure postStrict numeratorMeasure).exponent *
      (Encoder.Annulus.normalizeLoop post oldMeasure postStrict numeratorMeasure).annulus.frac.value =
        post.value := by
  let normalized := Encoder.Annulus.normalizeLoop post oldMeasure postStrict numeratorMeasure
  exact GaussianInt.Fraction.Scale.value_of_scaled_den post normalized.annulus.frac normalized.exponent
    normalized.num_eq normalized.den_eq
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Geometry.Projective in
/-- Compute an annulus continuation from sufficient denominator-norm fuel using the retained private reconstruction
helpers.

The recurrence preserves slack-fuel removal, the terminal infinity model and the exact nonterminal normalization path.
Its stored tail, realization and modeled value belong to the same computed continuation. -/
private def encodeAnnulusBlocksFuel :
    (fuel : Nat) → (annulus : Annulus) →
      GaussianInt.normNat annulus.frac.denominator < fuel → Encoder.Annulus.Blocks.AnnulusBlockEncoding annulus
  | 0, annulus, bound => False.elim (Nat.not_lt_zero _ bound)
  | fuel + 1, annulus, bound =>
      if slack : GaussianInt.normNat annulus.frac.denominator < fuel then
        Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel fuel annulus slack
      else
        let sector := ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value
        let residual :=
          annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator
        if residualZero : residual = 0 then
          let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector := .omega
          let tail := Geometry.Projective.SectorBlock.Tail.ProjectiveTail.ofTail model
          ⟨[], tail,
            Cylinder.Projective.ProjectiveRealizes.done tail.point tail.valid,
            by
              change annulus.frac.value = sector.rep
              exact Encoder.Annulus.terminal_value_eq_rep annulus sector (by
                simpa only [residual, sector] using residualZero)⟩
        else
          let post := Encoder.Annulus.postInversion annulus (by
            simpa only [residual, sector] using residualZero)
          let normalized := Encoder.Annulus.normalizeLoop post.frac (GaussianInt.normNat annulus.frac.denominator)
            post.den_descent rfl
          have measureEq : GaussianInt.normNat annulus.frac.denominator = fuel :=
            Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt slack)
          let next := Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel fuel normalized.annulus
            (by
            simpa only [measureEq] using normalized.measure_lt)
          let block : Block :=
            ⟨.regular, normalized.exponent,
              ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
          let model : SectorBlock.Tail.SourceEncodingEncoderTailAlias sector :=
            .affine post.frac.value annulus.frac.value
              (Encoder.Annulus.post_compatible annulus post)
          let point := Line.Matrix.act block.matrix next.tail.point
          let tail : Geometry.Projective.SectorBlock.Tail.SourceEncodingEncoderProjectiveTailAlias sector :=
            { point := point
              valid := block.act_projectiveTail_valid next.tail
              model := model
              equivalent := by
                have acted : point.Equivalent
                    (Line.Matrix.act block.matrix next.tail.model.point) :=
                  Line.Matrix.act_respects_equivalent block.matrix
                    next.tail.equivalent
                have modeled :
                    (Line.Matrix.act block.matrix next.tail.model.point).Equivalent
                      (Line.Proj.affine post.frac.value) := by
                  dsimp only [block, Block.matrix]
                  exact Block.Semantics.Tail.regularBlock_act_equivalent
                    normalized.exponent next.tail.model
                    normalized.annulus.frac.value post.frac.value next.models
                    (Encoder.Annulus.Blocks.normalized_scaled_value post.frac
                      (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl)
                exact Line.Gaussian.Proj.equivalent_trans acted modeled
                  (block.act_model_valid next.tail)
                  (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
                    post.frac.value) }
          ⟨block :: next.continuation, tail,
            Cylinder.Projective.ProjectiveRealizes.step block next.tail next.realizes,
            rfl⟩
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The private sufficient-fuel continuation is empty when the selected residual is zero.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
private theorem encodeAnnulusBlocksFuel_continuation_of_eq
    (annulus : Annulus)
    (residualZero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator =
        0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel (Nat.succ (GaussianInt.normNat annulus.frac.denominator)) annulus
      (Nat.lt_succ_self _)).continuation = [] := by
  rw [Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel]
  rw [dif_neg (Nat.lt_irrefl _), dif_pos residualZero]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The private sufficient-fuel continuation starts with the exact normalized regular block when its residual is
nonzero.

The retained residual selects the empty or nonempty continuation. Normalized fractions, block order and recursive fuel
bounds are the same on both sides. -/
private theorem encodeAnnulusBlocksFuel_continuation_of_ne
    (annulus : Annulus)
    (residualNonzero :
      annulus.frac.numerator -
          Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select annulus.frac.value) *
            annulus.frac.denominator ≠
        0) :
    (Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel (Nat.succ (GaussianInt.normNat annulus.frac.denominator)) annulus
      (Nat.lt_succ_self _)).continuation =
      let post := Encoder.Annulus.postInversion annulus residualNonzero
      let normalized := Encoder.Annulus.normalizeLoop post.frac
        (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
      let block : Block :=
        ⟨.regular, normalized.exponent,
          ComplexContinuedFraction.Encoding.Sector.select normalized.annulus.frac.value⟩
      block :: (Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel (GaussianInt.normNat annulus.frac.denominator)
        normalized.annulus normalized.measure_lt).continuation := by
  rw [Encoder.Annulus.Blocks.encodeAnnulusBlocksFuel]
  rw [dif_neg (Nat.lt_irrefl _), dif_neg residualNonzero]
end Purelib.Data.CCL.Encoding.Encoder.Annulus.Blocks

end
