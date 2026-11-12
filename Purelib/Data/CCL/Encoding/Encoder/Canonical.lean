module

public import Purelib.Data.CCL.Encoding.Encoder.Integral
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Word
import Purelib.Data.CCL.Encoding.Parser.Header
import Purelib.Data.CCL.Encoding.Block.Syntax
import Purelib.Data.CCL.Encoding.Block.Semantics
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.SectorBlock.Tail

/-!
# The original integral encoder follows the original canonical parser

The proof uses the original normalization records and exact continuation
blocks. Every returned full word has an affine represented terminal precursor;
its last sector bit changes the tail to projective infinity.
-/

namespace Purelib.Data.CCL.Encoding.Encoder.Integral

open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry.Projective

/-- A zero selected residual leaves only the original selected three-bit sector word. -/
private theorem tail_word_of_zero (annulus : Annulus)
    (zero : annulus.frac.numerator -
      Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator = 0) :
    (encodeTail annulus).word = (Sector.select annulus.frac.value).code := by
  rewrite [encodeTail_word_eq,
    Annulus.Blocks.encodeAnnulusBlocks_continuation_of_eq annulus zero]
  exact Append.append_nil _

/-- A nonzero selected residual emits the original sector and normalization header before its original next word. -/
private theorem tail_word_of_nonzero (annulus : Annulus)
    (nonzero : annulus.frac.numerator -
      Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator ≠ 0) :
    (encodeTail annulus).word =
      let post := Annulus.postInversion annulus nonzero
      let normalized := Annulus.normalizeLoop post.frac
        (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
      (Sector.select annulus.frac.value).code ++
        ((List.replicate normalized.exponent true ++ [false]) ++
          (encodeTail normalized.annulus).word) := by
  rewrite [encodeTail_word_eq,
    Annulus.Blocks.encodeAnnulusBlocks_continuation_of_ne annulus nonzero]
  dsimp only
  rewrite [encodeTail_word_eq]
  simp only [Block.Basic.rawWord, Block.word, Block.Syntax.regularWord,
    Append.append_assoc, -eq_self, -iff_self]
  rfl

/-- Consume the original annulus recursion from an already represented zero-bit sector phase. -/
private theorem tail_terminal (annulus : Annulus) (stem : List Bool) (input before : Basic.Canonical)
    (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (phase : (Parser.State.parse stem).phase = .sector kind exponent .zero)
    (represented : Parser.Semantics.State.Represents (Parser.State.parse stem) input before)
    (radial : Parser.Semantics.Basic.radialBracket kind exponent before)
    (normalizedValue : Parser.Semantics.Basic.normalizedValue kind exponent before = annulus.frac.value) :
    Parser.Terminal.Word.Represents (stem ++ (encodeTail annulus).word) input := by
  let sector := Sector.select annulus.frac.value
  rcases Sector.Code.sector_eq_bits sector with ⟨first, second, third, sectorEq⟩
  have codeEq : sector.code = [first, second, third] :=
    (congrArg Sector.code sectorEq).trans (Sector.Code.sectorOfBits_code first second third)
  have full : Parser.Semantics.Basic.fullBlockHolds kind exponent
      (Sector.Code.sectorOfBits first second third) before := by
    refine ⟨radial, ?_⟩
    rewrite [normalizedValue, ← sectorEq]
    exact Sector.select_spec annulus.frac.value annulus.band.1
  let two := stem ++ [first, second]
  have parseTwo : Parser.State.parse two =
      Parser.State.step (Parser.State.step (Parser.State.parse stem) first) second := by
    rewrite [Parser.State.parse_append]
    rfl
  have phaseTwo : (Parser.State.parse two).phase =
      .sector kind exponent (.two first second) := by
    rewrite [parseTwo]
    rewrite [Parser.State.step_phase, Parser.State.step_phase, phase]
    rfl
  have twoRepresents : Parser.Semantics.State.Represents (Parser.State.parse two) input before :=
    parseTwo.symm ▸ Parser.State.represents_sectorTwo represented kind exponent first second third phase full
  by_cases zero : annulus.frac.numerator -
      Sector.Integral.sectorInt (Sector.select annulus.frac.value) * annulus.frac.denominator = 0
  · refine ⟨two, kind, exponent, first, second, third, before, ?_, phaseTwo, twoRepresents, ?_⟩
    · rewrite [tail_word_of_zero annulus zero]
      change stem ++ sector.code = two ++ [third]
      rewrite [codeEq]
      exact (Append.append_assoc stem [first, second] [third]).symm
    · exact normalizedValue.trans
        ((Annulus.terminal_value_eq_rep annulus sector zero).trans (congrArg Sector.rep sectorEq))
  · let post := Annulus.postInversion annulus zero
    let normalized := Annulus.normalizeLoop post.frac
      (GaussianInt.normNat annulus.frac.denominator) post.den_descent rfl
    have compatible := Annulus.post_compatible annulus post
    have residualNonzero : Parser.Semantics.Basic.normalizedValue kind exponent before -
        (Sector.Code.sectorOfBits first second third).rep ≠ 0 := by
      rewrite [normalizedValue, ← sectorEq]
      exact compatible.residual_nonzero
    have inverseEq : post.frac.value =
        (Basic.Canonical.gamma *
          (Parser.Semantics.Basic.normalizedValue kind exponent before -
            (Sector.Code.sectorOfBits first second third).rep))⁻¹ := by
      rewrite [normalizedValue, ← sectorEq]
      exact compatible.tail_eq_inverse
    have blockEq : Homography.Basic.homographic
        (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third))
          post.frac.value = before := by
      rewrite [inverseEq]
      exact Block.Semantics.block_homographic_inverse kind exponent
        (Sector.Code.sectorOfBits first second third) before residualNonzero
    have blockDenominator : Homography.Basic.denominator
        (Block.Matrix.blockMatrix kind exponent (Sector.Code.sectorOfBits first second third))
          post.frac.value ≠ 0 := by
      rewrite [inverseEq]
      exact Block.Semantics.block_inverse_denominator_ne kind exponent
        (Sector.Code.sectorOfBits first second third) before residualNonzero
    have loopActive : Parser.Semantics.Basic.activeHolds (.loopUnary 0) post.frac.value := by
      change (1 : Rat.Fraction.Rational) < Basic.Canonical.normSq post.frac.value
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact compatible.tail_norm_gt_one
    let after := stem ++ sector.code
    have parseAfter : Parser.State.parse after =
        Parser.State.completeSector (Parser.State.parse two) kind exponent first second third := by
      rewrite [Parser.State.parse_append]
      rewrite [codeEq]
      change Parser.State.step
        (Parser.State.step (Parser.State.step (Parser.State.parse stem) first) second) third = _
      rewrite [← parseTwo]
      exact Parser.Semantics.Transition.step_eq_completeSector (Parser.State.parse two)
        kind exponent first second third phaseTwo
    have afterRepresents : Parser.Semantics.State.Represents (Parser.State.parse after) input post.frac.value :=
      parseAfter.symm ▸ Parser.Semantics.Transition.completeSector_represents_next (Parser.State.parse two)
        kind exponent first second third input before post.frac.value phaseTwo twoRepresents
        blockEq blockDenominator full loopActive
    have afterPhase : (Parser.State.parse after).phase = .loopUnary 0 := by
      rewrite [parseAfter]
      rfl
    let nextStem := after ++ (List.replicate normalized.exponent true ++ [false])
    have parseNext : Parser.State.parse nextStem =
        ⟨.sector .loop normalized.exponent .zero,
          (Parser.State.parse after).matrix, (Parser.State.parse after).history⟩ := by
      rewrite [Parser.State.parse_append]
      exact Parser.State.foldl_loop_header (Parser.State.parse after) normalized.exponent afterPhase
    have nextRepresents : Parser.Semantics.State.Represents (Parser.State.parse nextStem) input post.frac.value := by
      rewrite [parseNext]
      apply Parser.State.represents_sectorZero afterRepresents .loop normalized.exponent
        (Sector.select normalized.annulus.frac.value) normalized.radialBracket
      rewrite [normalized.normalizedValue]
      exact Sector.select_spec normalized.annulus.frac.value normalized.annulus.band.1
    have nextPhase : (Parser.State.parse nextStem).phase = .sector .loop normalized.exponent .zero := by
      rewrite [parseNext]
      rfl
    have remainder := tail_terminal normalized.annulus nextStem input post.frac.value .loop normalized.exponent
      nextPhase nextRepresents normalized.radialBracket normalized.normalizedValue
    have wordEq : stem ++ (encodeTail annulus).word =
        nextStem ++ (encodeTail normalized.annulus).word := by
      rewrite [tail_word_of_nonzero annulus zero]
      change stem ++ (sector.code ++ ((List.replicate normalized.exponent true ++ [false]) ++
        (encodeTail normalized.annulus).word)) = _
      exact ((Append.append_assoc stem sector.code
        ((List.replicate normalized.exponent true ++ [false]) ++ (encodeTail normalized.annulus).word)).symm).trans
        (Append.append_assoc after (List.replicate normalized.exponent true ++ [false])
          (encodeTail normalized.annulus).word).symm
    exact wordEq.symm ▸ remainder
termination_by GaussianInt.normNat annulus.frac.denominator
decreasing_by exact normalized.measure_lt

/-- The exact cached initial normalization header reaches its original sector phase. -/
private theorem initial_phase {fraction : GaussianInt.Fraction}
    (initial : Normalization.InitialResult fraction) :
    Parser.State.parse initial.header =
      ⟨.sector initial.kind initial.exponent .zero,
        Parser.State.initialState.matrix, Parser.State.initialState.history⟩ := by
  have header := initial.headerSpec
  rcases initial.initial with high | low
  · rewrite [high] at header ⊢
    change initial.header = List.replicate initial.exponent true ++ [false] at header
    rewrite [header]
    exact Parser.State.foldl_initialHigh_header Parser.State.initialState initial.exponent rfl
      (initial.highPositive high)
  · rewrite [low] at header ⊢
    change initial.header = false :: (List.replicate initial.exponent true ++ [false]) at header
    rewrite [header]
    exact Parser.State.foldl_initialLow_header Parser.State.initialState initial.exponent rfl

/-- The original initial normalization and original annulus recursion produce a canonical terminal word. -/
private theorem initial_terminal {fraction : GaussianInt.Fraction}
    (initial : Normalization.InitialResult fraction) :
    Parser.Terminal.Word.Represents (initial.header ++ (encodeTail initial.annulus).word) fraction.value := by
  have original := Parser.Semantics.State.initialState_represents fraction.value
  have represented : Parser.Semantics.State.Represents
      (Parser.State.parse initial.header) fraction.value fraction.value := by
    rewrite [initial_phase initial]
    apply Parser.State.represents_sectorZero original initial.kind initial.exponent
      (Sector.select initial.annulus.frac.value) initial.radialBracket
    rewrite [initial.normalizedValue]
    exact Sector.select_spec initial.annulus.frac.value initial.annulus.band.1
  have phase : (Parser.State.parse initial.header).phase =
      .sector initial.kind initial.exponent .zero := by
    rewrite [initial_phase initial]
    rfl
  exact tail_terminal initial.annulus initial.header fraction.value fraction.value initial.kind initial.exponent
    phase represented initial.radialBracket initial.normalizedValue

/-- The original full integral encoder agrees with the original canonical parser on every admitted nonzero fraction.

Its exact complete word has a uniquely represented affine precursor at the
last two-bit sector phase. The final bit records that same normalized sector
at projective infinity. Unary headers, partial sectors and block transitions
retain the original half-open normalization decisions.
-/
public theorem encodeResult_terminal (fraction : GaussianInt.Fraction) (numeratorNonzero : fraction.numerator ≠ 0) :
    Parser.Terminal.Word.Represents (encodeResult fraction numeratorNonzero).word fraction.value := by
  unfold encodeResult
  split
  · exact initial_terminal (Normalization.initialHigh fraction numeratorNonzero ‹_›)
  · exact initial_terminal (Normalization.initialLow fraction numeratorNonzero (Nat.lt_of_not_ge ‹_›))

/-- Different displayed integral fractions with the same nonzero rational value have the same canonical full word. -/
public theorem encode_word_eq_of_value_eq (left right : GaussianInt.Fraction)
    (leftNonzero : left.numerator ≠ 0) (rightNonzero : right.numerator ≠ 0)
    (sameValue : left.value = right.value) :
    (encodeResult left leftNonzero).word = (encodeResult right rightNonzero).word :=
  Parser.Terminal.Word.unique (encodeResult_terminal left leftNonzero)
    (sameValue.symm ▸ encodeResult_terminal right rightNonzero)

end Purelib.Data.CCL.Encoding.Encoder.Integral
