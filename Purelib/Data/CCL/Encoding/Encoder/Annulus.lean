module
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Multiplication
import Purelib.Algebra.NatCast

public import Purelib.Data.CCL.Encoding.Block.Descent
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.GaussianInt.Cancellation
public import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.SectorBlock.Tail

import Purelib.Data.Gaussian.Power
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
public import Purelib.Data.GaussianInt.Constants.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Power
import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

-- Preserve the existing nominal `Annulus.Annulus` record and its field API.

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
set_option genInjectivity false in
/-- Retain a displayed Gaussian fraction with squared norm between one and two.

The closed-band witness belongs to that exact fraction readback; the displayed integer numerator and denominator remain
available for norm descent. -/
structure Annulus where
  /-- The retained displayed Gaussian-integer fraction. -/ frac :
    GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias
  /-- Evidence that this fraction's exact value lies in the closed unit-to-two squared-norm band. -/ band :
    ComplexContinuedFraction.Encoding.Sector.Band frac.value

constructive_injectivity Annulus

namespace Annulus

end Annulus
end Purelib.Data.CCL.Encoding.Encoder

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
set_option genInjectivity false in
/-- Retain the loop normalization exponent and annulus with exact numerator, denominator and measure relations.

The numerator equals the post-inversion numerator and the denominator is the retained integer gamma power times the
original denominator. Its natural norm is strictly below the supplied old measure. -/
structure LoopResult (post : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (oldMeasure : Nat) where
  /-- The exact normalization exponent returned by the retained binary scan. -/ exponent : Nat
  /-- The exact normalized displayed fraction and its annulus witness. -/ annulus : Annulus
  /-- The normalized numerator equals the exact post-inversion numerator. -/ num_eq : annulus.frac.numerator =
    post.numerator
  /-- The normalized denominator is the retained integer gamma power times the original post-inversion denominator. -/
    den_eq : annulus.frac.denominator = GaussianInt.natPow GaussianInt.gammaInt exponent * post.denominator
  /-- The normalized denominator norm is strictly below the retained old measure. -/ measure_lt : GaussianInt.normNat
    annulus.frac.denominator < oldMeasure

constructive_injectivity LoopResult

namespace LoopResult

end LoopResult
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
set_option genInjectivity false in
/-- Retain the displayed post-inversion fraction and strict denominator-norm descent from the original annulus.

The new numerator is the old denominator; the new denominator is integer gamma times the exact selected-sector residual.
Both identities and the strict descent refer to those retained fields. -/
structure PostInversion (old : Annulus) where
  /-- The retained displayed Gaussian-integer fraction. -/ frac :
    GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias
  /-- The post-inversion numerator equals the original annulus denominator. -/ num_eq : frac.numerator =
    old.frac.denominator
  /-- The post-inversion denominator is integer gamma times the exact selected-sector residual. -/ den_eq :
    frac.denominator = GaussianInt.gammaInt *
    (old.frac.numerator - Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select old.frac.value) *
      old.frac.denominator)
  /-- The post-inversion denominator norm is strictly below the original annulus denominator norm. -/ den_descent :
    GaussianInt.normNat frac.denominator < GaussianInt.normNat old.frac.denominator

constructive_injectivity PostInversion

namespace PostInversion

end PostInversion
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained numerator and denominator norm bounds place the fraction in the initial half-open annulus. -/
private theorem frac_entry_of_bounds (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (lower : GaussianInt.normNat fraction.denominator ≤ GaussianInt.normNat fraction.numerator)
    (upper : GaussianInt.normNat fraction.numerator < 2 * GaussianInt.normNat fraction.denominator) :
    ComplexContinuedFraction.Encoding.Sector.Entry fraction.value := by
  rw [ComplexContinuedFraction.Encoding.Sector.Entry, ← Norm.Basic.normSq_eq_canonical,
    GaussianInt.Fraction.normSq_value]
  have denominatorPositive :
      (0 : Fraction.Basic.Rational) < (GaussianInt.normNat fraction.denominator : Nat) :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos fraction.denominatorNonzero)
  constructor
  · apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
    rw [Fraction.Field.one_mul]
    exact Fraction.Cast.Order.natCast_le_direct lower
  · apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
    have castUpper := Fraction.Cast.Order.natCast_lt_direct upper
    simpa only [NatCast.mul, Nat.cast_ofNat] using castUpper
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained strict lower and weak upper norm bounds place the fraction in the loop half-open annulus. -/
private theorem frac_loop_of_bounds (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (lower : GaussianInt.normNat fraction.denominator < GaussianInt.normNat fraction.numerator)
    (upper : GaussianInt.normNat fraction.numerator ≤ 2 * GaussianInt.normNat fraction.denominator) :
    ComplexContinuedFraction.Encoding.Sector.Loop fraction.value := by
  rw [ComplexContinuedFraction.Encoding.Sector.Loop, ← Norm.Basic.normSq_eq_canonical,
    GaussianInt.Fraction.normSq_value]
  have denominatorPositive :
      (0 : Fraction.Basic.Rational) < (GaussianInt.normNat fraction.denominator : Nat) :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos fraction.denominatorNonzero)
  constructor
  · apply (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).2
    rw [Fraction.Field.one_mul]
    exact Fraction.Cast.Order.natCast_lt_direct lower
  · apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    have castUpper := Fraction.Cast.Order.natCast_le_direct upper
    simpa only [NatCast.mul, Nat.cast_ofNat] using castUpper
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Normalize the retained post-inversion fraction by an exact integer gamma power while preserving measure descent.

The original numerator norm equals the supplied old measure and strictly exceeds denominator norm. The retained binary
loop scan determines the exponent; only the denominator is scaled, and all original representation identities are
stored. -/
@[expose] def normalizeLoop (post : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias) (oldMeasure : Nat)
    (postStrict : GaussianInt.normNat post.denominator < GaussianInt.normNat post.numerator)
    (numeratorMeasure : GaussianInt.normNat post.numerator = oldMeasure) :
    CCL.Encoding.Encoder.Annulus.LoopResult post oldMeasure := by
  let scan := BinaryNormalization.loop
    (GaussianInt.normNat post.numerator) (GaussianInt.normNat post.denominator)
    (GaussianInt.normNat_pos post.denominatorNonzero) postStrict
  let denominator := GaussianInt.natPow GaussianInt.gammaInt scan.exponent * post.denominator
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero
      (GaussianInt.natPow_ne_zero GaussianInt.gammaInt (by decide) scan.exponent) post.denominatorNonzero
  let normalized : GaussianInt.Fraction := ⟨post.numerator, denominator, denominatorNonzero⟩
  have denominatorNorm :
      GaussianInt.normNat denominator = 2 ^ scan.exponent * GaussianInt.normNat post.denominator := by
    rw [show denominator = _ from rfl, GaussianInt.normNat_mul, GaussianInt.normNat_gammaInt_pow]
  have lower : GaussianInt.normNat normalized.denominator < GaussianInt.normNat normalized.numerator := by
    dsimp only [normalized]
    rw [denominatorNorm]
    exact scan.lower
  have upper : GaussianInt.normNat normalized.numerator ≤ 2 * GaussianInt.normNat normalized.denominator := by
    dsimp only [normalized]
    rw [denominatorNorm]
    calc
      GaussianInt.normNat post.numerator ≤
          2 ^ (scan.exponent + 1) * GaussianInt.normNat post.denominator := scan.upper
      _ = 2 * (2 ^ scan.exponent * GaussianInt.normNat post.denominator) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ scan.exponent) 2, Multiplication.mul_assoc]
  let loop : ComplexContinuedFraction.Encoding.Sector.Loop normalized.value := by
    rw [ComplexContinuedFraction.Encoding.Sector.Loop, ← Norm.Basic.normSq_eq_canonical,
      GaussianInt.Fraction.normSq_value]
    have denominatorPositive :
        (0 : Fraction.Basic.Rational) < (GaussianInt.normNat normalized.denominator : Nat) :=
      Fraction.Cast.Order.natCast_pos_direct
        (GaussianInt.normNat_pos normalized.denominatorNonzero)
    constructor
    · apply (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).2
      rw [Fraction.Field.one_mul]
      exact Fraction.Cast.Order.natCast_lt_direct lower
    · apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
      have castUpper := Fraction.Cast.Order.natCast_le_direct upper
      simpa only [NatCast.mul, Nat.cast_ofNat] using castUpper
  refine ⟨scan.exponent, ⟨normalized, ⟨loop.1.le, loop.2⟩⟩, rfl, rfl, ?_⟩
  calc
    GaussianInt.normNat normalized.denominator < GaussianInt.normNat normalized.numerator := lower
    _ = GaussianInt.normNat post.numerator := rfl
    _ = oldMeasure := numeratorMeasure
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Construct the displayed inverse gamma-scaled residual fraction with strict denominator-norm descent.

The exact selected integral residual is nonzero. Retain the old denominator as numerator and integer gamma times that
residual as denominator, using the original sector contraction to certify descent. -/
@[expose] def postInversion (old : Annulus)
    (residualNonzero :
      old.frac.numerator - Sector.Integral.sectorInt (ComplexContinuedFraction.Encoding.Sector.select old.frac.value) *
        old.frac.denominator ≠ 0) : CCL.Encoding.Encoder.Annulus.PostInversion old := by
  let sector := ComplexContinuedFraction.Encoding.Sector.select old.frac.value
  let residual := old.frac.numerator - Sector.Integral.sectorInt sector * old.frac.denominator
  have residualNonzero' : residual ≠ 0 := by
    simpa only [residual, sector] using residualNonzero
  let denominator := GaussianInt.gammaInt * residual
  have denominatorNonzero : denominator ≠ 0 :=
    GaussianInt.mul_ne_zero (by decide) residualNonzero'
  let next : GaussianInt.Fraction := ⟨old.frac.denominator, denominator, denominatorNonzero⟩
  have descent := CCL.Encoding.Block.Descent.inversion_stage_descent
    old.frac.denominatorGaussianNonzero old.band sector
    (ComplexContinuedFraction.Encoding.Sector.select_spec old.frac.value old.band.1)
    old.frac.value_mul_denominator.symm
  have denominatorMap : GaussianInt.toGaussian denominator =
      Basic.Canonical.gamma *
        (GaussianInt.toGaussian old.frac.numerator - sector.rep *
          GaussianInt.toGaussian old.frac.denominator) := by
    dsimp only [denominator, residual]
    rw [GaussianInt.toGaussian_mul, GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul,
      GaussianInt.toGaussian_gammaInt, Sector.Integral.toGaussian_sectorInt]
  rw [← denominatorMap, GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian] at descent
  exact
    ⟨next, rfl, rfl,
      Fraction.Cast.Order.natCast_lt_iff_direct.mp descent⟩
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- The retained post-inversion fraction is a compatible tail modeling the original annulus value. -/
private theorem post_compatible (annulus : Annulus)
    (post : CCL.Encoding.Encoder.Annulus.PostInversion annulus) :
    SectorBlock.Tail.SourceEncodingEncoderCompatibleTailAlias (ComplexContinuedFraction.Encoding.Sector.select
      annulus.frac.value)
      post.frac.value annulus.frac.value := by
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
  exact leftScaled.trans rightScaled.symm
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end

section
public section
namespace Purelib.Data.CCL.Encoding.Encoder.Annulus

open Purelib.Algebra

/-! ## Completed-block realization data -/

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- A zero displayed residual makes the annulus fraction value equal the retained sector representative. -/
private theorem terminal_value_eq_rep (annulus : Annulus) (sector :
  Sector.Basic.SourceEncodingEncoderSectorAlias)
    (residualZero :
      annulus.frac.numerator - Sector.Integral.sectorInt sector * annulus.frac.denominator = 0) :
    annulus.frac.value = sector.rep := by
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
end Purelib.Data.CCL.Encoding.Encoder.Annulus

end
