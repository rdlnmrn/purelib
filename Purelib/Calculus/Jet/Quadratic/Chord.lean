module

public import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Geometry.Rational.Affine
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Chord deviation from two original quadratic certificates

The two original certificates retain their separate increment indices and
all displayed data. Exact base/slope agreement and a scalar increment law
cancel the common affine part. Their actual remainder bounds then pay the
short output's distance from the chord of the full displayed output.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational

variable {increment shortIncrement : Canonical} {fraction : Rational}
variable (full : Certificate increment) (short : Certificate shortIncrement)

/-- The original two remainders give the exact chord residual when their displayed affine terms agree.

The actual short increment is retained as its own index. Its equality to
one real scalar multiple of the full increment does not rebuild or reindex
either certificate or any of its displayed output/remainder data.
-/
theorem chord_remainder_eq (scaled : shortIncrement = Gaussian.Cast.Path.ofCoordinate fraction * increment)
    (base_eq : short.base = full.base) (slope_eq : short.slope = full.slope) :
    short.output - Affine.line full.base (full.output - full.base) fraction =
      short.remainder - Gaussian.Cast.Path.ofCoordinate fraction * full.remainder := by
  have linear : shortIncrement * short.slope =
      (Gaussian.Cast.Path.ofCoordinate fraction * increment) * full.slope :=
    congrArg₂ (fun left right : Canonical => left * right) scaled slope_eq
  have terms : short.output - short.base - shortIncrement * short.slope =
      short.output - full.base - (Gaussian.Cast.Path.ofCoordinate fraction * increment) * full.slope :=
    congrArg₂ (fun base linear : Canonical => short.output - base - linear) base_eq linear
  have shortExpansion := terms.symm.trans short.expansion
  have algebra : short.output - Affine.line full.base (full.output - full.base) fraction =
      (short.output - full.base - (Gaussian.Cast.Path.ofCoordinate fraction * increment) * full.slope) -
        Gaussian.Cast.Path.ofCoordinate fraction * (full.output - full.base - increment * full.slope) := by
    unfold Affine.line
    ring1
  exact algebra.trans (congrArg₂ (fun first last : Canonical =>
    first - Gaussian.Cast.Path.ofCoordinate fraction * last) shortExpansion full.expansion)

/-- Original quadratic factors bound the actual short output's deviation from the original full chord.

Both original factors are bounded by the stated nonnegative ceiling. A
real scalar between zero and one contracts each original increment and
remainder norm. The retained exact remainder identity gives four times
that ceiling as a squared-increment-squared chord error bound.
-/
theorem chord_error_le (scaled : shortIncrement = Gaussian.Cast.Path.ofCoordinate fraction * increment)
    (base_eq : short.base = full.base) (slope_eq : short.slope = full.slope)
    {ceiling : Rational} (fullFactor : full.factor ≤ ceiling) (partialFactor : short.factor ≤ ceiling)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Norm.Basic.normSq (short.output - Affine.line full.base (full.output - full.base) fraction) ≤
      4 * ceiling * Norm.Basic.normSq increment ^ 2 := by
  have ceilingNonnegative := full.factor_nonneg.trans fullFactor
  have scalarNorm : Norm.Basic.normSq (Gaussian.Cast.Path.ofCoordinate fraction) = fraction ^ 2 := by
    change fraction ^ 2 + (0 : Rational) ^ 2 = fraction ^ 2
    ring1
  have fractionSquare : fraction ^ 2 ≤ (1 : Rational) :=
    (Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2).trans_eq (by ring1)
  have incrementBound : Norm.Basic.normSq shortIncrement ≤ Norm.Basic.normSq increment := by
    rewrite [scaled, Norm.Basic.normSq_mul, scalarNorm]
    exact (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct fractionSquare
      (Norm.Basic.normSq_nonneg increment)).trans_eq (Field.one_mul _)
  have incrementSquared := Order.Arithmetic.pow_le_pow_direct
    (Norm.Basic.normSq_nonneg shortIncrement) incrementBound 2
  have fullOriginal : Norm.Basic.normSq full.remainder ≤ full.factor * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
    exact full.remainder_le
  have fullBound : Norm.Basic.normSq full.remainder ≤ ceiling * Norm.Basic.normSq increment ^ 2 :=
    fullOriginal.trans (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct fullFactor
      (Order.Arithmetic.sq_nonneg_direct _))
  have partialOriginal : Norm.Basic.normSq short.remainder ≤
      short.factor * Norm.Basic.normSq shortIncrement ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
    exact short.remainder_le
  have partialBound : Norm.Basic.normSq short.remainder ≤ ceiling * Norm.Basic.normSq increment ^ 2 :=
    partialOriginal.trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct partialFactor
        (Order.Arithmetic.sq_nonneg_direct _)).trans
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct incrementSquared ceilingNonnegative))
  have scaledBound : Norm.Basic.normSq (Gaussian.Cast.Path.ofCoordinate fraction * full.remainder) ≤
      ceiling * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Norm.Basic.normSq_mul, scalarNorm]
    exact ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct fractionSquare
      (Norm.Basic.normSq_nonneg full.remainder)).trans_eq (Field.one_mul _)).trans fullBound
  rewrite [full.chord_remainder_eq short scaled base_eq slope_eq]
  exact ((Norm.Bounds.normSq_sub_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct partialBound scaledBound)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))).trans_eq (by ring1)

/-- A nonzero increment divides the retained quadratic remainder into an explicit first-difference slope error.

The original certificate supplies the exact numerator and its fourth-order
quadrance payment. Cancellation uses the same nonzero increment and its
positive quadrance; no derivative or limiting equality is assumed.
-/
theorem differenceQuotient_le {increment : Canonical}
    (certificate : Certificate increment) (nonzero : increment ≠ 0) :
    Canonical.normSq ((certificate.output - certificate.base) / increment - certificate.slope) ≤
      certificate.factor * Canonical.normSq increment := by
  have numerator : increment *
      ((certificate.output - certificate.base) / increment - certificate.slope) = certificate.remainder := by
    change increment * ((certificate.output - certificate.base) * increment⁻¹ - certificate.slope) = _
    calc
      _ = (increment * increment⁻¹) * (certificate.output - certificate.base) -
          increment * certificate.slope := by ring1
      _ = certificate.output - certificate.base - increment * certificate.slope := by
        rewrite [Canonical.mul_inv_cancel increment nonzero, Canonical.one_mul]
        rfl
      _ = certificate.remainder := certificate.expansion
  have positive : (0 : Rational) < Canonical.normSq increment :=
    (Norm.Basic.normSq_pos nonzero).trans_eq (Norm.Basic.normSq_eq_canonical increment)
  have scaled := (congrArg Canonical.normSq numerator).trans_le certificate.remainder_le
  rewrite [Canonical.normSq_mul] at scaled
  have multiplied :
      Canonical.normSq ((certificate.output - certificate.base) / increment - certificate.slope) *
          Canonical.normSq increment ≤
        (certificate.factor * Canonical.normSq increment) * Canonical.normSq increment :=
    (Field.mul_comm _ _).trans_le (scaled.trans_eq (by ring1))
  exact Order.Arithmetic.le_of_mul_le_mul_right_direct multiplied positive

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate

end
