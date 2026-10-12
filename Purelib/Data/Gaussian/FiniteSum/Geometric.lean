module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Geometric.Quarter

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Gaussian.FiniteSum.Geometric

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A finite Gaussian sum with squared norms bounded by quarter-geometric decay has squared norm at most four times the
scale.

The pointwise hypothesis bounds term index by scale times one quarter to that index. Finite prefix induction shifts the
remaining family and its scale by one quarter, yielding a bound independent of the prefix length. -/
theorem sum_geometric_normSq_le (term : Nat → Basic.Canonical) :
    ∀ (count : Nat) (scale : Fraction.Rational), 0 ≤ scale →
      (∀ index, Data.Gaussian.Norm.Basic.normSq (term index) ≤
        scale * (1 / 4 : Fraction.Rational) ^ index) →
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Prefix.sum term count) ≤ 4 * scale := by
  intro count
  induction count generalizing term with
  | zero =>
    intro scale scaleNonnegative termBound
    rw [FiniteSum.Prefix.sum_zero, Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      scaleNonnegative
  | succ count inductionHypothesis =>
    intro scale scaleNonnegative termBound
    rw [FiniteSum.Prefix.sum_succ_front]
    have headBound : Data.Gaussian.Norm.Basic.normSq (term 0) ≤ scale := by
      simpa only [pow_zero, Fraction.Field.mul_one_direct] using
        termBound 0
    have quarterScaleNonnegative : 0 ≤ scale / 4 :=
      Fraction.Order.Field.div_nonneg_direct scaleNonnegative (by decide)
    have shiftedBound : ∀ index,
        Data.Gaussian.Norm.Basic.normSq (term (index + 1)) ≤
          (scale / 4) * (1 / 4 : Fraction.Rational) ^ index := by
      intro index
      calc
        Data.Gaussian.Norm.Basic.normSq (term (index + 1)) ≤
            scale * (1 / 4 : Fraction.Rational) ^ (index + 1) := termBound _
        _ = (scale / 4) * (1 / 4 : Fraction.Rational) ^ index :=
          Geometric.Quarter.geometric_scale_shift scale index
    have tailBound := inductionHypothesis
      (fun index => term (index + 1)) (scale / 4)
        quarterScaleNonnegative shiftedBound
    have tailBound' :
        Data.Gaussian.Norm.Basic.normSq (FiniteSum.Prefix.sum (fun index => term (index + 1)) count) ≤ scale := by
      calc
        Data.Gaussian.Norm.Basic.normSq (FiniteSum.Prefix.sum (fun index => term (index + 1)) count) ≤
            4 * (scale / 4) := tailBound
        _ = scale := Fraction.Compatibility.four_mul_quarter_scale scale
    calc
      Data.Gaussian.Norm.Basic.normSq
          (term 0 + FiniteSum.Prefix.sum (fun index => term (index + 1)) count) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (term 0) +
          Data.Gaussian.Norm.Basic.normSq (FiniteSum.Prefix.sum (fun index => term (index + 1)) count)) :=
            Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (scale + scale) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add headBound tailBound') (by decide)
      _ = 4 * scale := Fraction.Compatibility.two_double_scale scale
end Purelib.Data.Gaussian.FiniteSum.Geometric

end
