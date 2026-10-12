module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Partition.Interval
public import Purelib.Integration.Partition.Unit.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Observed, cached exponential polynomial cells

Every cell retains its generated affine coefficient restriction and exact
integral sample.  The observations are actual later finite exponential
readings at displayed rational parameters; they are not evidence about an
unspecified integrand.  Endpoint observations make each generated list
nonempty, and the general constructor supports every displayed unit parameter.
-/

namespace Purelib.Integration.Partition.Affine

section
open Purelib.Data.Rat
open Purelib.Integration.Partition
/-- Map a local parameter affinely into the supplied interval's original endpoint coordinates. -/
def sourceParameter (interval : Integration.Partition.Interval)
  (localParameter :
  Fraction.Rational) : Fraction.Rational :=
  interval.start + (interval.finish - interval.start) * localParameter

/-- A local unit parameter maps into the unit interval when the retained source interval is valid. -/
theorem sourceParameter_bounds {interval : Integration.Partition.Interval}
  (valid :
  interval.Valid)
    {localParameter : Fraction.Rational} (nonnegative : 0 ≤ localParameter) (bounded : localParameter ≤ 1) :
    0 ≤ sourceParameter interval localParameter ∧ sourceParameter interval localParameter ≤ 1 := by
  have widthNonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct valid.2.1.le
  have scaledNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct widthNonnegative nonnegative
  have scaledBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded widthNonnegative
  unfold sourceParameter
  constructor
  · calc
      0 = (0 : Fraction.Rational) + 0 := by decide
      _ ≤ interval.start + (interval.finish - interval.start) * localParameter :=
        add_le_add valid.1 scaledNonnegative
  · calc
      interval.start + (interval.finish - interval.start) * localParameter ≤
          interval.start + (interval.finish - interval.start) * 1 :=
        add_le_add le_rfl scaledBound
      _ = interval.finish := by ring1
      _ ≤ 1 := valid.2.2

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Partition in
/-- Gaussian rational embedding preserves the exact affine source-parameter formula. -/
theorem parameter_sourceParameter (interval :
  Integration.Partition.Interval)
  (localParameter : Fraction.Rational) :
    RationalEmbedding.parameter (sourceParameter interval localParameter) =
      RationalEmbedding.parameter interval.start + (RationalEmbedding.parameter interval.finish -
        RationalEmbedding.parameter interval.start) *
        RationalEmbedding.parameter localParameter := by
  apply Basic.ext <;>
    simp only [RationalEmbedding.parameter, sourceParameter, Basic.add_re, Basic.add_im, Basic.sub_re,
      Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
end Purelib.Integration.Partition.Affine

end
