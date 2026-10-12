module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Quadratic.Identity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

open Purelib.Approximation in
open Purelib.Data in
/-- Build an identity trace from an approximation with a specified geometric radius schedule.

The increment and output at each index are the source sample, while the base and remainder are zero and the slope is
one. The trace retains the supplied error scale and uses one plus the source center bound to bound all five fields. -/
def identityOfGeometricApproximation (source :
  Gaussian.Sequence.ApproximationData)
    (scale : Rat.Fraction.Rational) (scaleNonnegative : 0 ≤ scale)
    (radius_eq : ∀ index, source.radiusSq index =
      Rational.Geometric.Basic.quarterRadius scale index) :
    Trace source.sample where
  certificate index := Trace.identityCertificate (source.sample index)
  errorScale := scale
  errorScale_nonneg := scaleNonnegative
  increment_later_close := by
    intro earlier later order
    rw [← radius_eq earlier]
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using source.later_close order
  base_later_close := by
    intro earlier later order
    change Canonical.normSq ((0 : Canonical) - 0) ≤ _
    rw [_root_.sub_self, Canonical.normSq_zero]
    exact Rational.Geometric.Basic.quarterRadius_nonneg
      scaleNonnegative earlier
  output_later_close := by
    intro earlier later order
    change Canonical.normSq
      (source.sample later - source.sample earlier) ≤ _
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      (source.later_close order).trans_eq (radius_eq earlier)
  slope_later_close := by
    intro earlier later order
    change Canonical.normSq ((1 : Canonical) - 1) ≤ _
    rw [_root_.sub_self, Canonical.normSq_zero]
    exact Rational.Geometric.Basic.quarterRadius_nonneg
      scaleNonnegative earlier
  remainder_later_close := by
    intro earlier later order
    change Canonical.normSq ((0 : Canonical) - 0) ≤ _
    rw [_root_.sub_self, Canonical.normSq_zero]
    exact Rational.Geometric.Basic.quarterRadius_nonneg
      scaleNonnegative earlier
  centerBound := 1 + source.centerBound
  centerBound_nonneg := add_nonneg (by decide) source.centerBound_nonneg
  increment_bounded index := by
    have bounded := (source.sample_bounded index).trans
      (le_add_of_nonneg_left (by decide : (0 : Rat.Fraction.Rational) ≤ 1))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bounded
  base_bounded index := by
    change Canonical.normSq (0 : Canonical) ≤ 1 + source.centerBound
    rw [Canonical.normSq_zero]
    exact add_nonneg (by decide) source.centerBound_nonneg
  output_bounded index := by
    change Canonical.normSq (source.sample index) ≤ _
    have bounded := (source.sample_bounded index).trans
      (le_add_of_nonneg_left (by decide : (0 : Rat.Fraction.Rational) ≤ 1))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bounded
  slope_bounded index := by
    change Canonical.normSq (1 : Canonical) ≤ 1 + source.centerBound
    rw [Canonical.normSq_one]
    exact le_add_of_nonneg_right source.centerBound_nonneg
  remainder_bounded index := by
    change Canonical.normSq (0 : Canonical) ≤ 1 + source.centerBound
    rw [Canonical.normSq_zero]
    exact add_nonneg (by decide) source.centerBound_nonneg
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
