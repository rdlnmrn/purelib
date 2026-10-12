module
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Scale
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Addition.Bounds
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

open Purelib.Approximation.Rational.Geometric.Scale (quarterRadius_sum_scale)

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
/-- Add two quadratic traces at the same increment sequence.

Certificates are added pointwise. The new geometric scale is twice the sum of the original scales, and the new center
bound is twice the sum of the original bounds; the input increment sequence is retained. -/
def add {increment : Nat → Canonical}
  (left right : Trace increment) :
    Trace increment :=
  { certificate := fun index =>
      (left.certificate index).add (right.certificate index)
    errorScale := 2 * (left.errorScale + right.errorScale)
    errorScale_nonneg :=
      Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
    increment_later_close := by
      intro earlier later order
      calc
        Canonical.normSq (increment later - increment earlier) ≤
            Rational.Geometric.Basic.quarterRadius
              left.errorScale earlier := left.increment_later_close order
        _ ≤ 2 *
            (Rational.Geometric.Basic.quarterRadius
                left.errorScale earlier +
              Rational.Geometric.Basic.quarterRadius
                right.errorScale earlier) :=
          Purelib.Data.Rat.Fraction.Order.le_twice_sum_of_nonneg _ _
            (Rational.Geometric.Basic.quarterRadius_nonneg
              left.errorScale_nonneg earlier)
            (Rational.Geometric.Basic.quarterRadius_nonneg
              right.errorScale_nonneg earlier)
        _ = Rational.Geometric.Basic.quarterRadius
              (2 * (left.errorScale + right.errorScale)) earlier :=
          (quarterRadius_sum_scale _ _ _).symm
    base_later_close := by
      intro earlier later order
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_movement_le _ _ _ _ _ _
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using left.base_later_close order) (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.base_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    output_later_close := by
      intro earlier later order
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_movement_le _ _ _ _ _ _
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using left.output_later_close order)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.output_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    slope_later_close := by
      intro earlier later order
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_movement_le _ _ _ _ _ _
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using left.slope_later_close order) (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.slope_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    remainder_later_close := by
      intro earlier later order
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact (Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_movement_le _ _ _ _ _ _
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using left.remainder_later_close order)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.remainder_later_close order)).trans_eq
          (quarterRadius_sum_scale _ _ _).symm
    centerBound := 2 * (left.centerBound + right.centerBound)
    centerBound_nonneg :=
      Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
    increment_bounded := by
      intro index
      exact (left.increment_bounded index).trans
        (Purelib.Data.Rat.Fraction.Order.le_twice_sum_of_nonneg _ _ left.centerBound_nonneg
          right.centerBound_nonneg)
    base_bounded := by
      intro index
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_bounded _ _ _ _ (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using left.base_bounded index)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.base_bounded index)
    output_bounded := by
      intro index
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_bounded _ _ _ _ (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using left.output_bounded index)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.output_bounded index)
    slope_bounded := by
      intro index
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_bounded _ _ _ _ (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using left.slope_bounded index)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.slope_bounded index)
    remainder_bounded := by
      intro index
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Purelib.Data.Gaussian.Norm.Addition.Bounds.sum_bounded _ _ _ _ (by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using left.remainder_bounded index)
        (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.remainder_bounded index) }

open Purelib.Data
/-- Negate every displayed certificate while keeping the common increment sequence.

The geometric error scale and center bound are retained exactly. Negation preserves the quadrance estimates for each
changed certificate field. -/
def neg {increment : Nat → Canonical}
  (trace : Trace increment) :
    Trace increment :=
  { certificate := fun index => (trace.certificate index).neg
    errorScale := trace.errorScale
    errorScale_nonneg := trace.errorScale_nonneg
    increment_later_close := trace.increment_later_close
    base_later_close := by
      intro earlier later order
      change Canonical.normSq
        (-(trace.certificate later).base -
          -(trace.certificate earlier).base) ≤ _
      have identity :
          -(trace.certificate later).base -
              -(trace.certificate earlier).base =
            -((trace.certificate later).base -
              (trace.certificate earlier).base) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
            ring1
      rw [identity, Canonical.normSq_neg]
      exact trace.base_later_close order
    output_later_close := by
      intro earlier later order
      change Canonical.normSq
        (-(trace.certificate later).output -
          -(trace.certificate earlier).output) ≤ _
      have identity :
          -(trace.certificate later).output -
              -(trace.certificate earlier).output =
            -((trace.certificate later).output -
              (trace.certificate earlier).output) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
            ring1
      rw [identity, Canonical.normSq_neg]
      exact trace.output_later_close order
    slope_later_close := by
      intro earlier later order
      change Canonical.normSq
        (-(trace.certificate later).slope -
          -(trace.certificate earlier).slope) ≤ _
      have identity :
          -(trace.certificate later).slope -
              -(trace.certificate earlier).slope =
            -((trace.certificate later).slope -
              (trace.certificate earlier).slope) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
            ring1
      rw [identity, Canonical.normSq_neg]
      exact trace.slope_later_close order
    remainder_later_close := by
      intro earlier later order
      change Canonical.normSq
        (-(trace.certificate later).remainder -
          -(trace.certificate earlier).remainder) ≤ _
      have identity :
          -(trace.certificate later).remainder -
              -(trace.certificate earlier).remainder =
            -((trace.certificate later).remainder -
              (trace.certificate earlier).remainder) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
            ring1
      rw [identity, Canonical.normSq_neg]
      exact trace.remainder_later_close order
    centerBound := trace.centerBound
    centerBound_nonneg := trace.centerBound_nonneg
    increment_bounded := trace.increment_bounded
    base_bounded := by
      intro index
      change Canonical.normSq (-(trace.certificate index).base) ≤ trace.centerBound
      rw [Canonical.normSq_neg]
      exact trace.base_bounded index
    output_bounded := by
      intro index
      change Canonical.normSq (-(trace.certificate index).output) ≤ trace.centerBound
      rw [Canonical.normSq_neg]
      exact trace.output_bounded index
    slope_bounded := by
      intro index
      change Canonical.normSq (-(trace.certificate index).slope) ≤ trace.centerBound
      rw [Canonical.normSq_neg]
      exact trace.slope_bounded index
    remainder_bounded := by
      intro index
      change Canonical.normSq (-(trace.certificate index).remainder) ≤ trace.centerBound
      rw [Canonical.normSq_neg]
      exact trace.remainder_bounded index }

/-- Each certificate of an added trace is the sum of the two original certificates. -/
@[simp] theorem add_certificate {increment : Nat →
  Canonical}
    (left right : Trace increment) (index : Nat) :
    (add left right).certificate index =
      (left.certificate index).add (right.certificate index) := rfl
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
