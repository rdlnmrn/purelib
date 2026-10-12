module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Order
public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Rational.Geometric.Order (quarterRadius_succ_le)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Local.Horner

open Purelib.Approximation.Gaussian.Sequence.Geometric

open Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
section Channel

/-- Apply the finite reduced complex-log Horner program at depth `index + 1` to a geometrically coherent channel in its
displayed `1/9` disk. -/
def reducedLogSample {source : Nat →
  Data.Gaussian.Basic.Canonical} (channel : Channel source)
    (disk : ∀ index, Data.Gaussian.Norm.Basic.normSq (source index) ≤ 1 / 9) :
    Channel (fun index =>
      Sample.sample (source index) (index + 1)) where
  errorScale := 2 *
    (5 + Sensitivity.sampleInputScale *
      channel.errorScale)
  errorScale_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          Sensitivity.sampleInputScale_nonneg
          channel.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have depthOrder : earlier + 1 ≤ later + 1 := by omega
    have truncationRaw :=
      Sample.sample_later_close
        (disk later) depthOrder
    have truncation :
        Data.Gaussian.Norm.Basic.normSq
            (Sample.sample (source later)
                (later + 1) -
              Sample.sample (source later)
                (earlier + 1)) ≤
          Geometric.Basic.quarterRadius 5 earlier := by
      calc
        _ ≤ 5 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := truncationRaw
        _ = Geometric.Basic.quarterRadius 5 (earlier + 1) :=
          (Geometric.Basic.quarterRadius_eq_mul_pow
            5 (earlier + 1)).symm
        _ ≤ Geometric.Basic.quarterRadius 5 earlier :=
          quarterRadius_succ_le 5 (by decide) earlier
    have inputEffectRaw :=
      Sensitivity.sample_input_close
        (disk later) (disk earlier) (earlier + 1)
    have inputEffect :
        Data.Gaussian.Norm.Basic.normSq
            (Sample.sample (source later)
                (earlier + 1) -
              Sample.sample (source earlier)
                (earlier + 1)) ≤
          Sensitivity.sampleInputScale *
            Geometric.Basic.quarterRadius
              channel.errorScale earlier :=
      inputEffectRaw.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (channel.later_close order)
          Sensitivity.sampleInputScale_nonneg)
    calc
      Data.Gaussian.Norm.Basic.normSq
          (Sample.sample (source later)
              (later + 1) -
            Sample.sample (source earlier)
              (earlier + 1)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              (Sample.sample (source later)
                  (later + 1) -
                Sample.sample (source later)
                  (earlier + 1)) +
            Data.Gaussian.Norm.Basic.normSq
              (Sample.sample (source later)
                  (earlier + 1) -
                Sample.sample (source earlier)
                  (earlier + 1))) := Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 *
          (Geometric.Basic.quarterRadius 5 earlier +
            Sensitivity.sampleInputScale *
              Geometric.Basic.quarterRadius
                channel.errorScale earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add truncation inputEffect) (by decide)
      _ = Geometric.Basic.quarterRadius
          (2 * (5 + Sensitivity.sampleInputScale *
            channel.errorScale)) earlier := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 1
  centerBound_nonneg := by decide
  bounded := fun index =>
    Sample.sample_bounded_one (disk index)
      (index + 1)
end Channel

end Purelib.Approximation.Gaussian.Sequence.Geometric.Channel

end
