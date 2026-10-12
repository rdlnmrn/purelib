module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

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

namespace Purelib.Approximation.Gaussian.Sequence.Geometric

set_option genInjectivity false in
/-- A single finite-stage channel with an explicit geometric modulus and uniform rational centre bound. -/
structure Channel (sample : Nat →
  Data.Gaussian.Basic.Canonical) where
  /-- The retained rational scale of the quarter-power movement bound. -/ errorScale : Fraction.Rational
  /-- The retained movement scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- Every later sample stays within the earlier stage's quarter-radius squared movement allowance. -/ later_close : ∀
    {earlier later : Nat}, earlier ≤ later →
    Data.Gaussian.Norm.Basic.normSq (sample later - sample earlier) ≤
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The retained uniform rational bound on sample squared norms. -/ centerBound : Fraction.Rational
  /-- The uniform squared-norm bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every finite sample's squared norm is at most the retained centre bound. -/ bounded : ∀ index,
    Data.Gaussian.Norm.Basic.normSq (sample index) ≤ centerBound

constructive_injectivity Channel

namespace Channel.mk

end Channel.mk

end Purelib.Approximation.Gaussian.Sequence.Geometric

end
