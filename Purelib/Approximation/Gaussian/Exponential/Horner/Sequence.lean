module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

section
@[expose] public section

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Sequence

/-- The finite Horner samples on the closed rational unit disk, packaged with their rational squared-error sidecar. -/
def approximation (x : Data.Gaussian.Basic.Canonical)
  (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) : ApproximationData where
  sample := Sample.sample x
  radiusSq := Geometric.Basic.quarterRadius 10
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := Sample.sample_later_close x unitInput
  refineIndex current target _ :=
    Search.firstQuarterBelow 10 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 10 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 10 (by decide)
  centerBound := 10
  centerBound_nonneg := by decide
  sample_bounded := Sample.sample_bounded x unitInput
end Purelib.Approximation.Gaussian.Exponential.Horner.Sequence

end
