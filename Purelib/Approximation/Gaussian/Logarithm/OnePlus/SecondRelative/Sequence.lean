module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Bounds
import Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sample
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

open Purelib.Approximation.Gaussian.Logarithm.OnePlus

open Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sequence

/-- Package finite second-relative logarithm samples as a rational approximation on the quarter-quadrance disk.

The retained data use a scale-one geometric error modulus, terminating index refinement and uniform squared-norm bound
four. -/
def log1pSecondRelApproximation (u :
  Data.Gaussian.Basic.Canonical)
    (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) : ApproximationData where
  sample := Sample.log1pSecondRelSample u
  radiusSq := Geometric.Basic.quarterRadius 1
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := SecondRelative.Bounds.log1pSecondRelSample_later_close disk
  refineIndex current target _ :=
    Search.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := SecondRelative.Bounds.log1pSecondRelSample_bounded disk
end Purelib.Approximation.Gaussian.Logarithm.OnePlus.SecondRelative.Sequence

end
