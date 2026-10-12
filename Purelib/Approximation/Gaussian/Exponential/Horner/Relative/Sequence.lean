module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sample
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner.Relative

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the exponential

The relative exponential is not introduced by dividing by its argument.
Instead, `expRelSample z n` is the already finite inner Horner program, and
the factorization

`expSample z n - 1 = z * expRelSample z n`

is proved at every displayed depth, including `z = 0`.  A second shifted
Horner program gives a quadratic remainder.  All approximation objects below
contain only Gaussian-rational samples, rational squared-error allowances,
and terminating natural-number refinement programs.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sequence

/-- Progressive CCL-ready relative-exponential computation on the rational unit disk. -/
def expRelApproximation (z :
  Data.Gaussian.Basic.Canonical)
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) : ApproximationData where
  sample := Sample.expRelSample z
  radiusSq := Geometric.Basic.quarterRadius 10
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := Sample.expRelSample_later_close unitInput
  refineIndex current target _ :=
    Search.firstQuarterBelow 10 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 10 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 10 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := Sample.expRelSample_bounded unitInput
end Purelib.Approximation.Gaussian.Exponential.Horner.Relative.Sequence

end
