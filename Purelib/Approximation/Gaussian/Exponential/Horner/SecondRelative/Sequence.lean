module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sample
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sequence

/-- Package the finite second-relative exponential samples on the rational unit disk.

The approximation retains its scale-five-halves quarter-radius modulus, terminating index refinement and uniform
squared-norm bound one. -/
def expSecondRelApproximation (z :
  Data.Gaussian.Basic.Canonical)
    (unitInput : Data.Gaussian.Norm.Basic.normSq z ≤ 1) : ApproximationData where
  sample := Sample.expSecondRelSample z
  radiusSq := Geometric.Basic.quarterRadius
    Sample.expSecondRelErrorScale
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg
      Sample.expSecondRelErrorScale_nonneg
  later_close := Sample.expSecondRelSample_later_close unitInput
  refineIndex current target _ :=
    Search.firstQuarterBelow
      Sample.expSecondRelErrorScale current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge
      Sample.expSecondRelErrorScale current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate
      Sample.expSecondRelErrorScale Sample.expSecondRelErrorScale_nonneg
  centerBound := 1
  centerBound_nonneg := by decide
  sample_bounded := Sample.expSecondRelSample_bounded unitInput
end Purelib.Approximation.Gaussian.Exponential.Horner.SecondRelative.Sequence

end
