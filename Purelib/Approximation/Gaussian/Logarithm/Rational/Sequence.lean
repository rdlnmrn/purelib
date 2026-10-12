module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Rational.Sample
public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Rational.Sequence

/-- Construct the finite rational logarithm approximation for an input between one half and two.

The original Horner samples carry a scale-one quarter-radius modulus, an executable refinement search and the uniform
squared-norm bound four. -/
def approximation (x : Fraction.Rational) (halfLe : 1
  / 2 ≤ x) (leTwo : x ≤ 2) :
    Gaussian.Sequence.ApproximationData where
  sample := Sample.sample x
  radiusSq := Geometric.Basic.quarterRadius 1
  radiusSq_nonneg :=
    Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := Sample.sample_later_close halfLe leTwo
  refineIndex current target _ :=
    Search.firstQuarterBelow 1 current target
  refineIndex_ge current target _ :=
    Search.firstQuarterBelow_ge 1 current target
  refineIndex_accurate :=
    Search.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 4
  centerBound_nonneg := by decide
  sample_bounded := Sample.sample_bounded halfLe leTwo
end Purelib.Approximation.Gaussian.Logarithm.Rational.Sequence

end
