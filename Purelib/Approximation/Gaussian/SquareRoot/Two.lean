module

public import Purelib.Approximation.Rational.SquareRoot.Two
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# A finite coherent name for the positive square root of two

Each sample is the upper endpoint of the retained integer-floor bracket.
Cross-stage enclosure bounds yield a quarter-power squared allowance, and
the existing finite geometric selector pays every positive request.
-/

namespace Purelib.Approximation.Gaussian.SquareRoot.Two

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Embed the upper endpoint of the dyadic positive-root bracket on the real axis. -/
@[expose] public def sample (stage : Nat) : Basic.Canonical :=
  RationalEmbedding.realPoint (Rational.SquareRoot.Two.bracket stage).upper

/-- Every sample has squared norm at most nine. -/
public theorem sample_bounded (stage : Nat) : Norm.Basic.normSq (sample stage) ≤ 9 := by
  rw [sample, RationalEmbedding.normSq_realPoint]
  have squared := Arithmetic.pow_le_pow_direct
    (Rational.SquareRoot.Two.upper_spec stage).1.le
    (Rational.SquareRoot.Two.upper_bounds stage).2 2
  have threeSquare : (3 : Fraction.Rational) ^ 2 = 9 := by decide
  rw [threeSquare] at squared
  exact squared

/-- Later upper endpoints are within the earlier squared dyadic width. -/
public theorem later_close {earlier later : Nat} (ordered : earlier ≤ later) :
    Norm.Basic.normSq (sample later - sample earlier) ≤
      Rational.Geometric.Basic.quarterRadius 1 earlier := by
  have absolute := Rational.SquareRoot.Two.upper_abs_difference_le ordered
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.abs_nonneg_direct
      ((Rational.SquareRoot.Two.bracket later).upper -
        (Rational.SquareRoot.Two.bracket earlier).upper)) absolute 2
  rw [Bounds.Abs.abs_sq_direct, Rational.SquareRoot.Two.width_sq] at squared
  rw [sample, sample, RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint]
  exact squared

/-- The executable upper-endpoint sampler with its finite squared-error schedule.

The refinement operation uses the bounded quarter-radius search and preserves
the supplied starting stage while paying any positive rational request. -/
@[expose] public def approximation : ApproximationData where
  sample := sample
  radiusSq := Rational.Geometric.Basic.quarterRadius 1
  radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg (by decide)
  later_close := later_close
  refineIndex current target _ := Rational.Geometric.Search.firstQuarterBelow 1 current target
  refineIndex_ge current target _ := Rational.Geometric.Search.firstQuarterBelow_ge 1 current target
  refineIndex_accurate := Rational.Geometric.Search.firstQuarterBelow_accurate 1 (by decide)
  centerBound := 9
  centerBound_nonneg := by decide
  sample_bounded := sample_bounded

/-- The coherent name represented by the positive-root bracket samples. -/
@[expose] public def named : Name.Coherent.CoherentNamed :=
  Name.Coherent.CoherentNamed.ofApproximation approximation

end Purelib.Approximation.Gaussian.SquareRoot.Two
