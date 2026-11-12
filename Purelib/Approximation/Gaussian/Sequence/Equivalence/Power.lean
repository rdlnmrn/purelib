module

public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Order

/-! # Operational constant comparisons from finite power bounds -/

public section

namespace Purelib.Approximation.Gaussian.Sequence.Equivalence.Power

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order

/-- A finite decreasing bound on a positive power pays every original comparison to the same constant.

The finite search follows both the original starting index and retained
floor, with target raised to the same positive natural exponent. Original
later samples meet the caller's target without extracting a numerical root
or replacing either approximation program.
-/
def constant_after (source : ApproximationData) (point : Canonical) (degree : Nat)
    (_positiveDegree : 0 < degree) (floor : Nat) (scale : Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, floor ≤ index → normSq (source.sample index - point) ^ degree ≤
      Basic.quarterRadius scale index) :
    Gaussian.Equivalence.Equivalent source (Constant.constantApproximation point) where
  compare firstStart secondStart target targetPositive := by
    let start := Nat.max firstStart floor
    let targetPower := target ^ degree
    have targetPowerPositive : 0 < targetPower := Arithmetic.pow_pos_direct targetPositive degree
    let index := Search.firstQuarterBelow scale start targetPower
    have startLe := Search.firstQuarterBelow_ge scale start targetPower
    refine
      { leftIndex := index
        rightIndex := secondStart
        left_ge := (Data.Nat.Order.le_max_left _ _).trans startLe
        right_ge := Nat.le_refl secondStart
        close := ?_ }
    intro firstLater secondLater firstOrder _secondOrder
    change normSq (source.sample firstLater - point) < target
    have floorLe : floor ≤ firstLater :=
      ((Data.Nat.Order.le_max_right _ _).trans startLe).trans firstOrder
    have powered : normSq (source.sample firstLater - point) ^ degree < target ^ degree :=
      (samples firstLater floorLe).trans_lt
        ((Basic.quarterRadius_antitone nonnegative firstOrder).trans_lt
          (Search.firstQuarterBelow_accurate scale nonnegative start targetPower targetPowerPositive))
    if small : normSq (source.sample firstLater - point) < target then
      exact small
    else
      have lower : target ≤ normSq (source.sample firstLater - point) := Arithmetic.le_of_not_gt_direct small
      have powers := Arithmetic.pow_le_pow_direct targetPositive.le lower degree
      exact (not_lt_of_ge powers powered).elim

end Purelib.Approximation.Gaussian.Sequence.Equivalence.Power

end
