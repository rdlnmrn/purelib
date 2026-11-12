module

public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.SmallWidth
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Bounded comparisons of original geometric sample streams -/

public section

namespace Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

open Purelib
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Nat

/-- Independently selected sample indices above their requested floors retain the original geometric movement bound.

The two actual selected indices may occur in either order. The original
later-sample certificate is used in their actual order, then the earlier
requested floor pays its same original geometric scale.
-/
theorem selectedSamples_close (source : GeometricApproximation) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) {earlier later : Nat} (ordered : earlier ≤ later) :
    Norm.Basic.normSq (source.sample (indices later) - source.sample (indices earlier)) ≤
      Basic.quarterRadius source.errorScale earlier := by
  if forward : indices earlier ≤ indices later then
    exact (source.later_close forward).trans
      (Basic.quarterRadius_antitone source.errorScale_nonneg (floor earlier))
  else
    have reverse : indices later ≤ indices earlier := Nat.le_of_lt (Nat.lt_of_not_ge forward)
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact (source.later_close reverse).trans
      (Basic.quarterRadius_antitone source.errorScale_nonneg (ordered.trans (floor later)))

/-- Select actual original geometric samples at independent indices above their same requested floors.

No monotonicity is required of the selection. The same original sample
producer, movement scale and magnitude bound are retained; the selected
sample is computed once when that actual stage is requested.
-/
def selectStages (source : GeometricApproximation) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) : GeometricApproximation where
  sample index := source.sample (indices index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := source.selectedSamples_close indices floor
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := fun index => source.sample_bounded (indices index)

/-- A selected stage reads the same original sample at its actual supplied selected index. -/
theorem selectStages_sample (source : GeometricApproximation) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) (index : Nat) :
    (source.selectStages indices floor).sample index = source.sample (indices index) := by
  unfold selectStages
  rfl

/-- Compare two actual geometric sample streams with a uniform offset and a decaying same-stage bound.

The original movement scales and decaying bridge scale determine one paid
common stage above both independent starts. The uniform offset remains
in the displayed tolerance; this operation does not turn a bounded error
into operational equivalence. Both actual original sample streams are
retained, and every permitted later pair obeys the returned strict bound.
-/
def compareSamples (first last : GeometricApproximation) (offset bridge : Fraction.Rational)
    (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq (first.sample index - last.sample index) ≤
      offset + Basic.quarterRadius bridge index)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison first.toApproximation last.toApproximation leftStart rightStart (4 * offset + target) := by
  let scale := 2 * (first.errorScale + 2 * (bridge + last.errorScale))
  have scaleNonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg first.errorScale_nonneg (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg nonnegative last.errorScale_nonneg)))
  let common := Search.firstQuarterBelow scale (max leftStart rightStart) target
  have paid := Search.firstQuarterBelow_accurate scale scaleNonnegative (max leftStart rightStart) target positive
  refine
    { leftIndex := common
      rightIndex := common
      left_ge := (Order.le_max_left _ _).trans (Search.firstQuarterBelow_ge _ _ _)
      right_ge := (Order.le_max_right _ _).trans (Search.firstQuarterBelow_ge _ _ _)
      close := ?_ }
  intro leftLater rightLater leftOrder rightOrder
  have left := first.later_close leftOrder
  have middle := distance common
  have right := last.later_close rightOrder
  rewrite [Norm.Bounds.normSq_sub_symm] at right
  have bounded := Norm.Bounds.normSq_sub_le_weighted_sum
    (first.sample leftLater) (first.sample common) (last.sample common) (last.sample rightLater)
    (Basic.quarterRadius first.errorScale common) (offset + Basic.quarterRadius bridge common)
    (Basic.quarterRadius last.errorScale common) left middle right
  have scalar :
      2 * (Basic.quarterRadius first.errorScale common +
        2 * (offset + Basic.quarterRadius bridge common + Basic.quarterRadius last.errorScale common)) =
      4 * offset + Basic.quarterRadius scale common := by
    calc
      _ = 4 * offset + 2 * (Basic.quarterRadius first.errorScale common +
          2 * (Basic.quarterRadius bridge common + Basic.quarterRadius last.errorScale common)) := by ring1
      _ = _ := congrArg (fun value => 4 * offset + value)
        (Basic.quarterRadius_weighted_sum first.errorScale bridge last.errorScale common)
  exact (bounded.trans_eq scalar).trans_lt (Arithmetic.add_lt_add_left_direct paid _)

/-- Lift a bounded same-stage comparison through both actual productive Gaussian controllers.

The original round-trip comparisons pay the two independently requested
name starts. The middle comparison retains its uniform offset, and one
finite precision pays the two outer bridges. This constructs a bounded
comparison of the actual CCL names, without asserting their equivalence.
-/
def compareNames (first last : GeometricApproximation) (offset bridge : Fraction.Rational)
    (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq (first.sample index - last.sample index) ≤
      offset + Basic.quarterRadius bridge index)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison (Name.Sampling.approximation first.toApproximation.toNamed)
      (Name.Sampling.approximation last.toApproximation.toNamed) leftStart rightStart (16 * offset + target) := by
  let precision := SmallWidth.shrinkingWidth 10 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 10) positive
  let earlier := (Equivalence.Equivalent.toNamed_sampling first.toApproximation).compare
    leftStart 0 precision precisionPositive
  let middle := first.compareSamples last offset bridge nonnegative distance 0 0 precision precisionPositive
  let later := (Equivalence.Equivalent.toNamed_sampling last.toApproximation).symm.compare
    0 rightStart precision precisionPositive
  let compared := earlier.trans (middle.trans later)
  have scale : 2 * (precision + 2 * (4 * offset + precision + precision)) =
      16 * offset + 10 * precision := by ring1
  exact compared.weaken (16 * offset + target)
    (scale.trans_lt (Arithmetic.add_lt_add_left_direct paid _)).le

/-- A zero uniform offset gives operational equivalence through the same original finite comparison traversal. -/
def equivalentOfSamplesClose (first last : GeometricApproximation) (bridge : Fraction.Rational)
    (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq (first.sample index - last.sample index) ≤
      Basic.quarterRadius bridge index) : Equivalence.Equivalent first.toApproximation last.toApproximation where
  compare leftStart rightStart target positive :=
    (compareSamples first last 0 bridge nonnegative (fun index =>
      (distance index).trans_eq (Fraction.Field.zero_add (Basic.quarterRadius bridge index)).symm)
      leftStart rightStart target positive).weaken target (by
        have same : (4 : Fraction.Rational) * 0 + target = target := by ring1
        exact same.le)

/-- Independent stage selection preserves the original geometric output through the same finite Cauchy comparison. -/
def selectedStages_equivalent (source : GeometricApproximation) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) :
    Equivalence.Equivalent source.toApproximation (source.selectStages indices floor).toApproximation :=
  source.equivalentOfSamplesClose (source.selectStages indices floor) source.errorScale source.errorScale_nonneg (by
    intro index
    rewrite [selectStages_sample, Norm.Bounds.normSq_sub_symm]
    exact source.later_close (floor index))

open Purelib.Approximation.Gaussian.Equivalence (Comparison Equivalent)

variable (reference : Sequence.ApproximationData)
    (stages : (index : Nat) → (source : Sequence.ApproximationData) ×
      Comparison source reference 0 0 (Basic.quarterRadius 1 index))

/-- Sample each supplied original source at its retained paid index to obtain one geometric approximation.

Every stage retains its own original approximation and actual comparison
with the same reference. Original comparison composition gives the movement
bound through a common later reference sample. No new comparison request
or reference sample is computed to build the displayed source sample.
-/
def fromComparisons : GeometricApproximation where
  sample index :=
    let retained := stages index
    retained.1.sample retained.2.leftIndex
  errorScale := 4
  errorScale_nonneg := by decide
  later_close := by
    intro earlier later order
    let first := stages earlier
    let last := stages later
    have paid := (last.2.trans first.2.symm).close
      (Nat.le_refl last.2.leftIndex) (Nat.le_refl first.2.leftIndex)
    have targets := Basic.quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 1) order
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct targets
        (Fraction.Order.Basic.le_refl (Basic.quarterRadius 1 earlier)))
      (by decide : (0 : Fraction.Rational) ≤ 2)
    exact paid.le.trans (bound.trans_eq (by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1))
  centerBound := 2 * (reference.centerBound + 1)
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct (by decide)
      ((show (0 : Fraction.Rational) = 0 + 0 by decide).trans_le
        (Arithmetic.add_le_add_direct reference.centerBound_nonneg (by decide)))
  sample_bounded := by
    intro index
    let retained := stages index
    have paid := retained.2.close (Nat.le_refl retained.2.leftIndex)
      (Nat.le_refl retained.2.rightIndex)
    have offset := paid.le.trans (Basic.quarterRadius_le_scale (by decide) index)
    have bound := Norm.Bounds.value_normSq_le_of_offset offset
    exact bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (reference.sample_bounded retained.2.rightIndex)
        (Fraction.Order.Basic.le_refl 1)) (by decide))

/-- The geometric constructor reads the exact supplied source at its same retained paid index. -/
theorem fromComparisons_sample (index : Nat) :
    (fromComparisons reference stages).sample index =
      (stages index).1.sample (stages index).2.leftIndex := (rfl)

/-- The displayed stage samples agree operationally with their one original reference.

The original reference comparison pays the caller's independent right
start. Each later source retains its own comparison receipt; composing
that same receipt supplies the all-future bound without a uniform bound
on the separate receipts' reference indices.
-/
def fromComparisons_equivalent :
    Equivalent (fromComparisons reference stages).toApproximation reference where
  compare leftStart rightStart target positive := by
    let precision := target / 4
    have precisionPositive : 0 < precision := Fraction.Order.Field.div_pos_direct positive (by decide)
    let index := Search.firstQuarterBelow 1 leftStart precision
    let right := (Equivalent.refl reference).compare 0 rightStart precision precisionPositive
    refine
      { leftIndex := index
        rightIndex := right.rightIndex
        left_ge := Search.firstQuarterBelow_ge 1 leftStart precision
        right_ge := right.right_ge
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    let retained := stages leftLater
    have paid := (retained.2.trans right).close (Nat.le_refl retained.2.leftIndex) rightOrder
    have small := (Basic.quarterRadius_antitone (by decide : (0 : Fraction.Rational) ≤ 1)
      leftOrder).trans_lt (Search.firstQuarterBelow_accurate 1 (by decide) leftStart precision precisionPositive)
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct small.le (Fraction.Order.Basic.le_refl precision))
      (by decide : (0 : Fraction.Rational) ≤ 2)
    have scalar : 2 * (precision + precision) = target := by
      change 2 * (target / 4 + target / 4) = target
      rewrite [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
    exact paid.trans_le (bound.trans_eq scalar)

end Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

end
