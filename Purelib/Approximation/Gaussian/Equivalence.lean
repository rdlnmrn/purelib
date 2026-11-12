module
public import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Name.Basic (Named)

/-!
# Retained finite operational comparisons

Finite comparison records retain their original approximation owners, selected
indices and sample bounds. All comparison builders use the same executable
refinement and sampling programs and their original cached observations.
-/

namespace Purelib.Approximation.Gaussian.Equivalence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Nat

set_option genInjectivity false in
/-- One finite tail comparison below a displayed squared tolerance.

The two retained approximation owners and starting indices determine this
finite comparison. Its computed later indices retain both start bounds and the
squared-distance certificate for every pair of still later original samples. -/
public structure Comparison (left right : ApproximationData)
    (leftStart rightStart : Nat) (target : Fraction.Rational) where
  /-- The computed comparison index for the left approximation. -/ leftIndex : Nat
  /-- The computed comparison index for the right approximation. -/ rightIndex : Nat
  /-- The left comparison index is no earlier than the requested start. -/ left_ge : leftStart ≤ leftIndex
  /-- The right comparison index is no earlier than the requested start. -/ right_ge : rightStart ≤ rightIndex
  /-- Every pair of samples beyond the computed indices has squared distance below the displayed target. -/ close : ∀
    {leftLater rightLater : Nat},
    leftIndex ≤ leftLater → rightIndex ≤ rightLater →
      Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) < target

constructive_injectivity Comparison

set_option genInjectivity false in
/-- Two approximation sidechannels have the same finite operational value when their displayed tails can be synchronized
below every positive rational squared tolerance.

For each pair of finite starting indices and positive rational tolerance,
the retained comparison function returns explicit later indices and certificates
for the original approximation samples at all permitted later stages. -/
public structure Equivalent (left right : ApproximationData) where
  /-- Compute later comparison indices for any two starts and any positive rational squared tolerance. -/ compare : ∀
    (leftStart rightStart : Nat) (target : Fraction.Rational),
    0 < target → Comparison left right leftStart rightStart target

constructive_injectivity Equivalent

/-- A retained strict squared-distance comparison has a strictly positive tolerance. -/
public theorem Comparison.target_positive {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (comparison : Comparison left right leftStart rightStart target) :
    0 < target :=
  (Norm.Basic.normSq_nonneg _).trans_lt
    (comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex))

/-- Enlarge a finite comparison's tolerance while retaining both original paid indices. -/
@[expose] public def Comparison.weaken {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (comparison : Comparison left right leftStart rightStart target)
    (newTarget : Fraction.Rational) (ordered : target ≤ newTarget) :
    Comparison left right leftStart rightStart newTarget where
  leftIndex := comparison.leftIndex
  rightIndex := comparison.rightIndex
  left_ge := comparison.left_ge
  right_ge := comparison.right_ge
  close := fun leftOrder rightOrder => (comparison.close leftOrder rightOrder).trans_le ordered

/-- Reverse a finite comparison with the same original paid indices and squared tolerance. -/
@[expose] public def Comparison.symm {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (comparison : Comparison left right leftStart rightStart target) :
    Comparison right left rightStart leftStart target where
  leftIndex := comparison.rightIndex
  rightIndex := comparison.leftIndex
  left_ge := comparison.right_ge
  right_ge := comparison.left_ge
  close := by
    intro rightLater leftLater rightOrder leftOrder
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact comparison.close leftOrder rightOrder

/-- Compose two actual finite comparisons through a common later middle observation.

Both original comparisons retain their independently paid starts and bounds.
Their maximum middle index is used only in the proof; the returned outer
indices are the actual supplied left and right indices. Squared distances
compose with the factor two from the finite Gaussian triangle estimate.
-/
@[expose] public def Comparison.trans {left middle right : ApproximationData}
    {leftStart firstMiddleStart secondMiddleStart rightStart : Nat} {firstTarget secondTarget : Fraction.Rational}
    (first : Comparison left middle leftStart firstMiddleStart firstTarget)
    (second : Comparison middle right secondMiddleStart rightStart secondTarget) :
    Comparison left right leftStart rightStart (2 * (firstTarget + secondTarget)) where
  leftIndex := first.leftIndex
  rightIndex := second.rightIndex
  left_ge := first.left_ge
  right_ge := second.right_ge
  close := by
    intro leftLater rightLater leftOrder rightOrder
    let index := max first.rightIndex second.leftIndex
    have firstOrder : first.rightIndex ≤ index := by
      dsimp only [index]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have secondOrder : second.leftIndex ≤ index := by
      dsimp only [index]
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    exact (Norm.Bounds.normSq_sub_le_via (left.sample leftLater) (middle.sample index)
      (right.sample rightLater)).trans_lt
      (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Arithmetic.add_lt_add_direct (first.close leftOrder firstOrder)
          (second.close secondOrder rightOrder)))

/-- Retain the exact original comparison indices and bound through pointwise-identical numerical sample programs.

The original requested starts and tolerance remain unchanged. Scalar readback
transfers the same tail bound without another refinement or synchronization.
-/
@[expose] public def Comparison.withSamples {left right : ApproximationData}
    {leftStart rightStart : Nat} {target : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) (newLeft newRight : ApproximationData)
    (leftSame : ∀ index, newLeft.sample index = left.sample index)
    (rightSame : ∀ index, newRight.sample index = right.sample index) :
    Comparison newLeft newRight leftStart rightStart target where
  leftIndex := original.leftIndex
  rightIndex := original.rightIndex
  left_ge := original.left_ge
  right_ge := original.right_ge
  close := by
    intro leftLater rightLater leftOrder rightOrder
    rewrite [leftSame leftLater, rightSame rightLater]
    exact original.close leftOrder rightOrder

/-- Reversal keeps the actual original right comparison index as its left floor. -/
public theorem Comparison.symm_leftIndex {left right : ApproximationData}
    {leftStart rightStart : Nat} {target : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) :
    original.symm.leftIndex = original.rightIndex := rfl

/-- Reversal keeps the actual original left comparison index as its right floor. -/
public theorem Comparison.symm_rightIndex {left right : ApproximationData}
    {leftStart rightStart : Nat} {target : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) :
    original.symm.rightIndex = original.leftIndex := rfl

/-- Transport the whole SAME comparison through an exact scalar target equality, with no new synchronization. -/
@[expose] public def Comparison.castTarget {left right : ApproximationData}
    {leftStart rightStart : Nat} {target nextTarget : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) (equal : target = nextTarget) :
    Comparison left right leftStart rightStart nextTarget := by
  cases equal
  exact original

/-- Exact target transport preserves the complete original comparison heterogeneously. -/
public theorem Comparison.castTarget_heq {left right : ApproximationData}
    {leftStart rightStart : Nat} {target nextTarget : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) (equal : target = nextTarget) :
    HEq (original.castTarget equal) original := by
  cases equal
  rfl

/-- Exact target transport preserves the SAME selected left floor. -/
public theorem Comparison.castTarget_leftIndex {left right : ApproximationData}
    {leftStart rightStart : Nat} {target nextTarget : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) (equal : target = nextTarget) :
    (original.castTarget equal).leftIndex = original.leftIndex := by
  cases equal
  rfl

/-- Exact target transport preserves the SAME selected right floor. -/
public theorem Comparison.castTarget_rightIndex {left right : ApproximationData}
    {leftStart rightStart : Nat} {target nextTarget : Fraction.Rational}
    (original : Comparison left right leftStart rightStart target) (equal : target = nextTarget) :
    (original.castTarget equal).rightIndex = original.rightIndex := by
  cases equal
  rfl

/-- Reuse an original comparison procedure at identical starts, tolerances and paid indices through scalar readbacks. -/
@[expose] public def Equivalent.withSamples {left right : ApproximationData}
    (original : Equivalent left right) (newLeft newRight : ApproximationData)
    (leftSame : ∀ index, newLeft.sample index = left.sample index)
    (rightSame : ∀ index, newRight.sample index = right.sample index) : Equivalent newLeft newRight where
  compare leftStart rightStart target positive :=
    (original.compare leftStart rightStart target positive).withSamples newLeft newRight leftSame rightSame

/-- Request the same original operational relation after two already paid stage floors.

The actual original comparison receives the maximum of each caller start and
its retained floor. Its complete returned indices, tail bound and numerical
owners are consumed unchanged; only the two caller lower bounds are transported.
-/
@[expose] public def Equivalent.withFloors {left right : ApproximationData}
    (equivalent : Equivalent left right) (leftFloor rightFloor : Nat) : Equivalent left right where
  compare leftStart rightStart target positive :=
    let comparison := equivalent.compare (max leftStart leftFloor) (max rightStart rightFloor) target positive
    { leftIndex := comparison.leftIndex
      rightIndex := comparison.rightIndex
      left_ge := (by
        have start : leftStart ≤ max leftStart leftFloor := by
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left _ _
        exact start.trans comparison.left_ge)
      right_ge := (by
        have start : rightStart ≤ max rightStart rightFloor := by
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left _ _
        exact start.trans comparison.right_ge)
      close := comparison.close }

/-- Floor extension retains the entire actual original comparison apart from its weaker caller-start proofs. -/
public theorem Equivalent.withFloors_compare {left right : ApproximationData}
    (equivalent : Equivalent left right) (leftFloor rightFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    (equivalent.withFloors leftFloor rightFloor).compare leftStart rightStart target positive =
      { leftIndex :=
          (equivalent.compare (max leftStart leftFloor) (max rightStart rightFloor) target positive).leftIndex
        rightIndex :=
          (equivalent.compare (max leftStart leftFloor) (max rightStart rightFloor) target positive).rightIndex
        left_ge := ((equivalent.withFloors leftFloor rightFloor).compare leftStart rightStart target positive).left_ge
        right_ge := ((equivalent.withFloors leftFloor rightFloor).compare leftStart rightStart target positive).right_ge
        close :=
          (equivalent.compare (max leftStart leftFloor) (max rightStart rightFloor) target positive).close } := rfl

/-- Every approximation is operationally equivalent to itself.

The original maximum starting index is refined once at one quarter of
the requested tolerance. Both retained comparison indices use that same
refinement and its finite pairwise-error certificate. -/
@[expose] public def Equivalent.refl (approximation : ApproximationData) :
    Equivalent approximation approximation where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    have leftMaximum : leftStart ≤ start := by
      change leftStart ≤ max leftStart rightStart
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have rightMaximum : rightStart ≤ start := by
      change rightStart ≤ max leftStart rightStart
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    let index := approximation.refineIndex start (target / 4)
      (Bounds.Quarter.quarter_pos positive)
    have radiusSmall : approximation.radiusSq index < target / 4 :=
      approximation.refineIndex_accurate start (target / 4)
        (Bounds.Quarter.quarter_pos positive)
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := leftMaximum.trans
          (approximation.refineIndex_ge start (target / 4)
            (Bounds.Quarter.quarter_pos positive))
        right_ge := rightMaximum.trans
          (approximation.refineIndex_ge start (target / 4)
            (Bounds.Quarter.quarter_pos positive))
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftClose := approximation.later_close leftOrder
          have rightClose := approximation.later_close rightOrder
          have rightClose' :
              Norm.Basic.normSq
                (approximation.sample index -
                  approximation.sample rightLater) ≤
                approximation.radiusSq index := by
            rw [show approximation.sample index - approximation.sample rightLater =
                -(approximation.sample rightLater - approximation.sample index) by
                  apply Basic.ext <;>
                    simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1,
              Norm.Basic.normSq_neg]
            exact rightClose
          calc
            Norm.Basic.normSq
                (approximation.sample leftLater -
                  approximation.sample rightLater) ≤
                2 * (Norm.Basic.normSq
                    (approximation.sample leftLater -
                      approximation.sample index) +
                  Norm.Basic.normSq
                    (approximation.sample index -
                      approximation.sample rightLater)) :=
              Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 *
                (approximation.radiusSq index +
                  approximation.radiusSq index) :=
              Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose') (by decide)
            _ < 2 * (target / 4 + target / 4) :=
              Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Arithmetic.add_lt_add_direct
                  radiusSmall radiusSmall)
            _ = target := by
              have quarterSum : target / 4 + target / 4 = target / 2 := by
                apply Fraction.Field.mul_right_cancel_of_ne
                  (show (4 : Fraction.Rational) ≠ 0 by decide)
                calc
                  (target / 4 + target / 4) * 4 =
                      (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
                  _ = target + target := by
                    rw [show target / 4 * 4 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
                  _ = target * 2 := by ring1
                  _ = ((target / 2) * 2) * 2 := by
                    rw [show target / 2 * 2 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
                  _ = (target / 2) * (2 * 2) :=
                    Fraction.Field.mul_assoc (target / 2) 2 2
                  _ = (target / 2) * 4 := by
                    rw [show (2 : Fraction.Rational) * 2 = 4 by decide]
              rw [quarterSum, Fraction.Field.mul_comm]
              exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide) }

/-- Operational equivalence is symmetric.

The comparison calls the original forward comparison with exchanged
starts. It retains the computed indices in reverse order and transports the
same squared-distance bound through Gaussian negation. -/
@[expose] public def Equivalent.symm {left right : ApproximationData}
    (equivalent : Equivalent left right) : Equivalent right left where
  compare rightStart leftStart target positive :=
    (equivalent.compare leftStart rightStart target positive).symm

/-- Operational equivalence is transitive by sequentially synchronizing the middle approximation.

The first comparison selects the left and middle indices, and the second
starts at that retained middle index. Both use a quarter of the requested
tolerance, so their original squared-distance bounds compose at the same middle sample. -/
@[expose] public def Equivalent.trans {left middle right : ApproximationData}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Bounds.Quarter.quarter_pos positive
    let first := leftMiddle.compare leftStart 0 smallTarget smallPositive
    let second := middleRight.compare first.rightIndex rightStart
      smallTarget smallPositive
    have paid : 2 * (smallTarget + smallTarget) = target := by
      dsimp only [smallTarget]
      calc
        _ = (target / 4) * 4 := by ring1
        _ = target := Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
    exact (first.trans second).weaken target (by
      rewrite [paid]
      exact Fraction.Order.Basic.le_refl target)

/-- Compare two actual constant-sample approximations at their displayed finite squared separation.

The original starting indices already supply both observations. Their
actual constant readbacks determine the squared separation, and the paid
positive accuracy provides the strict additional allowance.
-/
@[expose] public def Comparison.of_constant_samples (left right : ApproximationData)
    (first second : Basic.Canonical) (leftSample : ∀ index, left.sample index = first)
    (rightSample : ∀ index, right.sample index = second)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Comparison left right leftStart rightStart (Norm.Basic.normSq (first - second) + accuracy) where
  leftIndex := leftStart
  rightIndex := rightStart
  left_ge := Nat.le_refl _
  right_ge := Nat.le_refl _
  close := by
    intro leftLater rightLater _ _
    rewrite [leftSample leftLater, rightSample rightLater]
    have ordered := Arithmetic.add_lt_add_left_direct positive (Norm.Basic.normSq (first - second))
    rewrite [_root_.add_zero] at ordered
    exact ordered

/-- Two finite approximation programs which display one and the same exact Gaussian rational at every index are
operationally equivalent.

Every sample of each original approximation equals the displayed Gaussian
rational witness. The supplied starting indices already form a comparison,
and their zero separation meets every positive rational tolerance. -/
@[expose] public def Equivalent.of_constant_samples (left right : ApproximationData)
    (value : Basic.Canonical)
    (leftSample : ∀ index, left.sample index = value)
    (rightSample : ∀ index, right.sample index = value) :
    Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let comparison := Comparison.of_constant_samples left right value value leftSample rightSample
      leftStart rightStart target positive
    exact comparison.weaken target (by
      rewrite [_root_.sub_self, Norm.Basic.normSq_zero, _root_.zero_add]
      exact Fraction.Order.Basic.le_refl target)

/-- Constant samples in operationally equivalent approximations have the same exact Gaussian reading. -/
public theorem Equivalent.constant_samples_eq {left right : ApproximationData} (equivalent : Equivalent left right)
    (first second : Basic.Canonical) (leftSample : ∀ index, left.sample index = first)
    (rightSample : ∀ index, right.sample index = second) : first = second := by
  if equal : first = second then exact equal
  else
    have differenceNonzero : first - second ≠ 0 :=
      fun zero => equal (Basic.gaussian_eq_of_sub_eq_zero zero)
    let comparison := equivalent.compare 0 0 (Norm.Basic.normSq (first - second))
      (Norm.Basic.normSq_pos differenceNonzero)
    have close := comparison.close (leftLater := comparison.leftIndex) (rightLater := comparison.rightIndex)
      (Nat.le_refl _) (Nat.le_refl _)
    rewrite [leftSample comparison.leftIndex, rightSample comparison.rightIndex] at close
    exact (lt_irrefl _ close).elim

/-- Operational equality of finite-request arithmetic CCL programs is equality of the nested finite witness
approximations calculated from their current states. This definition compares only displayed rational samples and
rational error requests; it does not quantify over completed values.

The two original names supply their own retained sampling approximations.
The resulting comparison retains those owners and synchronizes their actual
finite witness readings for each displayed positive rational tolerance. -/
@[expose] public def NamedEquivalent (left right : Named) :=
  Equivalent
    (Sampling.approximation left)
    (Sampling.approximation right)

/-- Every Gaussian name is operationally equivalent to itself.

The original name is sampled through its retained process and starting
state. Reflexivity retains the same sampled approximation on both sides. -/
@[expose] public def NamedEquivalent.refl (name : Named) : NamedEquivalent name name :=
  Equivalent.refl _

/-- Reverse a retained finite-request operational equivalence of names.

The two names retain their original sampled approximation owners.
Reversing the supplied comparison exchanges its indices and squared-distance evidence. -/
@[expose] public def NamedEquivalent.symm {left right : Named} (equivalent : NamedEquivalent left
  right) :
    NamedEquivalent right left :=
  Equivalent.symm equivalent

/-- Compose two finite-request operational equivalences through their common middle name.

The middle name supplies the common retained sampled approximation.
The two given comparisons are composed through its actual samples and indices. -/
@[expose] public def NamedEquivalent.trans {left middle right : Named}
    (leftMiddle : NamedEquivalent left middle)
    (middleRight : NamedEquivalent middle right) :
    NamedEquivalent left right :=
  Equivalent.trans leftMiddle middleRight

/-- Transport a retained operational comparison along exact equalities of its two original names.

Only the displayed endpoint indices change. Equality elimination retains the
same comparison function, selected sample indices and quantitative witnesses.
-/
@[expose] public def NamedEquivalent.transport {first second left right : Named}
    (firstEq : first = left) (secondEq : second = right)
    (equivalent : NamedEquivalent first second) : NamedEquivalent left right := by
  cases firstEq
  cases secondEq
  exact equivalent

/-- Compare an original approximation with zero using an equivalent bounded approximation and one paid accuracy.

The actual comparison supplies the retained left index and one actual
right sample. Its displayed norm bound and the Gaussian triangle bound
pay the returned tolerance. The zero comparison preserves the independently
requested zero start; no left sample or input comparison is recomputed.
-/
public def Equivalent.compare_zero_of_bound {left right : ApproximationData}
    (equivalent : Equivalent left right) (upper : Fraction.Rational)
    (bounded : ∀ index, Norm.Basic.normSq (right.sample index) ≤ upper)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Comparison left (Sampling.approximation (Named.exact 0)) leftStart rightStart (2 * (accuracy + upper)) := by
  let paid := equivalent.compare leftStart 0 accuracy positive
  refine ⟨paid.leftIndex, rightStart, paid.left_ge, Nat.le_refl _, ?_⟩
  intro leftLater _rightLater leftOrder _rightOrder
  change Norm.Basic.normSq (left.sample leftLater - (0 : Data.Gaussian.Basic.Canonical)) < _
  rewrite [Data.Gaussian.Basic.sub_zero]
  have close := paid.close leftOrder (Nat.le_refl paid.rightIndex)
  have translated := Arithmetic.add_lt_add_right_direct close
    (Norm.Basic.normSq (right.sample paid.rightIndex))
  have increased := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl accuracy) (bounded paid.rightIndex)
  have triangle := Norm.Bounds.normSq_sub_le_via (left.sample leftLater) (right.sample paid.rightIndex) 0
  rewrite [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.sub_zero] at triangle
  exact triangle.trans_lt (Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide) (translated.trans_le increased))

end Purelib.Approximation.Gaussian.Equivalence
