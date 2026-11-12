module

public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership

/-! # Operational agreement from signed original owner tails

A relative-distance certificate selects the same branch of two original
root tracks. Their unchanged square-residual procedures then pay every
requested root comparison. A literal OwnerJoin supplies that certificate
through its original distance law; a retained stationary OwnerLink can use
its actual realize certificate through the same operation.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTraceReadings

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation

variable {parameter : Canonical} {left right : Owner parameter}

namespace OwnerTail

variable (firstTail : OwnerTail left) (lastTail : OwnerTail right)
variable (leftIndex rightIndex : Nat)
variable (leftGe : firstTail.first ≤ leftIndex) (rightGe : lastTail.first ≤ rightIndex)
variable (near : ∀ (first : OwnerTail.Reading firstTail) (last : OwnerTail.Reading lastTail),
  leftIndex ≤ first.index → rightIndex ≤ last.index →
    Basic.Canonical.normSq (last.value - first.value) ≤ Basic.Canonical.normSq first.value)

/-- Compare the two original root approximations from a signed relative-distance certificate on their retained tails.

Both consumer starts and the original two thresholds are respected. The
positive first-tail floor pays both original square residuals. At every
later pair the actual signed-distance certificate bounds the root sum away
from zero, so difference of squares supplies the requested absolute bound.
-/
def approximationEquivalentOfNear :
    Equivalence.Equivalent (ownerApproximation left) (ownerApproximation right) where
  compare := by
    intro leftStart rightStart target positive
    let leftFloor := max leftStart leftIndex
    let rightFloor := max rightStart rightIndex
    have leftStart_le : leftStart ≤ leftFloor := by
      change leftStart ≤ max leftStart leftIndex
      rewrite [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_left _ _
    have leftIndex_le : leftIndex ≤ leftFloor := by
      change leftIndex ≤ max leftStart leftIndex
      rewrite [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_right _ _
    have rightStart_le : rightStart ≤ rightFloor := by
      change rightStart ≤ max rightStart rightIndex
      rewrite [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_left _ _
    have rightIndex_le : rightIndex ≤ rightFloor := by
      change rightIndex ≤ max rightStart rightIndex
      rewrite [Data.Nat.Order.max_eq_natMax]
      exact Data.Nat.Order.le_max_right _ _
    let residualTarget : Rational := target * firstTail.lower / 4
    have residualPositive : 0 < residualTarget := Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct positive firstTail.lower_positive)
      (of_decide_eq_true rfl : (0 : Rational) < 4)
    let first := (CertifiedSquareRoot.squareApproximation_equivalent_parameter left.track).compare
      leftFloor 0 residualTarget residualPositive
    let last := (CertifiedSquareRoot.squareApproximation_equivalent_parameter right.track).compare
      rightFloor 0 residualTarget residualPositive
    refine
      { leftIndex := first.leftIndex
        rightIndex := last.leftIndex
        left_ge := leftStart_le.trans first.left_ge
        right_ge := rightStart_le.trans last.left_ge
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have firstAfter := leftIndex_le.trans (first.left_ge.trans leftOrder)
    have lastAfter := rightIndex_le.trans (last.left_ge.trans rightOrder)
    let firstReading := OwnerTail.Reading.acquire firstTail leftLater (leftGe.trans firstAfter)
    let lastReading := OwnerTail.Reading.acquire lastTail rightLater (rightGe.trans lastAfter)
    have close := near firstReading lastReading firstAfter lastAfter
    change Basic.Canonical.normSq ((ownerApproximation right).sample rightLater -
      (ownerApproximation left).sample leftLater) ≤
        Basic.Canonical.normSq ((ownerApproximation left).sample leftLater) at close
    have reverse := Norm.Bounds.normSq_sub_symm
      ((ownerApproximation left).sample leftLater) ((ownerApproximation right).sample rightLater)
    simp only [Norm.Basic.normSq_eq_canonical] at reverse
    have signed : Basic.Canonical.normSq ((ownerApproximation left).sample leftLater -
        (ownerApproximation right).sample rightLater) ≤
          Basic.Canonical.normSq ((ownerApproximation left).sample leftLater) := by
      rewrite [reverse]
      exact close
    have rootLower := firstTail.lower_bound leftLater
    have rootPositive := firstTail.lower_positive.trans_le rootLower
    have paid : residualTarget ≤ target *
        Basic.Canonical.normSq ((ownerApproximation left).sample leftLater) / 4 :=
      Fraction.Order.Field.divide_mono
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootLower positive.le)
        (of_decide_eq_true rfl : (0 : Rational) < 4)
    have leftResidual := first.close leftOrder (Nat.le_refl first.rightIndex)
    have rightResidual := last.close rightOrder (Nat.le_refl last.rightIndex)
    rewrite [Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
    change Basic.Canonical.normSq ((ownerApproximation left).sample leftLater *
      (ownerApproximation left).sample leftLater - parameter) < residualTarget at leftResidual
    change Basic.Canonical.normSq ((ownerApproximation right).sample rightLater *
      (ownerApproximation right).sample rightLater - parameter) < residualTarget at rightResidual
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact SquareRootChannelOwnership.root_distance rootPositive (Fraction.Order.Basic.le_refl _)
      signed (leftResidual.trans_le paid) (rightResidual.trans_le paid)

/-- Preserve the original apart root names while composing the signed-tail comparison through their raw names.

The existing raw-name and apartification laws are used with each unchanged
track and its own complete apartness certificate. No owner, root state or
apartness preparation is acquired by this conversion.
-/
def equivalentOfNear : NamedEquivalent (ownerName left) (ownerName right) := by
  let first := CertifiedSquareRoot.rawRoot left.track
  let last := CertifiedSquareRoot.rawRoot right.track
  have raw : NamedEquivalent first.name last.name :=
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (firstTail.approximationEquivalentOfNear lastTail leftIndex rightIndex leftGe rightGe near)
  exact (Name.Coherent.CoherentNamed.apartifyEquivalent first
    (CertifiedSquareRoot.possibleApart left.parameterNonzero left.track)).symm.trans
      (raw.trans (Name.Coherent.CoherentNamed.apartifyEquivalent last
        (CertifiedSquareRoot.possibleApart right.parameterNonzero right.track)))

end OwnerTail

end Purelib.Riemann.Paths.OwnerTraceReadings

end
