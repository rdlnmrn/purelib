module

import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order

/-! # Whole original signed-root channel comparison

The historical body is a verifier-only private definition. The quantified
regression compares complete original NamedEquivalent values, including
all comparison functions, independently paid floors and square relations.
It performs no assumed root comparison or numerical fixture substitution.
-/

namespace TestPurelib.Riemann.RootContinuation.SquareRootChannelOwnership

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity sampled_square)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
  (Gaussian Coordinate CoherentNamed NamedEquivalent Apart root_distance equivalent_of_near_tails)

/-- The complete historical near-tail comparison construction before sharing its residual/payment branch. -/
private def formerNearTails {left right : CoherentNamed} {parameter : Gaussian}
    (leftSquare : SquareIdentity left parameter) (rightSquare : SquareIdentity right parameter)
    (apart : Apart left.name) (base rightBase : Nat)
    (near : ∀ leftIndex rightIndex, base ≤ leftIndex → rightBase ≤ rightIndex →
      normSq ((Name.Sampling.approximation left.name).sample leftIndex -
        (Name.Sampling.approximation right.name).sample rightIndex) ≤ apart.certificate.lowerSq) :
    NamedEquivalent left.name right.name where
  compare := by
    intro leftStart rightStart target positive
    let residualTarget := target * apart.certificate.lowerSq / 4
    have residualPositive : 0 < residualTarget :=
      Field.div_pos_direct
        (Arithmetic.mul_pos_direct positive apart.certificate.positive) (by decide)
    have baseBound : base ≤ max base leftStart := by
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_left _ _
    have startBound : leftStart ≤ max base leftStart := by
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_right _ _
    let first := (sampled_square leftSquare).compare (max base leftStart) 0 residualTarget residualPositive
    let rightFloor := match rightBase with
      | 0 => rightStart
      | _ + 1 => max rightBase rightStart
    have rightBaseBound : rightBase ≤ rightFloor := by
      cases rightBase with
      | zero => exact Nat.zero_le _
      | succ rightBase =>
          change rightBase + 1 ≤ max (rightBase + 1) rightStart
          rewrite [Nat.Order.max_eq_natMax]
          exact Nat.Order.le_max_left _ _
    have rightStartBound : rightStart ≤ rightFloor := by
      cases rightBase with
      | zero => exact Nat.le_refl _
      | succ rightBase =>
          change rightStart ≤ max (rightBase + 1) rightStart
          rewrite [Nat.Order.max_eq_natMax]
          exact Nat.Order.le_max_right _ _
    let second := (sampled_square rightSquare).compare rightFloor 0 residualTarget residualPositive
    refine
      { leftIndex := first.leftIndex
        rightIndex := second.leftIndex
        left_ge := startBound.trans first.left_ge
        right_ge := rightStartBound.trans second.left_ge
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have leftResidual := first.close leftOrder (Nat.le_refl first.rightIndex)
    have rightResidual := second.close rightOrder (Nat.le_refl second.rightIndex)
    rw [Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
    change normSq ((Name.Sampling.approximation left.name).sample leftLater *
      (Name.Sampling.approximation left.name).sample leftLater - parameter) < residualTarget at leftResidual
    change normSq ((Name.Sampling.approximation right.name).sample rightLater *
      (Name.Sampling.approximation right.name).sample rightLater - parameter) < residualTarget at rightResidual
    have rootLower := Name.Apart.Sampling.sampled_lower left apart leftLater
    rw [Norm.Basic.normSq_eq_canonical] at rootLower
    rw [Norm.Basic.normSq_eq_canonical]
    exact root_distance apart.certificate.positive rootLower
      (near leftLater rightLater (baseBound.trans (first.left_ge.trans leftOrder))
        (rightBaseBound.trans (second.left_ge.trans rightOrder)))
      leftResidual rightResidual

/-- Every original near-tail input retains its complete former comparison value after factoring the shared procedure. -/
private theorem nearTails_eq_former {left right : CoherentNamed} {parameter : Gaussian}
    (leftSquare : SquareIdentity left parameter) (rightSquare : SquareIdentity right parameter)
    (apart : Apart left.name) (base rightBase : Nat)
    (near : ∀ leftIndex rightIndex, base ≤ leftIndex → rightBase ≤ rightIndex →
      normSq ((Name.Sampling.approximation left.name).sample leftIndex -
        (Name.Sampling.approximation right.name).sample rightIndex) ≤ apart.certificate.lowerSq) :
    equivalent_of_near_tails leftSquare rightSquare apart base rightBase near =
      formerNearTails leftSquare rightSquare apart base rightBase near := by rfl

end TestPurelib.Riemann.RootContinuation.SquareRootChannelOwnership
