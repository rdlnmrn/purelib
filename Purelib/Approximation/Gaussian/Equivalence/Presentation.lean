module

public import Purelib.Approximation.Gaussian.Equivalence

namespace Purelib.Approximation.Gaussian.Equivalence.Comparison

open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Rat

/-- A comparison's two paid indices determine its identity for fixed owners and request.

The other fields are proofs of the start bounds and the all-later bound. Proof
irrelevance makes their witnesses immaterial to equality of the original record. -/
public theorem eq_of_indices {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (first second : Comparison left right leftStart rightStart target)
    (leftEq : first.leftIndex = second.leftIndex) (rightEq : first.rightIndex = second.rightIndex) :
    first = second := by
  cases first with
  | mk firstLeft firstRight firstLeftGe firstRightGe firstClose =>
    cases second with
    | mk secondLeft secondRight secondLeftGe secondRightGe secondClose =>
      cases leftEq
      cases rightEq
      rfl

/-- Original comparison equality holds exactly when both retained indices agree. -/
public theorem eq_iff_indices {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (first second : Comparison left right leftStart rightStart target) :
    first = second ↔ first.leftIndex = second.leftIndex ∧ first.rightIndex = second.rightIndex :=
  ⟨fun equal => ⟨congrArg Comparison.leftIndex equal, congrArg Comparison.rightIndex equal⟩,
    fun indices => eq_of_indices first second indices.1 indices.2⟩

/-- Decide equality of two already certified comparisons by their two indices.

The fixed parameters retain the same original approximation owners, starts and
tolerance. This decision does not recognize an independently supplied proof of
the universal all-later bound. -/
@[expose] public def decideEquality {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (first second : Comparison left right leftStart rightStart target) :
    Decidable (first = second) :=
  if leftEq : first.leftIndex = second.leftIndex then
    if rightEq : first.rightIndex = second.rightIndex then
      .isTrue (eq_of_indices first second leftEq rightEq)
    else .isFalse (fun equal => rightEq (congrArg Comparison.rightIndex equal))
  else .isFalse (fun equal => leftEq (congrArg Comparison.leftIndex equal))

set_option genInjectivity false in
/-- The result of checking the stage floors of a supplied tail certificate.

An accepted result retains the original comparison owner and both proposed
indices. Rejections identify which requested floor the proposed index violates. -/
public inductive FloorCheck (left right : ApproximationData) (leftStart rightStart : Nat)
    (target : Fraction.Rational) (leftIndex rightIndex : Nat) where
  | accepted (comparison : Comparison left right leftStart rightStart target)
      (left_eq : comparison.leftIndex = leftIndex) (right_eq : comparison.rightIndex = rightIndex)
  | leftBelow (failed : ¬ leftStart ≤ leftIndex)
  | rightBelow (failed : ¬ rightStart ≤ rightIndex)

/-- Check both stage floors and construct the original comparison when they hold.

The all-later bound must already be supplied for these exact owners, indices and
target. This finite check does not recognize an arbitrary proof presentation. -/
public def checkFloors (left right : ApproximationData) (leftStart rightStart : Nat)
    (target : Fraction.Rational) (leftIndex rightIndex : Nat)
    (close : ∀ {leftLater rightLater : Nat}, leftIndex ≤ leftLater → rightIndex ≤ rightLater →
      Purelib.Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) < target) :
    FloorCheck left right leftStart rightStart target leftIndex rightIndex :=
  if leftGe : leftStart ≤ leftIndex then
    if rightGe : rightStart ≤ rightIndex then
      .accepted ⟨leftIndex, rightIndex, leftGe, rightGe, close⟩ rfl rfl
    else .rightBelow rightGe
  else .leftBelow leftGe

/-- Checking an existing comparison's indices and bound returns an accepted comparison. -/
public theorem checkFloors_comparison {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (comparison : Comparison left right leftStart rightStart target) :
    ∃ (found : Comparison left right leftStart rightStart target)
      (leftEq : found.leftIndex = comparison.leftIndex) (rightEq : found.rightIndex = comparison.rightIndex),
      checkFloors left right leftStart rightStart target comparison.leftIndex comparison.rightIndex
        comparison.close = .accepted found leftEq rightEq := by
  cases result : checkFloors left right leftStart rightStart target comparison.leftIndex comparison.rightIndex
      comparison.close with
  | accepted found leftEq rightEq => exact ⟨found, leftEq, rightEq, rfl⟩
  | leftBelow failed => exact False.elim (failed comparison.left_ge)
  | rightBelow failed => exact False.elim (failed comparison.right_ge)

end Purelib.Approximation.Gaussian.Equivalence.Comparison
