module
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Integration.Cell.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Certified finite integration

Integration is a pair of finite rational sums.  Each displayed cell carries a
nonnegative weight and rational lower and upper values.  No function space,
partition limit, supremum, or completed integral is introduced.
-/

@[expose] public section

namespace Purelib.Integration

/-! ## Certified finite subdivision -/

set_option genInjectivity false in
open Purelib in
/-- A retained parent cell replaced by a finite list of children with conserved weight and tighter ranges.

Every child lower endpoint is above the original parent's lower endpoint, and every child upper endpoint is below its
upper endpoint. -/
structure IntegrationSplit {α : Type} (parent : Integration.IntegrationCell α) where
  /-- The retained ordered child-cell list replacing the original parent. -/ children : List
    (Integration.IntegrationCell α)
  /-- The children's total integration weight equals the original parent's weight. -/ weight_conserved :
    Integration.integrationWeight children = parent.weight
  /-- Each retained child lower endpoint is at least the parent's lower endpoint. -/ lower_refines : ∀ child, child ∈
    children → parent.lower ≤ child.lower
  /-- Each retained child upper endpoint is at most the parent's upper endpoint. -/ upper_refines : ∀ child, child ∈
    children → child.upper ≤ parent.upper

constructive_injectivity IntegrationSplit

section
open Purelib
open Purelib.Data.Rat
/-- A common lower value bound times total cell weight is at most the lower integral. -/
private theorem weight_mul_lower_le_lowerIntegral
    {α : Type} (baseline : Fraction.Rational) :
    ∀ {cells : List (Integration.IntegrationCell α)},
      (∀ cell, cell ∈ cells → baseline ≤ cell.lower) →
      Integration.integrationWeight cells * baseline ≤ Integration.lowerIntegral cells
  | [], _ => by
      simp only [Integration.integrationWeight_nil, Integration.lowerIntegral_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, lowerBounds => by
      have head := lowerBounds cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          baseline ≤ candidate.lower :=
        fun candidate member =>
          lowerBounds candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled := weight_mul_lower_le_lowerIntegral baseline tail
      dsimp only [Integration.integrationWeight, Integration.lowerIntegral]
      calc
        (cell.weight + Integration.integrationWeight remaining) * baseline =
            cell.weight * baseline +
              Integration.integrationWeight remaining * baseline := by ring1
        _ ≤ cell.weight * cell.lower + Integration.lowerIntegral remaining :=
          add_le_add headScaled tailScaled

/-- The upper integral is at most total cell weight times a common upper value bound. -/
private theorem upperIntegral_le_weight_mul
    {α : Type} (ceiling : Fraction.Rational) :
    ∀ {cells : List (Integration.IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.upper ≤ ceiling) →
      Integration.upperIntegral cells ≤ Integration.integrationWeight cells * ceiling
  | [], _ => by
      simp only [Integration.upperIntegral_nil, Integration.integrationWeight_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, upperBounds => by
      have head := upperBounds cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.upper ≤ ceiling :=
        fun candidate member =>
          upperBounds candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled := upperIntegral_le_weight_mul ceiling tail
      dsimp only [Integration.upperIntegral, Integration.integrationWeight]
      calc
        cell.weight * cell.upper + Integration.upperIntegral remaining ≤
            cell.weight * ceiling +
              Integration.integrationWeight remaining * ceiling :=
          add_le_add headScaled tailScaled
        _ = (cell.weight + Integration.integrationWeight remaining) * ceiling := by
          ring1

end

section
open Purelib
open Purelib.Data.Rat
/-- The certified children's integral enclosure refines the singleton enclosure of their original parent. -/
theorem IntegrationSplit.integralBound_refines
    {α : Type} {parent : Integration.IntegrationCell α}
    (split : IntegrationSplit parent) :
    Interval.Refines (Integration.integralBound split.children) (Integration.integralBound [parent]) := by
  constructor
  · dsimp only [Integration.integralBound, Integration.lowerIntegral]
    have lower := weight_mul_lower_le_lowerIntegral parent.lower
      split.lower_refines
    rw [split.weight_conserved] at lower
    simpa only [add_zero] using lower
  · dsimp only [Integration.integralBound, Integration.upperIntegral]
    have upper := upperIntegral_le_weight_mul parent.upper
      split.upper_refines
    rw [split.weight_conserved] at upper
    simpa only [add_zero] using upper

/-- Replacing the exact parent occurrence by its certified children refines the whole frontier enclosure. -/
theorem IntegrationSplit.frontier_integralBound_refines
    {α : Type} {parent : Integration.IntegrationCell α}
    (split : IntegrationSplit parent)
    (before after : List (Integration.IntegrationCell α)) :
    Interval.Refines
      (Integration.integralBound (before ++ split.children ++ after))
      (Integration.integralBound (before ++ [parent] ++ after)) := by
  have middle := split.integralBound_refines
  have withAfter := Interval.Refines.add middle
    (Interval.Refines.refl (Integration.integralBound after))
  have complete := Interval.Refines.add
    (Interval.Refines.refl (Integration.integralBound before)) withAfter
  rw [Data.List.Append.append_assoc, Data.List.Append.append_assoc]
  rw [Integration.integralBound_append before (split.children ++ after),
    Integration.integralBound_append split.children after,
    Integration.integralBound_append before ([parent] ++ after),
    Integration.integralBound_append [parent] after]
  exact complete

/-! ## Finite integration-refinement histories -/

end

open Purelib in
/-- Finite frontier refinement generated by identity, retained cell splitting and transitive composition.

A split preserves the ordered before and after contexts and uses the original parent's weight-conserving, range-refining
children. -/
inductive IntegrationFrontierRefines {α : Type} :
    List (Integration.IntegrationCell α) → List (Integration.IntegrationCell α) → Prop where
  /-- Every exact frontier refines itself. -/ | refl (frontier : List (Integration.IntegrationCell α)) :
      IntegrationFrontierRefines frontier frontier
  /-- Replace the retained parent occurrence by its certified children within unchanged ordered contexts. -/ | split
    (before after : List (Integration.IntegrationCell α))
      (parent : Integration.IntegrationCell α) (children : IntegrationSplit parent) :
      IntegrationFrontierRefines
        (before ++ children.children ++ after)
        (before ++ [parent] ++ after)
  /-- Compose two frontier refinements through their exact shared middle frontier. -/ | trans {inner middle outer : List
    (Integration.IntegrationCell α)} :
      IntegrationFrontierRefines inner middle →
      IntegrationFrontierRefines middle outer →
      IntegrationFrontierRefines inner outer

namespace IntegrationFrontierRefines

open Purelib in
open Purelib.Data.Rat in
/-- Every finite sequence of certified frontier splits refines the original integral enclosure. -/
theorem integralBound_refines {α : Type}
    {inner outer : List (Integration.IntegrationCell α)}
    (refines : Integration.IntegrationFrontierRefines inner outer) :
    Interval.Refines (Integration.integralBound inner) (Integration.integralBound outer) := by
  induction refines with
  | refl frontier => exact Interval.Refines.refl _
  | split before after parent children =>
      exact children.frontier_integralBound_refines before after
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

section
open Purelib
/-- Frontier refinement cannot decrease the lower integral. -/
theorem lower_mono {α : Type}
    {inner outer : List (Integration.IntegrationCell α)}
    (refines : Integration.IntegrationFrontierRefines inner outer) :
    Integration.lowerIntegral outer ≤ Integration.lowerIntegral inner :=
  refines.integralBound_refines.lower

/-- Frontier refinement cannot increase the upper integral. -/
theorem upper_antitone {α : Type}
    {inner outer : List (Integration.IntegrationCell α)}
    (refines : Integration.IntegrationFrontierRefines inner outer) :
    Integration.upperIntegral inner ≤ Integration.upperIntegral outer :=
  refines.integralBound_refines.upper

/-- Frontier refinement cannot increase weighted oscillation. -/
theorem oscillation_le {α : Type}
    {inner outer : List (Integration.IntegrationCell α)}
    (refines : Integration.IntegrationFrontierRefines inner outer) :
    Integration.integralOscillation inner ≤ Integration.integralOscillation outer := by
  rw [← Integration.integralBound_width, ← Integration.integralBound_width]
  exact refines.integralBound_refines.width_le

/-- Replacing a parent by its certified children preserves total weight in the retained surrounding contexts. -/
private theorem integrationWeight_context_split
    {α : Type} (before after : List (Integration.IntegrationCell α))
    (parent : Integration.IntegrationCell α) (children : Integration.IntegrationSplit parent) :
    Integration.integrationWeight (before ++ children.children ++ after) =
      Integration.integrationWeight (before ++ [parent] ++ after) := by
  rw [Data.List.Append.append_assoc, Data.List.Append.append_assoc]
  rw [Integration.integrationWeight_append before (children.children ++ after),
    Integration.integrationWeight_append children.children after,
    Integration.integrationWeight_append before ([parent] ++ after),
    Integration.integrationWeight_append [parent] after]
  simp only [Integration.integrationWeight, add_zero]
  rw [children.weight_conserved]

end

open Purelib in
open Purelib.Integration in
/-- Every finite frontier refinement preserves the exact original total integration weight. -/
theorem weight_conserved {α : Type}
    {inner outer : List (Integration.IntegrationCell α)}
    (refines : Integration.IntegrationFrontierRefines inner outer) :
    Integration.integrationWeight inner = Integration.integrationWeight outer := by
  induction refines with
  | refl frontier => rfl
  | split before after parent children =>
      exact IntegrationFrontierRefines.integrationWeight_context_split before after parent children
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

end IntegrationFrontierRefines
end Purelib.Integration

end
