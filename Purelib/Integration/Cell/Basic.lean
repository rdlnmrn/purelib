module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Certified finite integration

Integration is a pair of finite rational sums.  Each displayed cell carries a
nonnegative weight and rational lower and upper values.  No function space,
partition limit, supremum, or completed integral is introduced.
-/

public section

namespace Purelib.Integration

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib

set_option genInjectivity false in
/-- A payload with nonnegative integration weight and an ordered rational range enclosure.

The lower and upper readings remain separate from the payload and weight; finite frontiers combine them by exact
weighted sums. -/
structure IntegrationCell (α : Type) where
  /-- The original payload associated with this weighted cell. -/ item : α
  /-- The retained rational integration weight. -/ weight : Fraction.Rational
  /-- The retained integration weight is nonnegative. -/ weight_nonnegative : 0 ≤ weight
  /-- The lower endpoint of the cell's value enclosure. -/ lower : Fraction.Rational
  /-- The upper endpoint of the cell's value enclosure. -/ upper : Fraction.Rational
  /-- The lower value endpoint is at most the upper endpoint. -/ range_valid : lower ≤ upper

constructive_injectivity IntegrationCell

namespace IntegrationCell

/-- View the original cell's lower and upper readings as their retained rational interval. -/
@[expose] def range {α : Type} (cell : IntegrationCell α) : Data.Rat.Interval :=
  ⟨cell.lower, cell.upper, cell.range_valid⟩

/-- Construct a cell whose range enclosure is the supplied exact value and whose nonnegative weight is retained. -/
@[expose] def exact {α : Type} (item : α) (weight value : Fraction.Rational)
    (weightNonnegative : 0 ≤ weight) : Integration.IntegrationCell α where
  item := item
  weight := weight
  weight_nonnegative := weightNonnegative
  lower := value
  upper := value
  range_valid := le_rfl

/-- The difference between the cell's upper and lower range endpoints. -/
@[expose] def oscillation {α : Type} (cell : Integration.IntegrationCell α) : Fraction.Rational :=
  cell.upper - cell.lower

/-- Every cell's ordered range has nonnegative oscillation.

The original range certificate orders the retained lower and upper readings. Their displayed subtraction is therefore
nonnegative. -/
theorem oscillation_nonneg {α : Type} (cell : Integration.IntegrationCell α) :
    0 ≤ cell.oscillation :=
  Arithmetic.sub_nonneg_direct cell.range_valid

end IntegrationCell

/-- Sum weights over the original ordered cell occurrences. -/
@[expose] def integrationWeight {α : Type} : List (Integration.IntegrationCell α) → Fraction.Rational
  | [] => 0
  | cell :: remaining => cell.weight + Purelib.Integration.integrationWeight remaining

/-- Sum each original cell's weight times its lower range endpoint. -/
@[expose] def lowerIntegral {α : Type} : List (Integration.IntegrationCell α) → Fraction.Rational
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.lower + Purelib.Integration.lowerIntegral remaining

/-- Sum each original cell's weight times its upper range endpoint. -/
@[expose] def upperIntegral {α : Type} : List (Integration.IntegrationCell α) → Fraction.Rational
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.upper + Purelib.Integration.upperIntegral remaining

/-- Sum each original cell's weight times its range oscillation. -/
@[expose] def integralOscillation {α : Type} :
    List (Integration.IntegrationCell α) → Fraction.Rational
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.oscillation + Purelib.Integration.integralOscillation remaining

/-- Weighted oscillation is the finite sum of the same retained cell products. -/
theorem integralOscillation_eq_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    integralOscillation cells = (cells.map (fun cell => cell.weight * cell.oscillation)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight * cell.oscillation + integralOscillation remaining =
        cell.weight * cell.oscillation + (remaining.map (fun other => other.weight * other.oscillation)).sum
      rw [integralOscillation_eq_sum remaining]

/-- The empty frontier has zero total weight. -/
@[simp] theorem integrationWeight_nil {α : Type} :
    Integration.integrationWeight ([] : List (Integration.IntegrationCell α)) = 0 := rfl

/-- The empty frontier has zero lower integral. -/
@[simp] theorem lowerIntegral_nil {α : Type} :
    Integration.lowerIntegral ([] : List (Integration.IntegrationCell α)) = 0 := rfl

/-- The empty frontier has zero upper integral. -/
@[simp] theorem upperIntegral_nil {α : Type} :
    Integration.upperIntegral ([] : List (Integration.IntegrationCell α)) = 0 := rfl

/-- The empty frontier has zero weighted oscillation. -/
@[simp] theorem integralOscillation_nil {α : Type} :
    Integration.integralOscillation ([] : List (Integration.IntegrationCell α)) = 0 := rfl

/-- Every finite cell frontier has nonnegative total weight. -/
theorem integrationWeight_nonneg {α : Type} :
    ∀ cells : List (Integration.IntegrationCell α), 0 ≤ Integration.integrationWeight cells
  | [] => le_rfl
  | cell :: remaining =>
      add_nonneg cell.weight_nonnegative
        (Purelib.Integration.integrationWeight_nonneg remaining)

/-- Every finite cell frontier has nonnegative weighted oscillation. -/
theorem integralOscillation_nonneg {α : Type} :
    ∀ cells : List (Integration.IntegrationCell α), 0 ≤ Integration.integralOscillation cells
  | [] => le_rfl
  | cell :: remaining =>
      add_nonneg
        (Arithmetic.mul_nonneg_direct
          cell.weight_nonnegative cell.oscillation_nonneg)
        (Purelib.Integration.integralOscillation_nonneg remaining)

/-- The upper integral equals the lower integral plus the exact weighted oscillation.

The ordered frontier retains every original weight and pair of range readings. Structural recursion transports the tail
equality and the displayed weighted endpoint difference. -/
theorem upperIntegral_eq_lower_add_oscillation {α : Type} :
    ∀ cells : List (Integration.IntegrationCell α),
      Integration.upperIntegral cells = Integration.lowerIntegral cells + Integration.integralOscillation cells
  | [] => by
      exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm
  | cell :: remaining => by
      have inductionHypothesis :=
        Purelib.Integration.upperIntegral_eq_lower_add_oscillation remaining
      dsimp only [Integration.upperIntegral, Integration.lowerIntegral, Integration.integralOscillation,
        Integration.IntegrationCell.oscillation]
      rw [inductionHypothesis]
      ring1

/-- Every frontier's lower integral is at most its upper integral. -/
theorem lowerIntegral_le_upperIntegral {α : Type}
    (cells : List (Integration.IntegrationCell α)) :
    Integration.lowerIntegral cells ≤ Integration.upperIntegral cells := by
  rw [Integration.upperIntegral_eq_lower_add_oscillation]
  exact le_add_of_nonneg_right (Integration.integralOscillation_nonneg cells)

/-- Enclose the finite weighted integral between the frontier's exact lower and upper sums. -/
@[expose] def integralBound {α : Type} (cells : List (Integration.IntegrationCell α)) : Data.Rat.Interval where
  lower := Integration.lowerIntegral cells
  upper := Integration.upperIntegral cells
  valid := Integration.lowerIntegral_le_upperIntegral cells

/-- The integral enclosure's width equals the exact weighted oscillation. -/
theorem integralBound_width {α : Type}
    (cells : List (Integration.IntegrationCell α)) :
    (Integration.integralBound cells).width = Integration.integralOscillation cells := by
  dsimp only [Interval.width, Integration.integralBound]
  rw [Integration.upperIntegral_eq_lower_add_oscillation]
  ring1

/-- Concatenating frontiers adds their total weights. -/
theorem integrationWeight_append {α : Type}
    (left right : List (Integration.IntegrationCell α)) :
    Integration.integrationWeight (left ++ right) =
      Integration.integrationWeight left + Integration.integrationWeight right := by
  induction left with
  | nil =>
      exact (Fraction.Field.zero_add (Integration.integrationWeight right)).symm
  | cons cell remaining inductionHypothesis =>
      change cell.weight + Integration.integrationWeight (remaining ++ right) =
        (cell.weight + Integration.integrationWeight remaining) + Integration.integrationWeight right
      rw [inductionHypothesis]
      exact (Fraction.Field.add_assoc _ _ _).symm

/-- Concatenating frontiers adds their lower integrals. -/
theorem lowerIntegral_append {α : Type}
    (left right : List (Integration.IntegrationCell α)) :
    Integration.lowerIntegral (left ++ right) =
      Integration.lowerIntegral left + Integration.lowerIntegral right := by
  induction left with
  | nil => exact (Fraction.Field.zero_add (Integration.lowerIntegral right)).symm
  | cons cell remaining inductionHypothesis =>
      change cell.weight * cell.lower + Integration.lowerIntegral (remaining ++ right) =
        (cell.weight * cell.lower + Integration.lowerIntegral remaining) + Integration.lowerIntegral right
      rw [inductionHypothesis]
      exact (Fraction.Field.add_assoc _ _ _).symm

/-- Concatenating frontiers adds their upper integrals. -/
theorem upperIntegral_append {α : Type}
    (left right : List (Integration.IntegrationCell α)) :
    Integration.upperIntegral (left ++ right) =
      Integration.upperIntegral left + Integration.upperIntegral right := by
  induction left with
  | nil => exact (Fraction.Field.zero_add (Integration.upperIntegral right)).symm
  | cons cell remaining inductionHypothesis =>
      change cell.weight * cell.upper + Integration.upperIntegral (remaining ++ right) =
        (cell.weight * cell.upper + Integration.upperIntegral remaining) + Integration.upperIntegral right
      rw [inductionHypothesis]
      exact (Fraction.Field.add_assoc _ _ _).symm

/-- Concatenating frontiers adds their weighted oscillations. -/
theorem integralOscillation_append {α : Type}
    (left right : List (Integration.IntegrationCell α)) :
    Integration.integralOscillation (left ++ right) =
      Integration.integralOscillation left + Integration.integralOscillation right := by
  induction left with
  | nil => exact (Fraction.Field.zero_add (Integration.integralOscillation right)).symm
  | cons cell remaining inductionHypothesis =>
      change cell.weight * cell.oscillation + Integration.integralOscillation (remaining ++ right) =
        (cell.weight * cell.oscillation + Integration.integralOscillation remaining) + Integration.integralOscillation
          right
      rw [inductionHypothesis]
      exact (Fraction.Field.add_assoc _ _ _).symm

/-- The enclosure of a concatenated frontier is the interval sum of its two enclosures. -/
theorem integralBound_append {α : Type}
    (left right : List (Integration.IntegrationCell α)) :
    Integration.integralBound (left ++ right) =
      (Integration.integralBound left).add (Integration.integralBound right) := by
  apply Interval.ext
  · exact Integration.lowerIntegral_append left right
  · exact Integration.upperIntegral_append left right

/-- Evaluate a rational observable at each retained cell payload and sum with the original weights. -/
@[expose] def weightedEvaluation {α : Type} (value : α → Fraction.Rational) :
    List (Integration.IntegrationCell α) → Fraction.Rational
  | [] => 0
  | cell :: remaining =>
      cell.weight * value cell.item + Purelib.Integration.weightedEvaluation value remaining

/-- Weighted evaluation is the finite sum of the same original cell products. -/
theorem weightedEvaluation_eq_sum {α : Type} (value : α → Fraction.Rational) :
    ∀ cells : List (IntegrationCell α),
      weightedEvaluation value cells = (cells.map (fun cell => cell.weight * value cell.item)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight * value cell.item + weightedEvaluation value remaining =
        cell.weight * value cell.item + (remaining.map (fun other => other.weight * value other.item)).sum
      rw [weightedEvaluation_eq_sum value remaining]

/-- Pointwise directed discrepancies bound the difference of the original weighted evaluations. -/
private theorem weighted_difference_le {α : Type} (first second cost : α → Fraction.Rational)
    (pointwise : ∀ item, first item - second item ≤ cost item) : ∀ cells : List (IntegrationCell α),
    weightedEvaluation first cells - weightedEvaluation second cells ≤ weightedEvaluation cost cells
  | [] => by
      change (0 : Fraction.Rational) - 0 ≤ 0
      decide
  | cell :: remaining => by
      have head := Arithmetic.mul_le_mul_of_nonneg_left_direct (pointwise cell.item)
        cell.weight_nonnegative
      have tail := weighted_difference_le first second cost pointwise remaining
      change (cell.weight * first cell.item + weightedEvaluation first remaining) -
          (cell.weight * second cell.item + weightedEvaluation second remaining) ≤
        cell.weight * cost cell.item + weightedEvaluation cost remaining
      calc
        _ = cell.weight * (first cell.item - second cell.item) +
            (weightedEvaluation first remaining - weightedEvaluation second remaining) := by ring1
        _ ≤ _ := Arithmetic.add_le_add_direct head tail

/-- Weighted evaluations differ by at most the weighted absolute point discrepancies. -/
theorem weightedEvaluation_abs_sub_le {α : Type} (first second : α → Fraction.Rational)
    (cells : List (IntegrationCell α)) :
    Fraction.abs (weightedEvaluation first cells - weightedEvaluation second cells) ≤
      weightedEvaluation (fun item => Fraction.abs (first item - second item)) cells := by
  have forward := weighted_difference_le first second (fun item => Fraction.abs (first item - second item))
    (fun _ => Fraction.Order.Basic.le_max_left _ _) cells
  have backward := weighted_difference_le second first (fun item => Fraction.abs (first item - second item))
    (fun item => by
      have reverse : second item - first item = -(first item - second item) := by ring1
      rw [reverse]
      exact Fraction.Order.Basic.le_max_right _ _) cells
  change max (weightedEvaluation first cells - weightedEvaluation second cells)
    (-(weightedEvaluation first cells - weightedEvaluation second cells)) ≤ _
  apply Fraction.Order.Basic.max_le forward
  have reverse : -(weightedEvaluation first cells - weightedEvaluation second cells) =
      weightedEvaluation second cells - weightedEvaluation first cells := by ring1
  rw [reverse]
  exact backward

/-- A pointwise observable bound scales by the exact total weight of the original cells. -/
theorem weightedEvaluation_le_weight_mul {α : Type} (value : α → Fraction.Rational)
    (bound : Fraction.Rational) : ∀ (cells : List (IntegrationCell α)),
    (∀ cell ∈ cells, value cell.item ≤ bound) →
      weightedEvaluation value cells ≤ integrationWeight cells * bound
  | [], _ => by
      change (0 : Fraction.Rational) ≤ 0 * bound
      rw [Fraction.Field.zero_mul_direct]
  | cell :: remaining, bounded => by
      have first := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (bounded cell List.mem_cons_self) cell.weight_nonnegative
      have tail := weightedEvaluation_le_weight_mul value bound remaining
        (fun other member => bounded other (List.mem_cons_of_mem cell member))
      change cell.weight * value cell.item + weightedEvaluation value remaining ≤
        (cell.weight + integrationWeight remaining) * bound
      have sum := Arithmetic.add_le_add_direct first tail
      have identity : cell.weight * bound + integrationWeight remaining * bound =
          (cell.weight + integrationWeight remaining) * bound := by ring1
      rw [identity] at sum
      exact sum

/-- The weighted evaluation lies in the integral enclosure when every retained payload value lies in its cell range. -/
theorem weightedEvaluation_mem_integralBound
    {α : Type} (value : α → Fraction.Rational) :
    ∀ {cells : List (Integration.IntegrationCell α)},
      (∀ cell, cell ∈ cells →
        cell.lower ≤ value cell.item ∧ value cell.item ≤ cell.upper) →
      (Integration.integralBound cells).Contains (Integration.weightedEvaluation value cells)
  | [], _ => ⟨le_rfl, le_rfl⟩
  | cell :: remaining, ranges => by
      have head := ranges cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.lower ≤ value candidate.item ∧
            value candidate.item ≤ candidate.upper :=
        fun candidate member =>
          ranges candidate (List.mem_cons_of_mem cell member)
      have inductionHypothesis :=
        Purelib.Integration.weightedEvaluation_mem_integralBound value tail
      constructor
      · dsimp only [Integration.integralBound, Integration.lowerIntegral, Integration.weightedEvaluation]
        exact add_le_add
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            head.1 cell.weight_nonnegative)
          inductionHypothesis.1
      · dsimp only [Integration.integralBound, Integration.upperIntegral, Integration.weightedEvaluation]
        exact add_le_add
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            head.2 cell.weight_nonnegative)
          inductionHypothesis.2

/-- A uniform nonnegative range-oscillation bound controls total oscillation by total weight times that bound. -/
theorem integralOscillation_le_weight_mul
    {α : Type} {delta : Fraction.Rational} (deltaNonnegative : 0 ≤ delta) :
    ∀ {cells : List (Integration.IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.oscillation ≤ delta) →
      Integration.integralOscillation cells ≤ Integration.integrationWeight cells * delta
  | [], _ => by
      simp only [Integration.integralOscillation_nil, Integration.integrationWeight_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, bounded => by
      have head := bounded cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.oscillation ≤ delta :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled :=
        Purelib.Integration.integralOscillation_le_weight_mul deltaNonnegative tail
      dsimp only [Integration.integralOscillation, Integration.integrationWeight]
      calc
        cell.weight * cell.oscillation + Integration.integralOscillation remaining ≤
            cell.weight * delta + Integration.integrationWeight remaining * delta :=
          add_le_add headScaled tailScaled
        _ = (cell.weight + Integration.integrationWeight remaining) * delta := by ring1

/-- A uniform oscillation bound with a strict total-weight budget makes the integral enclosure narrower than epsilon. -/
theorem integralBound_width_lt_of_uniform
    {α : Type} {cells : List (Integration.IntegrationCell α)}
    {delta epsilon : Fraction.Rational} (deltaNonnegative : 0 ≤ delta)
    (bounded : ∀ cell, cell ∈ cells → cell.oscillation ≤ delta)
    (budget : Integration.integrationWeight cells * delta < epsilon) :
    (Integration.integralBound cells).width < epsilon := by
  rw [Integration.integralBound_width]
  exact (Integration.integralOscillation_le_weight_mul deltaNonnegative bounded).trans_lt
    budget
end Purelib.Integration

end
