import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.AtomOperations
import FiniteMeasure.Moments

/-!
# Explicit finite rational mixtures

A mixing coefficient is displayed rational data in `[0,1]`.  A mixture is
formed by scaling two finite atom tables and concatenating them, so all laws
below are exact finite-list calculations.
-/

namespace FiniteMeasure

/-- Certified rational coefficient for a two-way finite mixture. -/
structure MixingWeight where
  coefficient : Coordinate
  nonnegative : 0 ≤ coefficient
  atMostOne : coefficient ≤ 1

namespace MixingWeight

/-- The displayed rational weight assigned to the right-hand component. -/
def complement (weight : MixingWeight) : Coordinate :=
  1 - weight.coefficient

theorem complement_nonnegative (weight : MixingWeight) :
    0 ≤ weight.complement :=
  RFAP.ConstructiveFraction.sub_nonneg_direct weight.atMostOne

theorem coefficient_add_complement (weight : MixingWeight) :
    weight.coefficient + weight.complement = 1 := by
  unfold complement
  ring1

/-- Swap the two displayed mixture coefficients. -/
def swap (weight : MixingWeight) : MixingWeight where
  coefficient := weight.complement
  nonnegative := weight.complement_nonnegative
  atMostOne := by
    unfold complement
    exact sub_le_self 1 weight.nonnegative

@[simp] theorem swap_coefficient (weight : MixingWeight) :
    weight.swap.coefficient = weight.complement := rfl

@[simp] theorem swap_complement (weight : MixingWeight) :
    weight.swap.complement = weight.coefficient := by
  unfold swap complement
  ring1

end MixingWeight

namespace Distribution

/-- Concatenate two explicitly scaled finite probability tables. -/
def mixture {α : Type} (left right : Distribution α)
    (weight : MixingWeight) : Distribution α where
  atoms :=
    scaleAtoms weight.coefficient weight.nonnegative left.atoms ++
      scaleAtoms weight.complement weight.complement_nonnegative right.atoms
  total_one := by
    rw [totalWeight_append, totalWeight_scaleAtoms,
      totalWeight_scaleAtoms, left.total_one, right.total_one,
      mul_one, mul_one, weight.coefficient_add_complement]

/-- A finite mixture displays exactly the concatenated number of atoms. -/
theorem mixture_atoms_length {α : Type} (left right : Distribution α)
    (weight : MixingWeight) :
    (left.mixture right weight).atoms.length =
      left.atoms.length + right.atoms.length := by
  simp only [mixture, List.length_append, scaleAtoms_length]

/-- Exact finite law of total probability for a rational mixture. -/
theorem mixture_probability {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (event : α → Bool) :
    (left.mixture right weight).probability event =
      weight.coefficient * left.probability event +
        weight.complement * right.probability event := by
  unfold mixture probability
  rw [eventWeight_append, eventWeight_scaleAtoms, eventWeight_scaleAtoms]

/-- Exact finite linearity of expectation under rational mixing. -/
theorem mixture_expectation {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (value : α → Coordinate) :
    (left.mixture right weight).expectation value =
      weight.coefficient * left.expectation value +
        weight.complement * right.expectation value := by
  unfold mixture expectation
  rw [expectationWeight_append, expectationWeight_scaleAtoms,
    expectationWeight_scaleAtoms]

/-- Swapping both displayed components and their rational weights preserves
every executable event evaluation. -/
theorem mixture_swap_probability {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (event : α → Bool) :
    (left.mixture right weight).probability event =
      (right.mixture left weight.swap).probability event := by
  rw [left.mixture_probability right weight,
    right.mixture_probability left weight.swap]
  simp only [MixingWeight.swap_coefficient, MixingWeight.swap_complement]
  ring1

/-- Swapping both displayed components and their rational weights preserves
every rational observable evaluation. -/
theorem mixture_swap_expectation {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Coordinate) :
    (left.mixture right weight).expectation value =
      (right.mixture left weight.swap).expectation value := by
  rw [left.mixture_expectation right weight,
    right.mixture_expectation left weight.swap]
  simp only [MixingWeight.swap_coefficient, MixingWeight.swap_complement]
  ring1

/-- Finite within/between variance decomposition for a rational mixture. -/
theorem mixture_variance {α : Type} (left right : Distribution α)
    (weight : MixingWeight) (value : α → Coordinate) :
    (left.mixture right weight).variance value =
      weight.coefficient * left.variance value +
        weight.complement * right.variance value +
        weight.coefficient * weight.complement *
          (left.expectation value - right.expectation value) ^ 2 := by
  rw [(left.mixture right weight).variance_eq_secondMoment_sub_sq,
    left.variance_eq_secondMoment_sub_sq,
    right.variance_eq_secondMoment_sub_sq,
    left.mixture_expectation right weight,
    left.mixture_expectation right weight]
  unfold MixingWeight.complement
  ring1

end Distribution

end FiniteMeasure
