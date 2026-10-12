module
import Purelib.Measure.Content.Density.Aligned
public import Purelib.Measure.Content.Density.Witness
public import Purelib.Measure.Content.Lp.AlmostEverywhere
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Finite change-of-measure calculus

Finite Radon--Nikodym witnesses compose by multiplying their rational
densities.  Identity witnesses, transitivity, uniqueness away from zero
source mass, and reciprocal round trips are direct finite calculations.
-/

namespace Purelib.Measure

namespace Content.DensityWitness

/-- Certify constant density one as a density witness from the retained content to itself. -/
def refl {α : Type} (content : Content α) :
    AtomicChange.Witness content content where
  density _ := 1
  nonnegative item := by decide
  integral_eq value :=
    content.integral_congr _ _ (fun item => by ring1)

open Purelib.Data.Rat in
/-- Compose two density witnesses through their exact shared middle content using the pointwise product of their
retained densities.

Keep the original source and final target. The original two integral identities and scalar associativity certify the
same product density at every payload. -/
def trans {α : Type} {source middle target : Content α}
    (first : AtomicChange.Witness source middle)
    (second : AtomicChange.Witness middle target) :
    AtomicChange.Witness source target where
  density item := first.density item * second.density item
  nonnegative item := Fraction.Order.Arithmetic.mul_nonneg_direct
    (first.nonnegative item) (second.nonnegative item)
  integral_eq value := by
    calc
      target.integral value = middle.integral (fun item =>
          second.density item * value item) :=
        second.integral_eq value
      _ = source.integral (fun item =>
          first.density item * (second.density item * value item)) :=
        first.integral_eq _
      _ = source.integral (fun item =>
          (first.density item * second.density item) * value item) := by
        exact source.integral_congr _ _ (fun item => by ring1)

open Purelib.Measure
/-- The identity density witness reads one at every payload. -/
@[simp] theorem refl_density {α : Type} (content : Content α)
    (item : α) : (refl content).density item = 1 := rfl

/-- The composed witness reads the product of its two original densities at the same payload. -/
@[simp] theorem trans_density {α : Type}
    {source middle target : Content α}
    (first : AtomicChange.Witness source middle)
    (second : AtomicChange.Witness middle target) (item : α) :
    (trans first second).density item =
      first.density item * second.density item := rfl

/-- Two witnesses between the same original contents have equal densities at every nonzero-weight source occurrence. -/
theorem density_equalAlmostEverywhere {α : Type} [DecidableEq α]
    {source target : Content α}
    (first second : AtomicChange.Witness source target) :
    source.EqualAlmostEverywhere first.density second.density := by
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    have weightPositive : 0 < atom.weight :=
      lt_of_le_of_ne atom.nonnegative (Ne.symm zero)
    have selected : atomEvent atom.item atom.item = true := by
      change decide (atom.item = atom.item) = true
      exact decide_eq_true rfl
    have weightLe : atom.weight ≤ source.measure (atomEvent atom.item) :=
      atom_weight_le_eventWeight_of_mem member selected
    have massPositive : 0 < source.measure (atomEvent atom.item) :=
      weightPositive.trans_le weightLe
    exact Content.DensityWitness.density_eq_of_positive_atom first second atom.item massPositive

/-- Forward and reverse density witnesses multiply to one at every nonzero-weight original source occurrence. -/
theorem density_mul_reverse_eq_one_almostEverywhere
    {α : Type} [DecidableEq α]
    {source target : Content α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    source.EqualAlmostEverywhere
      (fun item => forward.density item * backward.density item)
      (fun _ => 1) :=
  density_equalAlmostEverywhere
    (trans forward backward) (refl source)

/-- Reverse and forward density witnesses multiply to one at every nonzero-weight original target occurrence. -/
theorem density_reverse_mul_eq_one_almostEverywhere
    {α : Type} [DecidableEq α]
    {source target : Content α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    target.EqualAlmostEverywhere
      (fun item => backward.density item * forward.density item)
      (fun _ => 1) :=
  density_equalAlmostEverywhere
    (trans backward forward) (refl target)

/-- The two associations of three composable retained density witnesses have the same pointwise density. -/
theorem trans_assoc_density {α : Type}
    {firstContent secondContent thirdContent fourthContent : Content α}
    (first : AtomicChange.Witness firstContent secondContent)
    (second : AtomicChange.Witness secondContent thirdContent)
    (third : AtomicChange.Witness thirdContent fourthContent)
    (item : α) :
    (trans (trans first second) third).density item =
      (trans first (trans second third)).density item := by
  change (first.density item * second.density item) * third.density item =
    first.density item * (second.density item * third.density item)
  ring1

end Content.DensityWitness

end Purelib.Measure
