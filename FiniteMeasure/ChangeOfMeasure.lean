import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.RadonNikodym
import FiniteMeasure.AlmostEverywhere

/-!
# Finite change-of-measure calculus

Finite Radon--Nikodym witnesses compose by multiplying their rational
densities.  Identity witnesses, transitivity, uniqueness away from zero
source mass, and reciprocal round trips are direct finite calculations.
-/

namespace FiniteMeasure

namespace AtomicChange.Witness

/-- Identity change of finite content has constant density one. -/
def refl {α : Type} (content : FiniteContent α) :
    AtomicChange.Witness content content where
  density _ := 1
  nonnegative item := by decide
  integral_eq value :=
    content.integral_congr _ _ (fun item => by ring1)

/-- Successive finite changes of content multiply their displayed rational
densities. -/
def trans {α : Type} {source middle target : FiniteContent α}
    (first : AtomicChange.Witness source middle)
    (second : AtomicChange.Witness middle target) :
    AtomicChange.Witness source target where
  density item := first.density item * second.density item
  nonnegative item := RFAP.ConstructiveFraction.mul_nonneg_direct
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

@[simp] theorem refl_density {α : Type} (content : FiniteContent α)
    (item : α) : (refl content).density item = 1 := rfl

@[simp] theorem trans_density {α : Type}
    {source middle target : FiniteContent α}
    (first : AtomicChange.Witness source middle)
    (second : AtomicChange.Witness middle target) (item : α) :
    (first.trans second).density item =
      first.density item * second.density item := rfl

/-- The pointwise uniqueness theorem upgrades to the finite
almost-everywhere relation: reconstructing densities may differ only on
displayed zero-weight source atoms. -/
theorem density_equalAlmostEverywhere {α : Type} [DecidableEq α]
    {source target : FiniteContent α}
    (first second : AtomicChange.Witness source target) :
    source.EqualAlmostEverywhere first.density second.density := by
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    have weightPositive : 0 < atom.weight :=
      lt_of_le_of_ne atom.nonnegative (Ne.symm zero)
    have selected : atomEvent atom.item atom.item = true := by
      unfold atomEvent
      simp only [decide_true]
    have weightLe : atom.weight ≤ source.measure (atomEvent atom.item) :=
      atom_weight_le_eventWeight_of_mem member selected
    have massPositive : 0 < source.measure (atomEvent atom.item) :=
      weightPositive.trans_le weightLe
    exact first.density_eq_of_positive_atom second atom.item massPositive

/-- A change followed by a reverse change has density product one away from
zero source mass. -/
theorem density_mul_reverse_eq_one_almostEverywhere
    {α : Type} [DecidableEq α]
    {source target : FiniteContent α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    source.EqualAlmostEverywhere
      (fun item => forward.density item * backward.density item)
      (fun _ => 1) :=
  (forward.trans backward).density_equalAlmostEverywhere (refl source)

/-- The reciprocal round-trip identity also holds in the reverse direction,
relative to target zero mass. -/
theorem density_reverse_mul_eq_one_almostEverywhere
    {α : Type} [DecidableEq α]
    {source target : FiniteContent α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    target.EqualAlmostEverywhere
      (fun item => backward.density item * forward.density item)
      (fun _ => 1) :=
  (backward.trans forward).density_equalAlmostEverywhere (refl target)

/-- Associating three finite changes differently produces the same rational
density pointwise. -/
theorem trans_assoc_density {α : Type}
    {firstContent secondContent thirdContent fourthContent : FiniteContent α}
    (first : AtomicChange.Witness firstContent secondContent)
    (second : AtomicChange.Witness secondContent thirdContent)
    (third : AtomicChange.Witness thirdContent fourthContent)
    (item : α) :
    ((first.trans second).trans third).density item =
      (first.trans (second.trans third)).density item := by
  change (first.density item * second.density item) * third.density item =
    first.density item * (second.density item * third.density item)
  ring1

end AtomicChange.Witness

end FiniteMeasure
