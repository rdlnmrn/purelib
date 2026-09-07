import FiniteMeasure.ChangeOfMeasure

/-!
# Absolute continuity of finite contents

Absolute continuity is the preservation of zero content for every executable
event.  It is a direct relation between displayed finite contents; every
nonnegative reweighting and every finite Radon--Nikodym witness supplies it.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- `target` is absolutely continuous with respect to `source` when every
zero-source executable event also has zero target content. -/
def AbsolutelyContinuous {α : Type} (target source : FiniteContent α) : Prop :=
  ∀ event : α → Bool, source.measure event = 0 → target.measure event = 0

theorem AbsolutelyContinuous.refl {α : Type} (content : FiniteContent α) :
    content.AbsolutelyContinuous content := by
  intro event zero
  exact zero

theorem AbsolutelyContinuous.trans {α : Type}
    {first second third : FiniteContent α}
    (firstSecond : first.AbsolutelyContinuous second)
    (secondThird : second.AbsolutelyContinuous third) :
    first.AbsolutelyContinuous third := by
  intro event zero
  exact firstSecond event (secondThird event zero)

/-- Every explicit nonnegative density change is absolutely continuous with
respect to its source content. -/
theorem reweight_absolutelyContinuous {α : Type}
    (content : FiniteContent α) (density : α → Coordinate)
    (nonnegative : ∀ item, 0 ≤ density item) :
    (content.reweight density nonnegative).AbsolutelyContinuous content := by
  intro event zero
  exact content.reweight_measure_zero density nonnegative event zero

theorem total_eq_zero_of_absolutelyContinuous {α : Type}
    {target source : FiniteContent α}
    (continuous : target.AbsolutelyContinuous source)
    (sourceZero : source.total = 0) : target.total = 0 := by
  rw [← target.measure_univ]
  apply continuous (fun _ => true)
  rw [source.measure_univ]
  exact sourceZero

/-- Two contents have exactly the same executable zero events. -/
def SameNullEvents {α : Type} (left right : FiniteContent α) : Prop :=
  left.AbsolutelyContinuous right ∧ right.AbsolutelyContinuous left

theorem SameNullEvents.refl {α : Type} (content : FiniteContent α) :
    content.SameNullEvents content :=
  ⟨AbsolutelyContinuous.refl content, AbsolutelyContinuous.refl content⟩

theorem SameNullEvents.symm {α : Type} {left right : FiniteContent α}
    (same : left.SameNullEvents right) : right.SameNullEvents left :=
  ⟨same.2, same.1⟩

theorem SameNullEvents.trans {α : Type}
    {first second third : FiniteContent α}
    (firstSecond : first.SameNullEvents second)
    (secondThird : second.SameNullEvents third) :
    first.SameNullEvents third :=
  ⟨firstSecond.1.trans secondThird.1,
    secondThird.2.trans firstSecond.2⟩

theorem SameNullEvents.measure_eq_zero_iff {α : Type}
    {left right : FiniteContent α} (same : left.SameNullEvents right)
    (event : α → Bool) :
    left.measure event = 0 ↔ right.measure event = 0 :=
  ⟨same.2 event, same.1 event⟩

end FiniteContent

namespace AtomicChange.Witness

/-- The canonical witness supplied by an arbitrary nonnegative reweighting.
-/
def ofReweight {α : Type} (content : FiniteContent α)
    (density : α → Coordinate) (nonnegative : ∀ item, 0 ≤ density item) :
    AtomicChange.Witness content (content.reweight density nonnegative) where
  density := density
  nonnegative := nonnegative
  integral_eq value := content.reweight_integral density nonnegative value

/-- Every reconstructing density proves absolute continuity of target with
respect to source. -/
theorem absolutelyContinuous {α : Type}
    {source target : FiniteContent α}
    (witness : AtomicChange.Witness source target) :
    target.AbsolutelyContinuous source := by
  intro event zero
  have reweightedZero := source.reweight_measure_zero witness.density
    witness.nonnegative event zero
  rw [source.reweight_measure] at reweightedZero
  calc
    target.measure event = source.integral (fun item =>
          witness.density item * Distribution.indicator event item) :=
      witness.measure_eq event
    _ = 0 := reweightedZero

/-- Forward and reverse density witnesses identify exactly the same null
events. -/
theorem sameNullEvents_of_reverse {α : Type}
    {source target : FiniteContent α}
    (forward : AtomicChange.Witness source target)
    (backward : AtomicChange.Witness target source) :
    target.SameNullEvents source :=
  ⟨forward.absolutelyContinuous, backward.absolutelyContinuous⟩

end AtomicChange.Witness

namespace AtomicChange

theorem target_absolutelyContinuous_source {α : Type} [DecidableEq α]
    (change : AtomicChange α) :
    change.target.AbsolutelyContinuous change.source :=
  change.witness.absolutelyContinuous

end AtomicChange

end FiniteMeasure
