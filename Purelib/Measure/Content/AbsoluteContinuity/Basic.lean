module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Density.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Absolute continuity of finite contents

Absolute continuity is the preservation of zero content for every executable
event.  It is a direct relation between displayed finite contents; every
nonnegative reweighting and every finite Radon--Nikodym witness supplies it.
-/

namespace Purelib.Measure

namespace Content

/-- Require every Boolean event of zero source content to have zero target content. -/
def AbsolutelyContinuous {α : Type} (target source : Content α) : Prop :=
  ∀ event : α → Bool, source.measure event = 0 → target.measure event = 0

/-- Every content is absolutely continuous with respect to itself. -/
theorem AbsolutelyContinuous.refl {α : Type} (content : Content α) :
    content.AbsolutelyContinuous content := by
  intro event zero
  exact zero

/-- Compose absolute continuity through the same retained middle content. -/
theorem AbsolutelyContinuous.trans {α : Type}
    {first second third : Content α}
    (firstSecond : first.AbsolutelyContinuous second)
    (secondThird : second.AbsolutelyContinuous third) :
    first.AbsolutelyContinuous third := by
  intro event zero
  exact firstSecond event (secondThird event zero)

open Purelib.Data.Rat in
/-- Pointwise nonnegative density reweighting is absolutely continuous with respect to the original content. -/
theorem reweight_absolutelyContinuous {α : Type}
    (content : Content α) (density : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ density item) :
    (content.reweight density nonnegative).AbsolutelyContinuous content := by
  intro event zero
  exact content.reweight_measure_zero density nonnegative event zero

/-- Absolute continuity with respect to a zero-total source forces target total zero. -/
theorem total_eq_zero_of_absolutelyContinuous {α : Type}
    {target source : Content α}
    (continuous : target.AbsolutelyContinuous source)
    (sourceZero : source.total = 0) : target.total = 0 := by
  rw [← target.measure_univ]
  apply continuous (fun _ => true)
  rw [source.measure_univ]
  exact sourceZero

/-- Require the two retained contents to be absolutely continuous in both directions. -/
def SameNullEvents {α : Type} (left right : Content α) : Prop :=
  left.AbsolutelyContinuous right ∧ right.AbsolutelyContinuous left

/-- Every retained content has the same null events as itself. -/
theorem SameNullEvents.refl {α : Type} (content : Content α) :
    content.SameNullEvents content :=
  ⟨AbsolutelyContinuous.refl content, AbsolutelyContinuous.refl content⟩

/-- Reverse the relation of having the same zero-content Boolean events. -/
theorem SameNullEvents.symm {α : Type} {left right : Content α}
    (same : left.SameNullEvents right) : right.SameNullEvents left :=
  ⟨same.2, same.1⟩

/-- Compose equality of null events through the same retained middle content. -/
theorem SameNullEvents.trans {α : Type}
    {first second third : Content α}
    (firstSecond : first.SameNullEvents second)
    (secondThird : second.SameNullEvents third) :
    first.SameNullEvents third :=
  ⟨firstSecond.1.trans secondThird.1,
    secondThird.2.trans firstSecond.2⟩

/-- Contents with the same null events measure the supplied event as zero simultaneously. -/
theorem SameNullEvents.measure_eq_zero_iff {α : Type}
    {left right : Content α} (same : left.SameNullEvents right)
    (event : α → Bool) :
    left.measure event = 0 ↔ right.measure event = 0 :=
  ⟨same.2 event, same.1 event⟩

end Content

namespace AtomicChange.Witness
end AtomicChange.Witness

namespace AtomicChange
end AtomicChange

end Purelib.Measure

end
