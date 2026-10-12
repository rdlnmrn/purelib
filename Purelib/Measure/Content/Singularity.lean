module

public import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Mutual singularity of finite contents

Two finite contents are mutually singular when one executable Boolean event
separates their displayed mass.  Hahn certificates separate the computed
positive and negative Jordan contents exactly.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

set_option genInjectivity false in
/-- Retain a Boolean separator with zero left mass outside it and zero right mass inside it.

The separator and both null-event certificates refer to the exact two input contents; no ambient measurable space or
chosen support is introduced. -/
structure MutuallySingular {α : Type}
    (left right : Content α) where
  /-- The exact retained Boolean event separating the two contents. -/ separator : α → Bool
  /-- The original left content gives zero mass to the separator's complement. -/ left_outside_zero : left.measure
    (complementEvent separator) = 0
  /-- The original right content gives zero mass to the separator itself. -/ right_inside_zero : right.measure separator
    = 0

constructive_injectivity MutuallySingular

namespace MutuallySingular

/-- Reverse a retained singularity witness by complementing its exact separator. -/
def symm {α : Type} {left right : Content α}
    (singular : MutuallySingular left right) :
    MutuallySingular right left where
  separator := complementEvent singular.separator
  left_outside_zero := by
    calc
      right.measure (complementEvent (complementEvent singular.separator)) =
          right.measure singular.separator :=
        right.measure_congr _ _ (fun item => by
          unfold complementEvent
          cases singular.separator item <;> rfl)
      _ = 0 := singular.right_inside_zero
  right_inside_zero := singular.left_outside_zero

/-- A left content of total mass zero is singular to any retained right content, using the empty separator. -/
def of_left_total_eq_zero {α : Type} (left right : Content α)
    (zero : left.total = 0) : MutuallySingular left right where
  separator := fun _ => false
  left_outside_zero := by
    calc
      left.measure (complementEvent (fun _ : α => false)) =
          left.measure (fun _ => true) :=
        left.measure_congr _ _ (fun _ => rfl)
      _ = left.total := left.measure_univ
      _ = 0 := zero
  right_inside_zero := right.measure_empty

/-- Any left content is singular to a right content of total mass zero, using the reversed empty-separator witness. -/
def of_right_total_eq_zero {α : Type} (left right : Content α)
    (zero : right.total = 0) : MutuallySingular left right :=
  (of_left_total_eq_zero right left zero).symm

/-- A left content both singular to and absolutely continuous with respect to the same right content has total mass
zero. -/
theorem left_total_eq_zero_of_absolutelyContinuous {α : Type}
    {left right : Content α}
    (singular : MutuallySingular left right)
    (continuous : left.AbsolutelyContinuous right) :
    left.total = 0 := by
  have insideZero : left.measure singular.separator = 0 :=
    continuous singular.separator singular.right_inside_zero
  calc
    left.total = left.measure singular.separator +
        left.measure (complementEvent singular.separator) :=
      (left.add_complement singular.separator).symm
    _ = 0 := by rw [insideZero, singular.left_outside_zero, zero_add]

end MutuallySingular

end Content

end Purelib.Measure

end
