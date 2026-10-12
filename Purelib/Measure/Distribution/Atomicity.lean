module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Atomicity
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
/-!
# Atomicity of displayed finite contents

Every positive displayed finite content has a payload with positive singleton
mass.  Hence a content whose singleton events are all null has zero total,
and no displayed finite probability distribution is atomless.  This records
inside the theory the exact boundary separating it from nonatomic measure
spaces.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

/-- Every finite normalized distribution with decidable payload equality has a singleton of positive probability. -/
theorem exists_positive_singleton {α : Type} [DecidableEq α]
    (distribution : Distribution α) :
    ∃ item : α, 0 < distribution.probability (atomEvent item) := by
  exact distribution.toContent.exists_positive_singleton
    (by rw [distribution.toContent_total]; decide)

open Purelib.Data.Rat in
/-- The content underlying a finite normalized distribution with decidable equality cannot be atomless. -/
theorem not_atomless {α : Type} [DecidableEq α]
    (distribution : Distribution α) :
    ¬distribution.toContent.Atomless := by
  intro atomless
  have totalZero :=
    distribution.toContent.total_eq_zero_of_atomless atomless
  rw [distribution.toContent_total] at totalZero
  exact (by decide : (1 : Fraction.Rational) ≠ 0) totalZero

end Distribution

end Purelib.Measure

end
