module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Weighted.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Predictable transforms and finite optional sampling

A predictable strategy attaches one rational stake to each displayed
martingale step.  The stake is explicitly cellwise on the preceding positive
partition.  Its gain is therefore a finite sum of martingale differences
multiplied by preceding-stage observables, so exact orthogonality makes the
expected total gain zero.

Zero-or-one stakes which decrease pointwise form an explicit finite stopping
strategy.  Its stopped value is the initial value plus the active increments,
and the same finite calculation gives optional sampling.  There is no
unbounded stopping time, convergence theorem, or integrability side condition.
-/

namespace Purelib.Measure

namespace PositiveEventPartition

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a rational stake and its exact cellwise representation on the supplied positive partition.

The stake's values are fixed on each retained cell of the same original distribution, with that dependency carried by
the type. -/
structure PredictableStake {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) where
  /-- The exact rational stake observable on the original payload type. -/ value : α → Fraction.Rational
  /-- The retained cell values and agreement certificate for this stake on the original partition. -/ cellwise :
    PositiveEventPartition.CellwiseObservable partition value

constructive_injectivity PredictableStake

namespace PredictableStake

open Purelib.Data.Rat in
open Purelib.Measure in
/-- Build a predictable stake with the supplied constant value on every retained cell. -/
def constant {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (constant : Fraction.Rational) : PositiveEventPartition.PredictableStake partition where
  value := fun _ => constant
  cellwise :=
    { cellValue := fun _ => constant
      agrees := by
        intro event eventMember atom atomMember selected
        rfl }

end PredictableStake

end PositiveEventPartition

end Purelib.Measure

end
