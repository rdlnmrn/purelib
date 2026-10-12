module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Distribution.Partition.Positive
public import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

namespace PositivePartitionRefinement

open Purelib.Data.Rat in
/-- Require every coarse-cellwise observable to admit a cellwise representation on the exact finer partition.

The property is indexed by the retained refinement and preserves the original observable and shared distribution. -/
def LiftsCellwiseObservables {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (_refinement : PositivePartitionRefinement fine coarse) : Prop :=
  ∀ {value : α → Fraction.Rational},
    coarse.IsCellwiseObservable value → fine.IsCellwiseObservable value

end PositivePartitionRefinement

end Purelib.Measure

end
