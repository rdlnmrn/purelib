module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Partition.Positive
public import Purelib.Measure.Distribution.Partition.Refinement.Cellwise
public import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Refinement

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

namespace Filtration

/-- Require every retained refinement step of the finite filtration to lift coarse-cellwise observables.

The recursive certificate covers the exact original chain and imposes no extra condition on its initial partition. -/
def CellwiseCompatible {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
      Filtration distribution finest → Prop
  | _, .base _ => True
  | _, .extend earlier fine refinement =>
      earlier.CellwiseCompatible ∧ refinement.LiftsCellwiseObservables
end Filtration

end Purelib.Measure

end
