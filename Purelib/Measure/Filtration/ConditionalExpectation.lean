module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Filtration.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
section
public section

/-!
# Displayed finite filtrations

A filtration is a finite inductive chain of positive event partitions.  Each
extension carries the explicit certificate that the new partition refines the
previous finest partition.  The construction has a first and last stage and
does not quantify over an unbounded time index.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat Purelib.Data.List
namespace Filtration

/-- List the original observable's conditional expectations at the filtration's retained partitions in order. -/
@[expose]
def conditionalExpectationValues {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) : List (α → Fraction.Rational) :=
  filtration.partitions.map fun partition =>
    partition.conditionalExpectation value

/-- The conditional-expectation value list has length equal to the exact filtration depth. -/
theorem conditionalExpectationValues_length {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) :
    (filtration.conditionalExpectationValues value).length =
      filtration.depth := by
  unfold conditionalExpectationValues
  rw [Map.length_map, filtration.partitions_length]

/-- Every observable in the retained conditional-expectation list has the original observable's expectation. -/
theorem expectation_conditionalExpectationValue_of_mem {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value candidate : α → Fraction.Rational)
    (member : candidate ∈ filtration.conditionalExpectationValues value) :
    distribution.expectation candidate = distribution.expectation value := by
  unfold conditionalExpectationValues at member
  rcases Map.mem_map.mp member with ⟨partition, partitionMember, same⟩
  subst candidate
  exact partition.expectation_conditionalExpectation value

/-- Conditioning the finest conditional expectation again at the coarsest partition gives the original coarsest
conditional expectation. -/
theorem conditionalExpectation_tower {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) (item : α) :
    filtration.coarsest.conditionalExpectation
        (finest.conditionalExpectation value) item =
      filtration.coarsest.conditionalExpectation value item := by
  induction filtration generalizing value with
  | base partition =>
      exact partition.conditionalExpectation_idempotent value item
  | @extend coarse earlier fine refinement inductionHypothesis =>
      calc
        earlier.coarsest.conditionalExpectation
              (fine.conditionalExpectation value) item =
            earlier.coarsest.conditionalExpectation
              (coarse.conditionalExpectation
                (fine.conditionalExpectation value)) item :=
          (inductionHypothesis
            (fine.conditionalExpectation value)).symm
        _ = earlier.coarsest.conditionalExpectation
              (coarse.conditionalExpectation value) item :=
          earlier.coarsest.conditionalExpectation_congr _ _
            (refinement.conditionalExpectation_tower value) item
        _ = earlier.coarsest.conditionalExpectation value item :=
          inductionHypothesis value

/-- The finest conditional expectation has variance at least that of the coarsest conditional expectation. -/
theorem variance_conditionalExpectation_mono {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (value : α → Fraction.Rational) :
    distribution.variance
        (filtration.coarsest.conditionalExpectation value) ≤
      distribution.variance (finest.conditionalExpectation value) := by
  induction filtration with
  | base partition => exact le_rfl
  | @extend coarse earlier fine refinement inductionHypothesis =>
      exact inductionHypothesis.trans
        (refinement.variance_conditionalExpectation_mono value)
namespace Martingale
end Martingale
end Filtration

end Purelib.Measure

end

end

section
public section

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

open Purelib Purelib.Data.Rat Purelib.Data.List

namespace Filtration

/-- Appending a retained finer partition appends exactly its conditional expectation to the original value list. -/
theorem conditionalExpectationValues_extend {α : Type}
    {distribution : Distribution α}
    {coarse fine : PositiveEventPartition distribution}
    (earlier : Filtration distribution coarse)
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) :
    Filtration.conditionalExpectationValues
        (Filtration.extend earlier fine refinement) value =
      earlier.conditionalExpectationValues value ++
        [fine.conditionalExpectation value] := by
  simp only [-eq_self, -iff_self, conditionalExpectationValues, partitions, Map.map_append,
    List.map_cons, List.map_nil]; try rfl

end Filtration

end Purelib.Measure

end
