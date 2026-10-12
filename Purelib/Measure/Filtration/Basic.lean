module

import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Partition.Positive
public import Purelib.Measure.Distribution.Partition.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

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

set_option genInjectivity false in
/-- Retain a nonempty finite refinement chain of positive partitions of one exact distribution, indexed by its final
partition.

Every extension stores the earlier chain, exact finer partition and its refinement certificate relative to the previous
final partition. -/
inductive Filtration {α : Type} (distribution : Distribution α) :
    PositiveEventPartition distribution → Type
  /-- Start a filtration with the exact retained positive partition. -/ | base (partition : PositiveEventPartition
    distribution) :
      Filtration distribution partition
  /-- Append the exact fine partition and its refinement of the retained earlier chain's final partition. -/ | extend
    {coarse : PositiveEventPartition distribution}
      (earlier : Filtration distribution coarse)
      (fine : PositiveEventPartition distribution)
      (refinement : PositivePartitionRefinement fine coarse) :
      Filtration distribution fine

constructive_injectivity Filtration

namespace Filtration

/-- Read the original first partition from the retained finite refinement chain. -/
@[expose]
def coarsest {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    Filtration distribution finest →
      PositiveEventPartition distribution
  | .base partition => partition
  | .extend earlier fine refinement => earlier.coarsest

/-- Count all retained partitions in the nonempty filtration, including its initial partition. -/
@[expose]
def depth {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    Filtration distribution finest → Nat
  | .base partition => 1
  | .extend earlier fine refinement => earlier.depth + 1

/-- List the exact retained partitions in order from the coarsest to the indexed finest partition. -/
@[expose]
def partitions {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    Filtration distribution finest →
      List (PositiveEventPartition distribution)
  | .base partition => [partition]
  | .extend earlier fine refinement => earlier.partitions ++ [fine]

/-- The retained partition list has length equal to the filtration depth. -/
theorem partitions_length {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest) :
    filtration.partitions.length = filtration.depth := by
  induction filtration with
  | base partition => rfl
  | extend earlier fine refinement inductionHypothesis =>
      simp only [-eq_self, -iff_self, partitions, Append.length_append, List.length_cons,
        List.length_nil, depth, inductionHypothesis]; try rfl

/-- Every retained finite filtration has positive depth. -/
theorem depth_positive {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest) :
    0 < filtration.depth := by
  induction filtration with
  | base partition => exact Nat.zero_lt_succ 0
  | extend earlier fine refinement inductionHypothesis =>
      unfold depth
      exact Nat.zero_lt_succ _

/-- The exact finest partition indexing the filtration occurs in its retained partition list. -/
theorem finest_mem_partitions {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest) :
    finest ∈ filtration.partitions := by
  induction filtration with
  | base partition => exact List.mem_cons_self
  | extend earlier fine refinement inductionHypothesis =>
      apply Membership.mem_append.mpr
      exact Or.inr List.mem_cons_self
namespace Martingale
end Martingale
end Filtration

end Purelib.Measure

end
