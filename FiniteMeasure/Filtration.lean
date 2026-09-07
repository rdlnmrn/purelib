import mathlib.Data.ConstructiveList
import FiniteMeasure.PartitionRefinement

/-!
# Displayed finite filtrations

A filtration is a finite inductive chain of positive event partitions.  Each
extension carries the explicit certificate that the new partition refines the
previous finest partition.  The construction has a first and last stage and
does not quantify over an unbounded time index.
-/

namespace FiniteMeasure

/-- A nonempty displayed finite chain of increasingly fine positive event
partitions, indexed by its finest partition. -/
inductive FiniteFiltration {α : Type} (distribution : Distribution α) :
    PositiveEventPartition distribution → Type
  | base (partition : PositiveEventPartition distribution) :
      FiniteFiltration distribution partition
  | extend {coarse : PositiveEventPartition distribution}
      (earlier : FiniteFiltration distribution coarse)
      (fine : PositiveEventPartition distribution)
      (refinement : PositivePartitionRefinement fine coarse) :
      FiniteFiltration distribution fine

namespace FiniteFiltration

/-- The first, coarsest partition in the displayed chain. -/
def coarsest {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    FiniteFiltration distribution finest →
      PositiveEventPartition distribution
  | .base partition => partition
  | .extend earlier fine refinement => earlier.coarsest

/-- Number of displayed filtration stages. -/
def depth {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    FiniteFiltration distribution finest → Nat
  | .base partition => 1
  | .extend earlier fine refinement => earlier.depth + 1

/-- Enumerate the partitions from coarsest to finest. -/
def partitions {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution} :
    FiniteFiltration distribution finest →
      List (PositiveEventPartition distribution)
  | .base partition => [partition]
  | .extend earlier fine refinement => earlier.partitions ++ [fine]

theorem partitions_length {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest) :
    filtration.partitions.length = filtration.depth := by
  induction filtration with
  | base partition => rfl
  | extend earlier fine refinement inductionHypothesis =>
      simp only [partitions, List.length_append, List.length_cons,
        List.length_nil, depth, inductionHypothesis]

theorem depth_positive {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest) :
    0 < filtration.depth := by
  induction filtration with
  | base partition => exact Nat.zero_lt_succ 0
  | extend earlier fine refinement inductionHypothesis =>
      unfold depth
      exact Nat.zero_lt_succ _

theorem finest_mem_partitions {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest) :
    finest ∈ filtration.partitions := by
  induction filtration with
  | base partition => exact List.mem_cons_self
  | extend earlier fine refinement inductionHypothesis =>
      apply List.mem_append.mpr
      exact Or.inr List.mem_cons_self

/-- Conditional expectations of one observable at every displayed stage,
ordered from coarsest to finest. -/
def conditionalExpectationValues {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) : List (α → Coordinate) :=
  filtration.partitions.map fun partition =>
    partition.conditionalExpectation value

theorem conditionalExpectationValues_length {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) :
    (filtration.conditionalExpectationValues value).length =
      filtration.depth := by
  unfold conditionalExpectationValues
  rw [List.length_map, filtration.partitions_length]

/-- Every displayed stage of the canonical conditional-expectation process
has the same exact rational expectation as its terminal observable. -/
theorem expectation_conditionalExpectationValue_of_mem {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value candidate : α → Coordinate)
    (member : candidate ∈ filtration.conditionalExpectationValues value) :
    distribution.expectation candidate = distribution.expectation value := by
  unfold conditionalExpectationValues at member
  rcases QuotientFreeList.mem_map.mp member with ⟨partition, partitionMember, same⟩
  subst candidate
  exact partition.expectation_conditionalExpectation value

/-- Exact tower law across the complete displayed refinement chain.  This is
the endpoint martingale identity for the canonical finite process. -/
theorem conditionalExpectation_tower {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) (item : α) :
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

/-- Between-cell variance is monotone from the coarsest to the finest stage
of an arbitrary displayed finite filtration. -/
theorem variance_conditionalExpectation_mono {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) :
    distribution.variance
        (filtration.coarsest.conditionalExpectation value) ≤
      distribution.variance (finest.conditionalExpectation value) := by
  induction filtration with
  | base partition => exact le_rfl
  | @extend coarse earlier fine refinement inductionHypothesis =>
      exact inductionHypothesis.trans
        (refinement.variance_conditionalExpectation_mono value)

/-- A martingale along one displayed filtration.  At each extension the old
value is exactly the conditional expectation of the new value with respect
to the preceding partition. -/
inductive Martingale {α : Type} (distribution : Distribution α) :
    {finest : PositiveEventPartition distribution} →
      (filtration : FiniteFiltration distribution finest) →
      (α → Coordinate) → Type
  | base (partition : PositiveEventPartition distribution)
      (value : α → Coordinate) :
      Martingale distribution (.base partition) value
  | extend {coarse : PositiveEventPartition distribution}
      {earlier : FiniteFiltration distribution coarse}
      {coarseValue : α → Coordinate}
      (past : Martingale distribution earlier coarseValue)
      (fine : PositiveEventPartition distribution)
      (refinement : PositivePartitionRefinement fine coarse)
      (fineValue : α → Coordinate)
      (step : ∀ item,
        coarse.conditionalExpectation fineValue item = coarseValue item) :
      Martingale distribution (.extend earlier fine refinement) fineValue

namespace Martingale

/-- First value of the nonempty displayed martingale. -/
def initialValue {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate} :
    Martingale distribution filtration terminalValue → α → Coordinate
  | .base partition value => value
  | .extend past fine refinement fineValue step => past.initialValue

/-- Enumerate the martingale values in chronological order. -/
def values {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate} :
    Martingale distribution filtration terminalValue →
      List (α → Coordinate)
  | .base partition value => [value]
  | .extend past fine refinement fineValue step =>
      past.values ++ [fineValue]

theorem values_length {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : Martingale distribution filtration terminalValue) :
    martingale.values.length = filtration.depth := by
  induction martingale with
  | base partition value => rfl
  | extend past fine refinement fineValue step inductionHypothesis =>
      simp only [values, List.length_append, List.length_cons,
        List.length_nil, depth, inductionHypothesis]

/-- Every finite martingale preserves exact rational expectation from its
first displayed value to its last. -/
theorem expectation_terminal_eq_initial {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    {filtration : FiniteFiltration distribution finest}
    {terminalValue : α → Coordinate}
    (martingale : Martingale distribution filtration terminalValue) :
    distribution.expectation terminalValue =
      distribution.expectation martingale.initialValue := by
  induction martingale with
  | base partition value => rfl
  | @extend coarse earlier coarseValue past fine refinement fineValue step
      inductionHypothesis =>
      calc
        distribution.expectation fineValue =
            distribution.expectation
              (coarse.conditionalExpectation fineValue) :=
          (coarse.expectation_conditionalExpectation fineValue).symm
        _ = distribution.expectation coarseValue :=
          distribution.expectation_congr _ _ step
        _ = distribution.expectation past.initialValue :=
          inductionHypothesis

end Martingale

/-- Conditional expectations of a fixed terminal observable form the
canonical martingale along every displayed finite filtration. -/
def canonicalMartingale {α : Type} {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) :
    Martingale distribution filtration (finest.conditionalExpectation value) :=
  match filtration with
  | .base partition =>
      .base partition (partition.conditionalExpectation value)
  | .extend earlier fine refinement =>
      .extend (earlier.canonicalMartingale value) fine refinement
        (fine.conditionalExpectation value)
        (refinement.conditionalExpectation_tower value)

theorem canonicalMartingale_initialValue {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (value : α → Coordinate) :
    (filtration.canonicalMartingale value).initialValue =
      filtration.coarsest.conditionalExpectation value := by
  induction filtration with
  | base partition => rfl
  | extend earlier fine refinement inductionHypothesis =>
      exact inductionHypothesis

end FiniteFiltration

end FiniteMeasure
