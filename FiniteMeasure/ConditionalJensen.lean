import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Jensen
import FiniteMeasure.PartitionExpectation
import FiniteMeasure.PoweredLp

/-!
# Finite conditional Jensen inequalities

Conditioning and conditional expectation are finite rational averages.
Jensen's supporting-line proof therefore applies cellwise without any
measurable-function space or limiting argument.  Squaring gives fully
explicit cellwise and partition-level second-moment contraction.
-/

namespace FiniteMeasure

namespace Distribution

/-- Nonnegativity of conditional variance is the square Jensen inequality
on one explicitly positive event. -/
theorem conditionalMean_sq_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    distribution.conditionalMean event value ^ 2 ≤
      distribution.conditionalMean event (fun item => value item ^ 2) := by
  have nonnegative :=
    distribution.conditionalVariance_nonneg event positive value
  rw [distribution.conditionalVariance_eq_secondMoment_sub_sq
    event positive value] at nonnegative
  exact sub_nonneg.mp nonnegative

/-- Conditional Jensen from an explicit supporting line on the displayed
conditioned atom table. -/
theorem conditionalJensen_of_supportingLine {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) (transform : Coordinate → Coordinate)
    (slope : Coordinate)
    (supports : ∀ atom,
      atom ∈ (distribution.conditioned event positive).atoms →
      transform
          ((distribution.conditioned event positive).expectation value) +
          slope *
            (value atom.item -
              (distribution.conditioned event positive).expectation value) ≤
        transform (value atom.item)) :
    transform (distribution.conditionalMean event value) ≤
      distribution.conditionalMean event
        (fun item => transform (value item)) := by
  rw [← distribution.conditioned_expectation_eq_conditionalMean
      event positive value,
    ← distribution.conditioned_expectation_eq_conditionalMean event positive
      (fun item => transform (value item))]
  exact (distribution.conditioned event positive).jensen_of_supportingLine
    value transform slope supports

/-- Conditional Jensen from support inequalities stated directly on the
original displayed rows selected by the conditioning event. -/
theorem conditionalJensen_of_supportingLine_on_event {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) (transform : Coordinate → Coordinate)
    (slope : Coordinate)
    (supports : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
      transform (distribution.conditionalMean event value) +
          slope * (value atom.item -
            distribution.conditionalMean event value) ≤
        transform (value atom.item)) :
    transform (distribution.conditionalMean event value) ≤
      distribution.conditionalMean event
        (fun item => transform (value item)) := by
  let affine : α → Coordinate := fun item =>
    transform (distribution.conditionalMean event value) +
      slope * (value item - distribution.conditionalMean event value)
  have affineMean : distribution.conditionalMean event affine =
      transform (distribution.conditionalMean event value) := by
    dsimp only [affine]
    rw [distribution.conditionalMean_add,
      distribution.conditionalMean_scale,
      distribution.conditionalMean_sub,
      distribution.conditionalMean_constant event positive,
      distribution.conditionalMean_constant event positive]
    ring1
  rw [← affineMean]
  exact distribution.conditionalMean_mono_on_event event positive affine
    (fun item => transform (value item)) supports

/-- Absolute value is conditionally Jensen-contractive on one explicitly
positive event. -/
theorem conditionalMean_rationalSeparation_zero_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    rationalSeparation (distribution.conditionalMean event value) 0 ≤
      distribution.conditionalMean event (fun item =>
        rationalSeparation (value item) 0) := by
  rw [← distribution.conditioned_expectation_eq_conditionalMean
      event positive value,
    ← distribution.conditioned_expectation_eq_conditionalMean event positive
      (fun item => rationalSeparation (value item) 0)]
  exact (distribution.conditioned event positive)
    |>.jensen_rationalSeparation_zero value

end Distribution

namespace PositiveEventPartition

/-- Full pointwise conditional Jensen certificate over a displayed positive
partition.  The caller supplies one rational supporting slope for each cell. -/
theorem conditionalJensen_on_atoms_of_supportingLines {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (transform : Coordinate → Coordinate)
    (slope : (α → Bool) → Coordinate)
    (supports : ∀ event, event ∈ partition.events →
      ∀ atom, atom ∈ distribution.atoms → event atom.item = true →
        transform (distribution.conditionalMean event value) +
            slope event * (value atom.item -
              distribution.conditionalMean event value) ≤
          transform (value atom.item))
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    transform (partition.conditionalExpectation value atom.item) ≤
      partition.conditionalExpectation
        (fun item => transform (value item)) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => transform (value item)) event eventMember atom member
      selected]
  exact distribution.conditionalJensen_of_supportingLine_on_event event
    (partition.positive event eventMember) value transform (slope event)
    (supports event eventMember)

/-- Cellwise conditional Jensen, stated pointwise on every displayed atom. -/
theorem rationalSeparation_conditionalExpectation_zero_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    rationalSeparation
        (partition.conditionalExpectation value atom.item) 0 ≤
      partition.conditionalExpectation
        (fun item => rationalSeparation (value item) 0) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => rationalSeparation (value item) 0) event eventMember atom
      member selected]
  exact distribution.conditionalMean_rationalSeparation_zero_le event
    (partition.positive event eventMember) value

/-- Square Jensen holds pointwise on every displayed partition atom. -/
theorem conditionalExpectation_sq_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (atom : Weighted α)
    (member : atom ∈ distribution.atoms) :
    partition.conditionalExpectation value atom.item ^ 2 ≤
      partition.conditionalExpectation
        (fun item => value item ^ 2) atom.item := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom member selected,
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      (fun item => value item ^ 2) event eventMember atom member selected]
  exact distribution.conditionalMean_sq_le event
    (partition.positive event eventMember) value

/-- Finite conditional expectation contracts the exact rational powered L1
norm. -/
theorem poweredL1_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.poweredL1 (partition.conditionalExpectation value) ≤
      distribution.poweredL1 value := by
  change distribution.expectation (fun item => rationalSeparation
      (partition.conditionalExpectation value item) 0) ≤
    distribution.expectation (fun item => rationalSeparation (value item) 0)
  calc
    distribution.expectation (fun item => rationalSeparation
          (partition.conditionalExpectation value item) 0) ≤
        distribution.expectation
          (partition.conditionalExpectation (fun item =>
            rationalSeparation (value item) 0)) := by
      apply distribution.expectation_mono
      intro atom member
      exact partition.rationalSeparation_conditionalExpectation_zero_le
        value atom member
    _ = distribution.expectation (fun item =>
          rationalSeparation (value item) 0) :=
      partition.expectation_conditionalExpectation _

/-- Finite conditional expectation is a contraction for exact rational L1
distance. -/
theorem l1Distance_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
    distribution.l1Distance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) ≤
      distribution.l1Distance left right := by
  have contraction := partition.poweredL1_conditionalExpectation_le
    (fun item => left item - right item)
  have conditionalDifference :=
    distribution.toFiniteContent.poweredL1_congr
      (partition.conditionalExpectation (fun item => left item - right item))
      (fun item => partition.conditionalExpectation left item -
        partition.conditionalExpectation right item)
      (partition.conditionalExpectation_sub left right)
  change distribution.poweredL1
      (partition.conditionalExpectation (fun item => left item - right item)) =
    distribution.poweredL1 (fun item =>
      partition.conditionalExpectation left item -
        partition.conditionalExpectation right item) at conditionalDifference
  rw [conditionalDifference,
    distribution.poweredL1_sub_eq_l1Distance,
    distribution.poweredL1_sub_eq_l1Distance] at contraction
  exact contraction

/-- Finite conditional expectation contracts the exact rational second
moment.  This is the global square Jensen inequality for a displayed positive
partition. -/
theorem expectation_sq_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.expectation (fun item =>
        partition.conditionalExpectation value item ^ 2) ≤
      distribution.expectation (fun item => value item ^ 2) := by
  have varianceBound := partition.variance_conditionalExpectation_le value
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq,
    partition.expectation_conditionalExpectation value] at varianceBound
  calc
    distribution.expectation (fun item =>
          partition.conditionalExpectation value item ^ 2) =
        (distribution.expectation (fun item =>
            partition.conditionalExpectation value item ^ 2) -
          distribution.expectation value ^ 2) +
            distribution.expectation value ^ 2 := by ring1
    _ ≤ (distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2) +
            distribution.expectation value ^ 2 :=
      add_le_add varianceBound le_rfl
    _ = distribution.expectation (fun item => value item ^ 2) := by ring1

end PositiveEventPartition

end FiniteMeasure
