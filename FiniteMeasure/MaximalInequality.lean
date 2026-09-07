import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalProjection
import FiniteMeasure.ConditionalJensen
import FiniteMeasure.Filtration

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace FiniteMeasure

/-- Executable upper-level event of one rational observable. -/
def atLeastObservableEvent {α : Type} (threshold : Coordinate)
    (value : α → Coordinate) : α → Bool :=
  fun item => decide (threshold ≤ value item)

/-- First crossings of a displayed observable list while the supplied active
event remains true. -/
def firstCrossingEventsFrom {α : Type} (active : α → Bool)
    (threshold : Coordinate) : List (α → Coordinate) →
      List (α → Bool)
  | [] => []
  | value :: remaining =>
      intersectionEvent active (atLeastObservableEvent threshold value) ::
        firstCrossingEventsFrom
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))
          threshold remaining

/-- First crossings starting with every item active. -/
def firstCrossingEvents {α : Type} (threshold : Coordinate)
    (values : List (α → Coordinate)) : List (α → Bool) :=
  firstCrossingEventsFrom (fun _ => true) threshold values

/-- Event on which no displayed value has yet reached the threshold. -/
def survivingEventFrom {α : Type} (active : α → Bool)
    (threshold : Coordinate) : List (α → Coordinate) → α → Bool
  | [] => active
  | value :: remaining =>
      survivingEventFrom
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value)))
        threshold remaining

theorem survivingEventFrom_append {α : Type} (active : α → Bool)
    (threshold : Coordinate) :
    ∀ (left right : List (α → Coordinate)),
      survivingEventFrom active threshold (left ++ right) =
        survivingEventFrom (survivingEventFrom active threshold left)
          threshold right
  | [], right => rfl
  | value :: remaining, right => by
      simp only [List.cons_append, survivingEventFrom]
      exact survivingEventFrom_append
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value)))
        threshold remaining right

theorem firstCrossingEventsFrom_append {α : Type}
    (active : α → Bool) (threshold : Coordinate) :
    ∀ (left right : List (α → Coordinate)),
      firstCrossingEventsFrom active threshold (left ++ right) =
        firstCrossingEventsFrom active threshold left ++
          firstCrossingEventsFrom
            (survivingEventFrom active threshold left) threshold right
  | [], right => rfl
  | value :: remaining, right => by
      simp only [List.cons_append, firstCrossingEventsFrom,
        survivingEventFrom, List.cons_append, List.cons.injEq, true_and]
      exact firstCrossingEventsFrom_append
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value)))
        threshold remaining right

theorem firstCrossingEventsFrom_length {α : Type}
    (active : α → Bool) (threshold : Coordinate) :
    ∀ values : List (α → Coordinate),
      (firstCrossingEventsFrom active threshold values).length = values.length
  | [] => rfl
  | value :: remaining => by
      simp only [firstCrossingEventsFrom, List.length_cons]
      rw [firstCrossingEventsFrom_length]

/-- The union of the first crossings is exactly the active part of the union
of all upper-level events. -/
theorem unionEvents_firstCrossingEventsFrom {α : Type}
    (threshold : Coordinate) :
    ∀ (values : List (α → Coordinate)) (active : α → Bool) (item : α),
      unionEvents (firstCrossingEventsFrom active threshold values) item =
        intersectionEvent active
          (unionEvents (values.map (atLeastObservableEvent threshold))) item
  | [], active, item => by
      simp only [firstCrossingEventsFrom, unionEvents, List.map_nil,
        intersectionEvent]
      cases active item <;> rfl
  | value :: remaining, active, item => by
      simp only [firstCrossingEventsFrom, List.map_cons, unionEvents,
        unionEvent]
      rw [unionEvents_firstCrossingEventsFrom threshold remaining
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value))) item]
      simp only [intersectionEvent, complementEvent]
      cases active item <;>
        cases atLeastObservableEvent threshold value item <;>
        cases unionEvents
          (remaining.map (atLeastObservableEvent threshold)) item <;> rfl

theorem unionEvents_firstCrossingEvents {α : Type}
    (threshold : Coordinate) (values : List (α → Coordinate)) (item : α) :
    unionEvents (firstCrossingEvents threshold values) item =
      unionEvents (values.map (atLeastObservableEvent threshold)) item := by
  rw [firstCrossingEvents,
    unionEvents_firstCrossingEventsFrom threshold values (fun _ => true) item]
  unfold intersectionEvent
  rfl

/-- First-crossing events are pairwise disjoint on every supplied finite atom
table. -/
theorem firstCrossingEventsFrom_mutuallyDisjointOn {α : Type}
    (atoms : List (Weighted α)) (threshold : Coordinate) :
    ∀ (values : List (α → Coordinate)) (active : α → Bool),
      MutuallyDisjointOn atoms
        (firstCrossingEventsFrom active threshold values)
  | [], active => trivial
  | value :: remaining, active => by
      constructor
      · intro atom member both
        have tailUnion := both.2
        rw [unionEvents_firstCrossingEventsFrom threshold remaining
          (intersectionEvent active
            (complementEvent
              (atLeastObservableEvent threshold value))) atom.item] at tailUnion
        have hitTrue : atLeastObservableEvent threshold value atom.item =
            true := (Bool.and_eq_true_iff.mp both.1).2
        have tailActive : intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value))
              atom.item = true :=
          (Bool.and_eq_true_iff.mp tailUnion).1
        have hitFalse : complementEvent
            (atLeastObservableEvent threshold value) atom.item = true :=
          (Bool.and_eq_true_iff.mp tailActive).2
        unfold complementEvent at hitFalse
        rw [hitTrue] at hitFalse
        exact Bool.noConfusion hitFalse
      · exact firstCrossingEventsFrom_mutuallyDisjointOn atoms threshold
          remaining
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))

theorem firstCrossingEvents_mutuallyDisjointOn {α : Type}
    (atoms : List (Weighted α)) (threshold : Coordinate)
    (values : List (α → Coordinate)) :
    MutuallyDisjointOn atoms (firstCrossingEvents threshold values) :=
  firstCrossingEventsFrom_mutuallyDisjointOn atoms threshold values
    (fun _ => true)

namespace Distribution

/-- A cellwise event indicator tests conditional expectation on that whole
event, not merely one displayed partition cell. -/
theorem eventIntegral_conditionalExpectation_of_indicator_cellwise
    {α : Type} (distribution : Distribution α)
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
    (represented : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator event)) :
    distribution.eventIntegral event
        (partition.conditionalExpectation value) =
      distribution.eventIntegral event value := by
  have orthogonal := partition.expectation_residual_mul_cellwise_eq_zero
    value (Distribution.indicator event) represented
  have rearranged : distribution.expectation (fun item =>
      (value item - partition.conditionalExpectation value item) *
        Distribution.indicator event item) =
      distribution.expectation (fun item =>
        Distribution.indicator event item * value item -
          Distribution.indicator event item *
            partition.conditionalExpectation value item) :=
    distribution.expectation_congr _ _ (fun item => by ring1)
  rw [rearranged, distribution.expectation_sub] at orthogonal
  exact (sub_eq_zero.mp orthogonal).symm

end Distribution

namespace PositiveEventPartition.CellwiseObservable

/-- The indicator of the always-true event is cellwise on every partition. -/
def indicatorTrue {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (fun _ : α => true)) where
  cellValue _ := 1
  agrees _event _eventMember _atom _atomMember _selected := rfl

/-- Intersect two explicitly cellwise events. -/
def indicatorIntersection {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {left right : α → Bool}
    (leftCellwise : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator left))
    (rightCellwise : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator right)) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (intersectionEvent left right)) where
  cellValue event :=
    leftCellwise.cellValue event * rightCellwise.cellValue event
  agrees event eventMember atom atomMember selected := by
    calc
      Distribution.indicator (intersectionEvent left right) atom.item =
          Distribution.indicator left atom.item *
            Distribution.indicator right atom.item := by
        unfold Distribution.indicator intersectionEvent
        cases left atom.item <;> cases right atom.item <;> rfl
      _ = leftCellwise.cellValue event * rightCellwise.cellValue event := by
        rw [leftCellwise.agrees event eventMember atom atomMember selected,
          rightCellwise.agrees event eventMember atom atomMember selected]

/-- Complement an explicitly cellwise event. -/
def indicatorComplement {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {event : α → Bool}
    (represented : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator event)) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (complementEvent event)) where
  cellValue cell := 1 - represented.cellValue cell
  agrees cell cellMember atom atomMember selected := by
    calc
      Distribution.indicator (complementEvent event) atom.item =
          1 - Distribution.indicator event atom.item := by
        unfold Distribution.indicator complementEvent
        cases event atom.item <;> rfl
      _ = 1 - represented.cellValue cell := by
        rw [represented.agrees cell cellMember atom atomMember selected]

/-- The indicator of an upper-level event of a cellwise rational observable
is cellwise, with the comparison executed on its displayed cell value. -/
def indicatorAtLeast {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {value : α → Coordinate}
    (represented : PositiveEventPartition.CellwiseObservable partition value)
    (threshold : Coordinate) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (atLeastObservableEvent threshold value)) where
  cellValue event :=
    match decide (threshold ≤ represented.cellValue event) with
    | true => 1
    | false => 0
  agrees event eventMember atom atomMember selected := by
    have same := represented.agrees event eventMember atom atomMember selected
    unfold Distribution.indicator atLeastObservableEvent
    rw [same]
    rfl

end PositiveEventPartition.CellwiseObservable

namespace PositiveEventPartition

/-- Propositional form of an explicit cellwise certificate.  This wrapper
keeps filtration compatibility proof-irrelevant while every witness inside
it is still a concrete finite cell-value function. -/
def IsCellwiseObservable {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) : Prop :=
  Nonempty (PositiveEventPartition.CellwiseObservable partition value)

end PositiveEventPartition

namespace PositivePartitionRefinement

/-- Structural adaptedness certificate omitted from the bare refinement:
every coarse-cellwise rational observable remains cellwise after refinement. -/
def LiftsCellwiseObservables {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (_refinement : PositivePartitionRefinement fine coarse) : Prop :=
  ∀ {value : α → Coordinate},
    coarse.IsCellwiseObservable value → fine.IsCellwiseObservable value

end PositivePartitionRefinement

namespace FiniteFiltration

/-- Every step of the displayed filtration carries the explicit adaptedness
map needed to reuse coarse event tests on its finer partition. -/
def CellwiseCompatible {α : Type} {distribution : Distribution α} :
    {finest : PositiveEventPartition distribution} →
      FiniteFiltration distribution finest → Prop
  | _, .base _ => True
  | _, .extend earlier fine refinement =>
      earlier.CellwiseCompatible ∧ refinement.LiftsCellwiseObservables

theorem conditionalExpectationValues_extend {α : Type}
    {distribution : Distribution α}
    {coarse fine : PositiveEventPartition distribution}
    (earlier : FiniteFiltration distribution coarse)
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) :
    FiniteFiltration.conditionalExpectationValues
        (FiniteFiltration.extend earlier fine refinement) value =
      earlier.conditionalExpectationValues value ++
        [fine.conditionalExpectation value] := by
  simp only [conditionalExpectationValues, partitions, List.map_append,
    List.map_cons, List.map_nil]

end FiniteFiltration

namespace PositiveEventPartition

/-- Conditional expectation preserves its terminal observable's restricted
integral on every one of its own rational upper-level events. -/
theorem eventIntegral_conditionalExpectation_atLeast {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (threshold : Coordinate) :
    distribution.eventIntegral
        (atLeastObservableEvent threshold
          (partition.conditionalExpectation value))
        (partition.conditionalExpectation value) =
      distribution.eventIntegral
        (atLeastObservableEvent threshold
          (partition.conditionalExpectation value)) value := by
  apply distribution.eventIntegral_conditionalExpectation_of_indicator_cellwise
  exact (partition.conditionalExpectation_cellwise value).indicatorAtLeast
    threshold

end PositiveEventPartition

namespace Distribution

/-- Sum of the restricted integrals of the value observed at each first
crossing. -/
def crossingValueIntegralSumFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Coordinate) : List (α → Coordinate) → Coordinate
  | [] => 0
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (atLeastObservableEvent threshold value)) value +
        distribution.crossingValueIntegralSumFrom
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))
          threshold remaining

/-- Sum of one common terminal observable over the same first-crossing
events. -/
def crossingTerminalIntegralSumFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Coordinate) (terminal : α → Coordinate) :
    List (α → Coordinate) → Coordinate
  | [] => 0
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (atLeastObservableEvent threshold value)) terminal +
        distribution.crossingTerminalIntegralSumFrom
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))
          threshold terminal remaining

/-- Explicit optional-transfer certificate on every displayed first-crossing
event. -/
def CrossingTransferFrom {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Coordinate) (terminal : α → Coordinate) :
    List (α → Coordinate) → Prop
  | [] => True
  | value :: remaining =>
      distribution.eventIntegral
          (intersectionEvent active
            (atLeastObservableEvent threshold value)) value ≤
        distribution.eventIntegral
          (intersectionEvent active
            (atLeastObservableEvent threshold value)) terminal ∧
      distribution.CrossingTransferFrom
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value)))
        threshold terminal remaining

theorem crossingTransferFrom_append {α : Type}
    (distribution : Distribution α) (active : α → Bool)
    (threshold : Coordinate) (terminal : α → Coordinate) :
    ∀ (left right : List (α → Coordinate)),
      distribution.CrossingTransferFrom active threshold terminal left →
      distribution.CrossingTransferFrom
        (survivingEventFrom active threshold left) threshold terminal right →
      distribution.CrossingTransferFrom active threshold terminal
        (left ++ right)
  | [], right, leftTransfer, rightTransfer => rightTransfer
  | value :: remaining, right, leftTransfer, rightTransfer => by
      constructor
      · exact leftTransfer.1
      · exact distribution.crossingTransferFrom_append
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))
          threshold terminal remaining right leftTransfer.2 rightTransfer

theorem threshold_mul_crossingProbabilitySum_le {α : Type}
    (distribution : Distribution α) (threshold : Coordinate) :
    ∀ (values : List (α → Coordinate)) (active : α → Bool),
      threshold *
          ((firstCrossingEventsFrom active threshold values).map
            distribution.probability).sum ≤
        distribution.crossingValueIntegralSumFrom active threshold values
  | [], active => by
      simp only [firstCrossingEventsFrom, List.map_nil, List.sum_nil,
        mul_zero, crossingValueIntegralSumFrom]
      exact le_rfl
  | value :: remaining, active => by
      let crossing := intersectionEvent active
        (atLeastObservableEvent threshold value)
      let laterActive := intersectionEvent active
        (complementEvent (atLeastObservableEvent threshold value))
      have headBound : threshold * distribution.probability crossing ≤
          distribution.eventIntegral crossing value := by
        have restricted := distribution.eventIntegral_mono_on_event crossing
          (fun _ => threshold) value (by
            intro atom member selected
            have hitTrue : atLeastObservableEvent threshold value atom.item =
                true := (Bool.and_eq_true_iff.mp selected).2
            exact of_decide_eq_true hitTrue)
        rw [distribution.eventIntegral_constant] at restricted
        calc
          threshold * distribution.probability crossing =
              distribution.probability crossing * threshold := by ring1
          _ ≤ distribution.eventIntegral crossing value := restricted
      have tailBound :=
        distribution.threshold_mul_crossingProbabilitySum_le threshold
          remaining laterActive
      change threshold * (distribution.probability crossing +
          ((firstCrossingEventsFrom laterActive threshold remaining).map
            distribution.probability).sum) ≤
        distribution.eventIntegral crossing value +
          distribution.crossingValueIntegralSumFrom laterActive threshold
            remaining
      calc
        threshold * (distribution.probability crossing +
            ((firstCrossingEventsFrom laterActive threshold remaining).map
              distribution.probability).sum) =
          threshold * distribution.probability crossing +
            threshold *
              ((firstCrossingEventsFrom laterActive threshold remaining).map
                distribution.probability).sum := by ring1
        _ ≤ distribution.eventIntegral crossing value +
            distribution.crossingValueIntegralSumFrom laterActive threshold
              remaining := add_le_add headBound tailBound

theorem crossingValueIntegralSum_le_terminal {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (terminal : α → Coordinate) :
    ∀ (values : List (α → Coordinate)) (active : α → Bool),
      distribution.CrossingTransferFrom active threshold terminal values →
      distribution.crossingValueIntegralSumFrom active threshold values ≤
        distribution.crossingTerminalIntegralSumFrom active threshold
          terminal values
  | [], active, transfer => le_rfl
  | value :: remaining, active, transfer => by
      exact add_le_add transfer.1
        (distribution.crossingValueIntegralSum_le_terminal threshold terminal
          remaining
          (intersectionEvent active
            (complementEvent (atLeastObservableEvent threshold value)))
          transfer.2)

theorem crossingTerminalIntegralSumFrom_eq {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (terminal : α → Coordinate) :
    ∀ (values : List (α → Coordinate)) (active : α → Bool),
      distribution.crossingTerminalIntegralSumFrom active threshold terminal
          values =
        ((firstCrossingEventsFrom active threshold values).map fun event =>
          distribution.eventIntegral event terminal).sum
  | [], active => rfl
  | value :: remaining, active => by
      simp only [crossingTerminalIntegralSumFrom, firstCrossingEventsFrom,
        List.map_cons, List.sum_cons]
      rw [distribution.crossingTerminalIntegralSumFrom_eq threshold terminal
        remaining
        (intersectionEvent active
          (complementEvent (atLeastObservableEvent threshold value)))]

/-- A two-stage first-crossing transfer consists only of the transfer on the
first event; the terminal-stage comparison is reflexive. -/
theorem crossingTransferFrom_two_of_first {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (first terminal : α → Coordinate)
    (firstTransfer : distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (atLeastObservableEvent threshold first)) first ≤
      distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (atLeastObservableEvent threshold first)) terminal) :
    distribution.CrossingTransferFrom (fun _ => true) threshold terminal
      [first, terminal] := by
  refine ⟨firstTransfer, ?_⟩
  constructor
  · exact le_rfl
  · trivial

/-- Sharp finite L1 maximal inequality from explicit first-crossing transfer
certificates. -/
theorem firstCrossing_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (positive : 0 < threshold) (values : List (α → Coordinate))
    (terminal : α → Coordinate)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item)
    (transfer : distribution.CrossingTransferFrom (fun _ => true)
      threshold terminal values) :
    threshold * distribution.probability
        (unionEvents (values.map (atLeastObservableEvent threshold))) ≤
      distribution.expectation terminal := by
  let crossings := firstCrossingEvents threshold values
  have unionProbabilitySame :
      distribution.probability (unionEvents crossings) =
        distribution.probability
          (unionEvents (values.map (atLeastObservableEvent threshold))) :=
    distribution.probability_congr _ _ (fun item =>
      unionEvents_firstCrossingEvents threshold values item)
  have unionBound := distribution.probability_unionEvents_le_sum crossings
  have scaledUnion :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct unionBound
      positive.le
  have crossingLower :=
    distribution.threshold_mul_crossingProbabilitySum_le threshold values
      (fun _ => true)
  have transferred :=
    distribution.crossingValueIntegralSum_le_terminal threshold terminal
      values (fun _ => true) transfer
  have terminalSum :=
    distribution.crossingTerminalIntegralSumFrom_eq threshold terminal
      values (fun _ => true)
  have packed :=
    distribution.eventIntegrals_sum_le_expectation_of_disjoint_nonnegative
      crossings terminal
      (firstCrossingEvents_mutuallyDisjointOn distribution.atoms threshold
        values)
      terminalNonnegative
  rw [← unionProbabilitySame]
  exact scaledUnion.trans (crossingLower.trans
    (transferred.trans (terminalSum.le.trans packed)))

/-- Two-stage specialization of the sharp finite L1 maximal inequality. -/
theorem twoStage_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (positive : 0 < threshold) (first terminal : α → Coordinate)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item)
    (firstTransfer : distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (atLeastObservableEvent threshold first)) first ≤
      distribution.eventIntegral
        (intersectionEvent (fun _ => true)
          (atLeastObservableEvent threshold first)) terminal) :
    threshold * distribution.probability
        (unionEvents ([first, terminal].map
          (atLeastObservableEvent threshold))) ≤
      distribution.expectation terminal :=
  distribution.firstCrossing_l1_maximal threshold positive
    [first, terminal] terminal terminalNonnegative
    (distribution.crossingTransferFrom_two_of_first threshold first terminal
      firstTransfer)

/-- Sharp two-stage Doob inequality for one displayed conditional
expectation and its nonnegative terminal observable.  The first-crossing
transfer is derived from the partition test-event identity. -/
theorem conditionalExpectation_twoStage_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (positive : 0 < threshold)
    (partition : PositiveEventPartition distribution)
    (terminal : α → Coordinate)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item) :
    threshold * distribution.probability
        (unionEvents
          ([partition.conditionalExpectation terminal, terminal].map
            (atLeastObservableEvent threshold))) ≤
      distribution.expectation terminal := by
  apply distribution.twoStage_l1_maximal threshold positive
    (partition.conditionalExpectation terminal) terminal terminalNonnegative
  exact (partition.eventIntegral_conditionalExpectation_atLeast terminal
    threshold).le

end Distribution

namespace FiniteFiltration

/-- The finite output of running the canonical conditional-expectation
process through first crossings: exact transfer on every crossing and a
cellwise certificate for the event that survives all displayed stages. -/
structure CanonicalCrossingCertificate {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (terminal : α → Coordinate) (active : α → Bool)
    (threshold : Coordinate) : Prop where
  transfer : distribution.CrossingTransferFrom active threshold terminal
    (filtration.conditionalExpectationValues terminal)
  survivingCellwise : finest.IsCellwiseObservable
    (Distribution.indicator
      (survivingEventFrom active threshold
        (filtration.conditionalExpectationValues terminal)))

/-- A cellwise-compatible displayed filtration automatically supplies every
first-crossing transfer equality for its canonical conditional-expectation
process.  The proof is finite induction over the recorded refinements. -/
theorem canonicalCrossingCertificate {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Coordinate) (active : α → Bool)
    (threshold : Coordinate)
    (activeCellwise : filtration.coarsest.IsCellwiseObservable
      (Distribution.indicator active)) :
    CanonicalCrossingCertificate filtration terminal active threshold := by
  induction filtration generalizing active with
  | base partition =>
      rcases activeCellwise with ⟨activeCellwise⟩
      let projected := partition.conditionalExpectation terminal
      let projectedCellwise :=
        partition.conditionalExpectation_cellwise terminal
      let aboveCellwise := projectedCellwise.indicatorAtLeast threshold
      let crossingCellwise :=
        activeCellwise.indicatorIntersection aboveCellwise
      let remainingCellwise := activeCellwise.indicatorIntersection
        aboveCellwise.indicatorComplement
      refine { transfer := ?_, survivingCellwise := ?_ }
      · change distribution.eventIntegral
            (intersectionEvent active
              (atLeastObservableEvent threshold projected)) projected ≤
          distribution.eventIntegral
            (intersectionEvent active
              (atLeastObservableEvent threshold projected)) terminal ∧ True
        constructor
        · exact
            (distribution
              |>.eventIntegral_conditionalExpectation_of_indicator_cellwise
                partition terminal
                (intersectionEvent active
                  (atLeastObservableEvent threshold projected))
                crossingCellwise).le
        · trivial
      · exact ⟨remainingCellwise⟩
  | @extend coarse earlier fine refinement inductionHypothesis =>
      change earlier.CellwiseCompatible ∧
        refinement.LiftsCellwiseObservables at compatible
      let past := inductionHypothesis compatible.1 active activeCellwise
      let pastValues := earlier.conditionalExpectationValues terminal
      let laterActive := survivingEventFrom active threshold pastValues
      have laterActiveCellwiseExists : fine.IsCellwiseObservable
          (Distribution.indicator laterActive) :=
        compatible.2 past.survivingCellwise
      rcases laterActiveCellwiseExists with ⟨laterActiveCellwise⟩
      let projected := fine.conditionalExpectation terminal
      let projectedCellwise := fine.conditionalExpectation_cellwise terminal
      let aboveCellwise := projectedCellwise.indicatorAtLeast threshold
      let crossingCellwise :=
        laterActiveCellwise.indicatorIntersection aboveCellwise
      let remainingCellwise := laterActiveCellwise.indicatorIntersection
        aboveCellwise.indicatorComplement
      have lastTransfer : distribution.CrossingTransferFrom laterActive
          threshold terminal [projected] := by
        constructor
        · exact
            (distribution
              |>.eventIntegral_conditionalExpectation_of_indicator_cellwise
                fine terminal
                (intersectionEvent laterActive
                  (atLeastObservableEvent threshold projected))
                crossingCellwise).le
        · trivial
      have appended : distribution.CrossingTransferFrom active threshold
          terminal (pastValues ++ [projected]) :=
        distribution.crossingTransferFrom_append active threshold terminal
          pastValues [projected] past.transfer lastTransfer
      refine { transfer := ?_, survivingCellwise := ?_ }
      · rw [conditionalExpectationValues_extend]
        exact appended
      · rw [conditionalExpectationValues_extend,
          survivingEventFrom_append]
        exact ⟨remainingCellwise⟩

/-- Canonical first-crossing transfer starting from the whole finite sample
table. -/
theorem canonicalCrossingTransfer {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Coordinate) (threshold : Coordinate) :
    distribution.CrossingTransferFrom (fun _ => true) threshold terminal
      (filtration.conditionalExpectationValues terminal) :=
    (filtration.canonicalCrossingCertificate compatible terminal
    (fun _ => true) threshold
    ⟨PositiveEventPartition.CellwiseObservable.indicatorTrue
      filtration.coarsest⟩).transfer

/-- Sharp finite Doob L1 maximal inequality for every cellwise-compatible
displayed filtration and nonnegative terminal observable. -/
theorem conditionalExpectation_l1_maximal {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item) :
    threshold * distribution.probability
        (unionEvents
          ((filtration.conditionalExpectationValues terminal).map
            (atLeastObservableEvent threshold))) ≤
      distribution.expectation terminal :=
  distribution.firstCrossing_l1_maximal threshold positive
    (filtration.conditionalExpectationValues terminal) terminal
    terminalNonnegative
    (filtration.canonicalCrossingTransfer compatible terminal threshold)

/-- Event that the square of at least one displayed conditional mean reaches
the supplied rational threshold. -/
def conditionalSquareMaximumEvent {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (terminal : α → Coordinate) (threshold : Coordinate) : α → Bool :=
  unionEvents (filtration.partitions.map fun partition =>
    atLeastObservableEvent threshold (fun item =>
      partition.conditionalExpectation terminal item ^ 2))

/-- Event that at least one displayed conditional second moment reaches the
supplied threshold. -/
def conditionalSecondMomentMaximumEvent {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (terminal : α → Coordinate) (threshold : Coordinate) : α → Bool :=
  unionEvents (filtration.partitions.map fun partition =>
    atLeastObservableEvent threshold
      (partition.conditionalExpectation fun item => terminal item ^ 2))

private theorem conditionalSquareEvents_implySecondMomentEvents
    {α : Type} (distribution : Distribution α)
    (terminal : α → Coordinate) (threshold : Coordinate) :
    ∀ partitions : List (PositiveEventPartition distribution),
      EventImpliesOn distribution.atoms
        (unionEvents (partitions.map fun partition =>
          atLeastObservableEvent threshold (fun item =>
            partition.conditionalExpectation terminal item ^ 2)))
        (unionEvents (partitions.map fun partition =>
          atLeastObservableEvent threshold
            (partition.conditionalExpectation fun item =>
              terminal item ^ 2)))
  | [] => by
      intro atom member selected
      exact Bool.noConfusion selected
  | partition :: remaining => by
      intro atom member selected
      cases headSelected : atLeastObservableEvent threshold (fun item =>
          partition.conditionalExpectation terminal item ^ 2) atom.item
      · have tailSelected : unionEvents (remaining.map fun candidate =>
            atLeastObservableEvent threshold (fun item =>
              candidate.conditionalExpectation terminal item ^ 2))
            atom.item = true := by
          simpa only [List.map_cons, unionEvents, unionEvent, headSelected,
            Bool.false_or] using selected
        have tailUpper :=
          conditionalSquareEvents_implySecondMomentEvents distribution
            terminal threshold remaining atom member tailSelected
        simp only [List.map_cons, unionEvents, unionEvent, tailUpper,
          Bool.or_true]
      · have thresholdLower : threshold ≤
            partition.conditionalExpectation terminal atom.item ^ 2 :=
          of_decide_eq_true headSelected
        have squareJensen :=
          partition.conditionalExpectation_sq_le terminal atom member
        have upperSelected : atLeastObservableEvent threshold
            (partition.conditionalExpectation fun item => terminal item ^ 2)
              atom.item = true :=
          decide_eq_true_eq.mpr (thresholdLower.trans squareJensen)
        simp only [List.map_cons, unionEvents, unionEvent, upperSelected,
          Bool.true_or]

/-- Every square-threshold hit of the canonical martingale is also a
conditional-second-moment threshold hit on the same displayed atom. -/
theorem conditionalSquareMaximumEvent_implies_secondMoment {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (terminal : α → Coordinate) (threshold : Coordinate) :
    EventImpliesOn distribution.atoms
      (filtration.conditionalSquareMaximumEvent terminal threshold)
      (filtration.conditionalSecondMomentMaximumEvent terminal threshold) :=
  conditionalSquareEvents_implySecondMomentEvents distribution terminal
    threshold filtration.partitions

/-- Root-free weak-L2 Doob maximal inequality for the canonical conditional
expectations of any rational terminal observable. -/
theorem conditionalExpectation_poweredL2_maximal {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : FiniteFiltration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Coordinate) (threshold : Coordinate)
    (positive : 0 < threshold) :
    threshold * distribution.probability
        (filtration.conditionalSquareMaximumEvent terminal threshold) ≤
      distribution.expectation (fun item => terminal item ^ 2) := by
  have probabilityBound : distribution.probability
        (filtration.conditionalSquareMaximumEvent terminal threshold) ≤
      distribution.probability
        (filtration.conditionalSecondMomentMaximumEvent terminal threshold) :=
    eventWeight_mono
      (filtration.conditionalSquareMaximumEvent_implies_secondMoment
        terminal threshold)
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      probabilityBound positive.le
  have doob := filtration.conditionalExpectation_l1_maximal compatible
    (fun item => terminal item ^ 2) threshold positive (by
      intro atom member
      exact RFAP.ConstructiveFraction.sq_nonneg_direct (terminal atom.item))
  have doobNamed : threshold * distribution.probability
        (filtration.conditionalSecondMomentMaximumEvent terminal threshold) ≤
      distribution.expectation (fun item => terminal item ^ 2) := by
    simpa only [conditionalSecondMomentMaximumEvent,
      conditionalExpectationValues, List.map_map, Function.comp_def]
      using doob
  exact scaled.trans doobNamed

end FiniteFiltration

end FiniteMeasure
