import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Cumulative

/-!
# Constructive finite rational quantiles

A rational-valued finite distribution admits an executable lower quantile at
every displayed level in `(0, 1]`.  The implementation insertion-sorts the
displayed atom table and performs a terminating weighted crossing search.
The result is accompanied by the exact strict-lower and cumulative
inequalities; no infimum, completed real line, or choice principle occurs.
-/

namespace FiniteMeasure

/-- Executable strict rational lower-ray event. -/
def strictlyBelowEvent (threshold : Coordinate) : Coordinate → Bool :=
  fun value => decide (value < threshold)

/-- Executable rational upper-ray event. -/
def atLeastCoordinateEvent (threshold : Coordinate) : Coordinate → Bool :=
  fun value => decide (threshold ≤ value)

private def ValueSorted : List (Weighted Coordinate) → Prop
  | [] => True
  | atom :: remaining =>
      (∀ candidate, candidate ∈ remaining → atom.item ≤ candidate.item) ∧
        ValueSorted remaining

private def insertByValue (atom : Weighted Coordinate) :
    List (Weighted Coordinate) → List (Weighted Coordinate)
  | [] => [atom]
  | candidate :: remaining =>
      if atom.item ≤ candidate.item then
        atom :: candidate :: remaining
      else
        candidate :: insertByValue atom remaining

private def sortByValue :
    List (Weighted Coordinate) → List (Weighted Coordinate)
  | [] => []
  | atom :: remaining => insertByValue atom (sortByValue remaining)

private theorem mem_insertByValue_source
    (atom candidate : Weighted Coordinate) :
    ∀ {atoms : List (Weighted Coordinate)},
      candidate ∈ insertByValue atom atoms →
        candidate = atom ∨ candidate ∈ atoms
  | [], member => by
      simp only [insertByValue, List.mem_cons, List.not_mem_nil,
        or_false] at member
      exact Or.inl member
  | head :: remaining, member => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before] at member
        rcases List.mem_cons.mp member with equal | member
        · exact Or.inl equal
        · rcases List.mem_cons.mp member with equal | tail
          · exact Or.inr (List.mem_cons.mpr (Or.inl equal))
          · exact Or.inr (List.mem_cons.mpr (Or.inr tail))
      · rw [insertByValue, if_neg before] at member
        rcases List.mem_cons.mp member with equal | tail
        · exact Or.inr (List.mem_cons.mpr (Or.inl equal))
        · rcases mem_insertByValue_source atom candidate tail with
            inserted | original
          · exact Or.inl inserted
          · exact Or.inr (List.mem_cons.mpr (Or.inr original))

/-- Every row in the sorted table came from the original displayed table. -/
private theorem mem_sortByValue_source
    (candidate : Weighted Coordinate) :
    ∀ {atoms : List (Weighted Coordinate)},
      candidate ∈ sortByValue atoms → candidate ∈ atoms
  | [], member => (List.not_mem_nil member).elim
  | atom :: remaining, member => by
      rcases mem_insertByValue_source atom candidate member with
          equal | tailMember
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons.mpr
          (Or.inr (mem_sortByValue_source candidate tailMember))

private theorem lowerBound_insertByValue
    (lower : Coordinate) (atom : Weighted Coordinate)
    (atomLower : lower ≤ atom.item) :
    ∀ {atoms : List (Weighted Coordinate)},
      (∀ candidate, candidate ∈ atoms → lower ≤ candidate.item) →
      ∀ candidate, candidate ∈ insertByValue atom atoms →
        lower ≤ candidate.item := by
  intro atoms bounded candidate member
  rcases mem_insertByValue_source atom candidate member with equal | original
  · rw [equal]
    exact atomLower
  · exact bounded candidate original

private theorem insertByValue_sorted
    (atom : Weighted Coordinate) :
    ∀ {atoms : List (Weighted Coordinate)},
      ValueSorted atoms → ValueSorted (insertByValue atom atoms)
  | [], sorted => by
      exact ⟨fun candidate member => by
        exact (List.not_mem_nil member).elim, trivial⟩
  | head :: remaining, sorted => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
        refine ⟨?_, ⟨headLower, tailSorted⟩⟩
        intro candidate member
        simp only [List.mem_cons] at member
        rcases member with equal | tail
        · rw [equal]
          exact before
        · exact before.trans (headLower candidate tail)
      · rw [insertByValue, if_neg before]
        refine ⟨?_, insertByValue_sorted atom tailSorted⟩
        apply lowerBound_insertByValue head.item atom
        · exact (RFAP.ConstructiveFraction.lt_of_not_ge_direct before).le
        · exact headLower

private theorem sortByValue_sorted :
    ∀ atoms : List (Weighted Coordinate), ValueSorted (sortByValue atoms)
  | [] => trivial
  | atom :: remaining =>
      insertByValue_sorted atom (sortByValue_sorted remaining)

private theorem insertByValue_eventWeight
    (atom : Weighted Coordinate) (event : Coordinate → Bool) :
    ∀ atoms : List (Weighted Coordinate),
      eventWeight (insertByValue atom atoms) event =
        eventWeight (atom :: atoms) event
  | [] => rfl
  | head :: remaining => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
      · rw [insertByValue, if_neg before]
        simp only [eventWeight, insertByValue_eventWeight]
        ring1

private theorem insertByValue_totalWeight
    (atom : Weighted Coordinate) :
    ∀ atoms : List (Weighted Coordinate),
      totalWeight (insertByValue atom atoms) =
        totalWeight (atom :: atoms)
  | [] => rfl
  | head :: remaining => by
      by_cases before : atom.item ≤ head.item
      · rw [insertByValue, if_pos before]
      · rw [insertByValue, if_neg before]
        simp only [totalWeight, insertByValue_totalWeight]
        ring1

private theorem sortByValue_eventWeight
    (atoms : List (Weighted Coordinate)) (event : Coordinate → Bool) :
    eventWeight (sortByValue atoms) event = eventWeight atoms event := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [sortByValue, insertByValue_eventWeight]
      simp only [eventWeight, inductionHypothesis]

private theorem sortByValue_totalWeight
    (atoms : List (Weighted Coordinate)) :
    totalWeight (sortByValue atoms) = totalWeight atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [sortByValue, insertByValue_totalWeight]
      simp only [totalWeight, inductionHypothesis]

private theorem eventWeight_strictlyBelow_eq_zero
    (threshold : Coordinate) :
    ∀ {atoms : List (Weighted Coordinate)},
      (∀ atom, atom ∈ atoms → threshold ≤ atom.item) →
      eventWeight atoms (strictlyBelowEvent threshold) = 0
  | [], bounded => rfl
  | atom :: remaining, bounded => by
      have headOrder := bounded atom List.mem_cons_self
      have headNotBelow : ¬atom.item < threshold :=
        fun below => below.2 headOrder
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          threshold ≤ candidate.item :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem atom member)
      simp only [eventWeight, strictlyBelowEvent, headNotBelow, decide_false,
        zero_add, eventWeight_strictlyBelow_eq_zero threshold tailBounded]

private structure SortedQuantileCertificate
    (atoms : List (Weighted Coordinate)) (level : Coordinate) where
  threshold : Coordinate
  selectedAtom : Weighted Coordinate
  selectedMember : selectedAtom ∈ atoms
  selectedValue : selectedAtom.item = threshold
  selectedPositive : 0 < selectedAtom.weight
  below : eventWeight atoms (strictlyBelowEvent threshold) < level
  cumulative : level ≤ eventWeight atoms (atMostEvent threshold)

/-- Proof-independent weighted crossing computation on an already sorted
atom table.  Correctness is supplied separately below. -/
private def sortedQuantileThreshold :
    List (Weighted Coordinate) → Coordinate → Coordinate
  | [], _ => 0
  | atom :: remaining, level =>
      if level ≤ atom.weight then atom.item
      else sortedQuantileThreshold remaining (level - atom.weight)

private def sortedQuantile :
    (atoms : List (Weighted Coordinate)) →
    ValueSorted atoms →
    (level : Coordinate) → 0 < level → level ≤ totalWeight atoms →
    SortedQuantileCertificate atoms level
  | [], sorted, level, positive, bounded => by
      exact (positive.2 bounded).elim
  | atom :: remaining, sorted, level, positive, bounded => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases crosses : level ≤ atom.weight
      · refine
          { threshold := atom.item
            selectedAtom := atom
            selectedMember := List.mem_cons_self
            selectedValue := rfl
            selectedPositive := positive.trans_le crosses
            below := ?_
            cumulative := ?_ }
        · have allLower : ∀ candidate,
              candidate ∈ atom :: remaining → atom.item ≤ candidate.item := by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equal | tail
            · rw [equal]
            · exact headLower candidate tail
          rw [eventWeight_strictlyBelow_eq_zero atom.item allLower]
          exact positive
        · simp only [eventWeight, atMostEvent, le_refl, decide_true]
          exact crosses.trans
            (le_add_of_nonneg_right
              (eventWeight_nonneg remaining (atMostEvent atom.item)))
      · let adjusted := level - atom.weight
        have atomLessLevel : atom.weight < level :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct crosses
        have adjustedPositive : 0 < adjusted :=
          RFAP.ConstructiveFraction.sub_pos_direct atomLessLevel
        have adjustedBounded : adjusted ≤ totalWeight remaining := by
          have shifted :=
            RFAP.ConstructiveFraction.add_le_add_right_direct bounded
              (-atom.weight)
          calc
            adjusted = level + -atom.weight := by
              dsimp only [adjusted]
              ring1
            _ ≤ (atom.weight + totalWeight remaining) + -atom.weight :=
              shifted
            _ = totalWeight remaining := by ring1
        let tailResult := sortedQuantile remaining tailSorted adjusted
          adjustedPositive adjustedBounded
        have headLeThreshold : atom.item ≤ tailResult.threshold := by
          rw [← tailResult.selectedValue]
          exact headLower tailResult.selectedAtom tailResult.selectedMember
        let headContribution : Coordinate :=
          match strictlyBelowEvent tailResult.threshold atom.item with
          | true => atom.weight
          | false => 0
        have headContributionLe : headContribution ≤ atom.weight := by
          dsimp only [headContribution]
          cases strictlyBelowEvent tailResult.threshold atom.item
          · exact atom.nonnegative
          · exact le_rfl
        refine
          { threshold := tailResult.threshold
            selectedAtom := tailResult.selectedAtom
            selectedMember :=
              List.mem_cons_of_mem atom tailResult.selectedMember
            selectedValue := tailResult.selectedValue
            selectedPositive := tailResult.selectedPositive
            below := ?_
            cumulative := ?_ }
        · change headContribution +
              eventWeight remaining
                (strictlyBelowEvent tailResult.threshold) < level
          calc
            headContribution +
                  eventWeight remaining
                    (strictlyBelowEvent tailResult.threshold) ≤
                atom.weight +
                  eventWeight remaining
                    (strictlyBelowEvent tailResult.threshold) :=
              RFAP.ConstructiveFraction.add_le_add_direct
                headContributionLe le_rfl
            _ < atom.weight + adjusted :=
              RFAP.ConstructiveFraction.add_lt_add_left_direct
                tailResult.below atom.weight
            _ = level := by
              dsimp only [adjusted]
              ring1
        · have headSelected :
              atMostEvent tailResult.threshold atom.item = true :=
            decide_eq_true_eq.mpr headLeThreshold
          simp only [eventWeight, headSelected]
          calc
            level = atom.weight + adjusted := by
              dsimp only [adjusted]
              ring1
            _ ≤ atom.weight +
                  eventWeight remaining
                    (atMostEvent tailResult.threshold) :=
              RFAP.ConstructiveFraction.add_le_add_direct le_rfl
                tailResult.cumulative

private theorem sortedQuantile_threshold_eq :
    ∀ (atoms : List (Weighted Coordinate))
      (sorted : ValueSorted atoms)
      (level : Coordinate) (positive : 0 < level)
      (bounded : level ≤ totalWeight atoms),
      (sortedQuantile atoms sorted level positive bounded).threshold =
        sortedQuantileThreshold atoms level
  | [], sorted, level, positive, bounded => by
      exact (positive.2 bounded).elim
  | atom :: remaining, sorted, level, positive, bounded => by
      rcases sorted with ⟨headLower, tailSorted⟩
      by_cases crosses : level ≤ atom.weight
      · simp [sortedQuantile, sortedQuantileThreshold, crosses]
      · let adjusted := level - atom.weight
        have atomLessLevel : atom.weight < level :=
          RFAP.ConstructiveFraction.lt_of_not_ge_direct crosses
        have adjustedPositive : 0 < adjusted :=
          RFAP.ConstructiveFraction.sub_pos_direct atomLessLevel
        have adjustedBounded : adjusted ≤ totalWeight remaining := by
          have shifted :=
            RFAP.ConstructiveFraction.add_le_add_right_direct bounded
              (-atom.weight)
          calc
            adjusted = level + -atom.weight := by
              dsimp only [adjusted]
              ring1
            _ ≤ (atom.weight + totalWeight remaining) + -atom.weight :=
              shifted
            _ = totalWeight remaining := by ring1
        simp only [sortedQuantile, sortedQuantileThreshold, crosses]
        exact sortedQuantile_threshold_eq remaining tailSorted adjusted
          adjustedPositive adjustedBounded

/-- Exact finite lower-quantile certificate at one rational level in
`(0, 1]`. -/
structure QuantileCertificate (distribution : Distribution Coordinate)
    (level : Coordinate) where
  threshold : Coordinate
  selectedAtom : Weighted Coordinate
  selectedMember : selectedAtom ∈ distribution.atoms
  selectedValue : selectedAtom.item = threshold
  selectedPositive : 0 < selectedAtom.weight
  probability_strictlyBelow_lt :
    distribution.probability (strictlyBelowEvent threshold) < level
  level_le_cumulative : level ≤ distribution.cumulative threshold

/-- Execute insertion sort and weighted crossing to obtain a certified
finite rational lower quantile. -/
def Distribution.quantileCertificate
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    QuantileCertificate distribution level := by
  let sortedAtoms := sortByValue distribution.atoms
  have sorted : ValueSorted sortedAtoms := sortByValue_sorted _
  have bounded : level ≤ totalWeight sortedAtoms := by
    rw [sortByValue_totalWeight, distribution.total_one]
    exact atMostOne
  let result := sortedQuantile sortedAtoms sorted level positive bounded
  have resultThreshold : result.threshold =
      sortedQuantileThreshold sortedAtoms level :=
    sortedQuantile_threshold_eq sortedAtoms sorted level positive bounded
  exact
    { threshold := sortedQuantileThreshold sortedAtoms level
      selectedAtom := result.selectedAtom
      selectedMember :=
        mem_sortByValue_source result.selectedAtom result.selectedMember
      selectedValue := result.selectedValue.trans resultThreshold
      selectedPositive := result.selectedPositive
      probability_strictlyBelow_lt := by
        unfold Distribution.probability
        rw [← sortByValue_eventWeight distribution.atoms]
        rw [← resultThreshold]
        exact result.below
      level_le_cumulative := by
        unfold Distribution.cumulative Distribution.probability
        rw [← sortByValue_eventWeight distribution.atoms]
        rw [← resultThreshold]
        exact result.cumulative }

/-- The selected lower quantile as executable rational data. -/
def Distribution.lowerQuantile
    (distribution : Distribution Coordinate)
    (level : Coordinate) (_positive : 0 < level) (_atMostOne : level ≤ 1) :
    Coordinate :=
  sortedQuantileThreshold (sortByValue distribution.atoms) level

/-- The executable lower quantile is the payload of an explicitly displayed
atom in the finite law. -/
theorem Distribution.lowerQuantile_eq_atom_of_mem
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    ∃ atom, atom ∈ distribution.atoms ∧
      atom.item = distribution.lowerQuantile level positive atMostOne := by
  let certificate := distribution.quantileCertificate level positive atMostOne
  exact ⟨certificate.selectedAtom, certificate.selectedMember,
    certificate.selectedValue⟩

/-- Strong support form: the selected lower-quantile value is carried by a
strictly positive-weight displayed atom. -/
theorem Distribution.lowerQuantile_eq_positiveAtom_of_mem
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    ∃ atom, atom ∈ distribution.atoms ∧ 0 < atom.weight ∧
      atom.item = distribution.lowerQuantile level positive atMostOne := by
  let certificate := distribution.quantileCertificate level positive atMostOne
  exact ⟨certificate.selectedAtom, certificate.selectedMember,
    certificate.selectedPositive, certificate.selectedValue⟩

theorem Distribution.probability_strictlyBelow_lowerQuantile_lt
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    distribution.probability
        (strictlyBelowEvent
          (distribution.lowerQuantile level positive atMostOne)) < level :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.probability_strictlyBelow_lt

theorem Distribution.level_le_cumulative_lowerQuantile
    (distribution : Distribution Coordinate)
    (level : Coordinate) (positive : 0 < level) (atMostOne : level ≤ 1) :
    level ≤ distribution.cumulative
      (distribution.lowerQuantile level positive atMostOne) :=
  (distribution.quantileCertificate level positive atMostOne)
    |>.level_le_cumulative

/-- At level one, the executable lower quantile is a finite upper-support
witness whose cumulative probability is exactly one. -/
theorem Distribution.cumulative_lowerQuantile_one_eq_one
    (distribution : Distribution Coordinate) :
    distribution.cumulative
      (distribution.lowerQuantile 1 (by decide) le_rfl) = 1 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · exact distribution.cumulative_le_one _
  · exact distribution.level_le_cumulative_lowerQuantile
      1 (by decide) le_rfl

/-- Every strictly positive-weight displayed atom lies at or below the
level-one lower quantile.  Zero-weight bookkeeping rows are intentionally
irrelevant. -/
theorem Distribution.positiveAtom_le_lowerQuantile_one
    (distribution : Distribution Coordinate)
    (atom : Weighted Coordinate) (member : atom ∈ distribution.atoms)
    (weightPositive : 0 < atom.weight) :
    atom.item ≤ distribution.lowerQuantile 1 (by decide) le_rfl := by
  apply RFAP.ConstructiveFraction.le_of_not_gt_direct
  intro quantileLtAtom
  let maximum := distribution.lowerQuantile 1 (by decide) le_rfl
  have notAtMost : atMostEvent maximum atom.item = false := by
    apply decide_eq_false_iff_not.mpr
    exact quantileLtAtom.2
  have complementSelected : complementEvent (atMostEvent maximum)
      atom.item = true := by
    simp only [complementEvent, notAtMost, Bool.not_false]
  have sum := distribution.probability_add_complement (atMostEvent maximum)
  have cumulativeOne : distribution.probability (atMostEvent maximum) = 1 :=
    distribution.cumulative_lowerQuantile_one_eq_one
  rw [cumulativeOne] at sum
  have complementZero :
      distribution.probability (complementEvent (atMostEvent maximum)) = 0 := by
    calc
      distribution.probability (complementEvent (atMostEvent maximum)) =
          (1 + distribution.probability
            (complementEvent (atMostEvent maximum))) - 1 := by ring1
      _ = 1 - 1 := congrArg (fun value => value - 1) sum
      _ = 0 := by ring1
  have weightLe := atom_weight_le_eventWeight_of_mem member complementSelected
  change atom.weight ≤
    distribution.probability (complementEvent (atMostEvent maximum))
    at weightLe
  rw [complementZero] at weightLe
  exact (weightPositive.2 weightLe).elim

/-- Every rational cut at or above the executable upper-support witness has
cumulative probability exactly one. -/
theorem Distribution.cumulative_eq_one_of_lowerQuantile_one_le
    (distribution : Distribution Coordinate) (cut : Coordinate)
    (upper : distribution.lowerQuantile 1 (by decide) le_rfl ≤ cut) :
    distribution.cumulative cut = 1 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · exact distribution.cumulative_le_one cut
  · rw [← distribution.cumulative_lowerQuantile_one_eq_one]
    exact distribution.cumulative_mono upper

/-- Finite generalized-inverse law: the selected quantile is below a
rational cut exactly when the cumulative mass at that cut reaches its
level. -/
theorem QuantileCertificate.threshold_le_iff_level_le_cumulative
    {distribution : Distribution Coordinate} {level : Coordinate}
    (certificate : QuantileCertificate distribution level)
    (cut : Coordinate) :
    certificate.threshold ≤ cut ↔ level ≤ distribution.cumulative cut := by
  constructor
  · intro thresholdLe
    exact certificate.level_le_cumulative.trans
      (distribution.cumulative_mono thresholdLe)
  · intro levelLe
    by_contra notThresholdLe
    have cutLtThreshold : cut < certificate.threshold :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct notThresholdLe
    have cumulativeLeBelow : distribution.cumulative cut ≤
        distribution.probability
          (strictlyBelowEvent certificate.threshold) := by
      apply eventWeight_mono
      intro atom member selected
      have atomLeCut : atom.item ≤ cut := of_decide_eq_true selected
      exact decide_eq_true_eq.mpr (atomLeCut.trans_lt cutLtThreshold)
    exact certificate.probability_strictlyBelow_lt.2
      (levelLe.trans cumulativeLeBelow)

/-- Higher rational quantile levels produce no smaller selected cut. -/
theorem QuantileCertificate.threshold_mono
    {distribution : Distribution Coordinate}
    {lowerLevel upperLevel : Coordinate}
    (lower : QuantileCertificate distribution lowerLevel)
    (upper : QuantileCertificate distribution upperLevel)
    (levels : lowerLevel ≤ upperLevel) :
    lower.threshold ≤ upper.threshold := by
  apply (lower.threshold_le_iff_level_le_cumulative upper.threshold).2
  exact levels.trans upper.level_le_cumulative

/-- Executable finite rational median certificate. -/
def Distribution.medianCertificate
    (distribution : Distribution Coordinate) :
    QuantileCertificate distribution (1 / 2) :=
  distribution.quantileCertificate (1 / 2) (by decide) (by decide)

/-- Executable lower median. -/
def Distribution.median
    (distribution : Distribution Coordinate) : Coordinate :=
  distribution.lowerQuantile (1 / 2) (by decide) (by decide)

theorem Distribution.probability_strictlyBelow_median_lt_half
    (distribution : Distribution Coordinate) :
    distribution.probability (strictlyBelowEvent distribution.median) < 1 / 2 :=
  distribution.medianCertificate.probability_strictlyBelow_lt

theorem Distribution.half_le_cumulative_median
    (distribution : Distribution Coordinate) :
    1 / 2 ≤ distribution.cumulative distribution.median :=
  distribution.medianCertificate.level_le_cumulative

private theorem complement_strictlyBelowEvent
    (threshold value : Coordinate) :
    complementEvent (strictlyBelowEvent threshold) value =
      atLeastCoordinateEvent threshold value := by
  by_cases below : value < threshold
  · have notAtLeast : ¬threshold ≤ value := below.2
    simp only [complementEvent, strictlyBelowEvent, atLeastCoordinateEvent,
      below, notAtLeast, decide_true, decide_false, Bool.not_true]
  · have atLeast : threshold ≤ value :=
      RFAP.ConstructiveFraction.le_of_not_gt_direct below
    simp only [complementEvent, strictlyBelowEvent, atLeastCoordinateEvent,
      below, atLeast, decide_false, decide_true, Bool.not_false]

/-- At least half of the mass lies on or above the executable lower median. -/
theorem Distribution.half_lt_probability_atLeast_median
    (distribution : Distribution Coordinate) :
    1 / 2 < distribution.probability
      (atLeastCoordinateEvent distribution.median) := by
  have sum := distribution.probability_add_complement
    (strictlyBelowEvent distribution.median)
  have complementProbability := distribution.probability_congr
    (complementEvent (strictlyBelowEvent distribution.median))
    (atLeastCoordinateEvent distribution.median)
    (complement_strictlyBelowEvent distribution.median)
  rw [complementProbability] at sum
  apply RFAP.ConstructiveFraction.lt_of_not_ge_direct
  intro upperLeHalf
  have sumLt :
      distribution.probability (strictlyBelowEvent distribution.median) +
          distribution.probability
            (atLeastCoordinateEvent distribution.median) < 1 := by
    calc
      distribution.probability (strictlyBelowEvent distribution.median) +
            distribution.probability
              (atLeastCoordinateEvent distribution.median) ≤
          distribution.probability
              (strictlyBelowEvent distribution.median) + 1 / 2 :=
        RFAP.ConstructiveFraction.add_le_add_direct le_rfl upperLeHalf
      _ < 1 / 2 + 1 / 2 :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          distribution.probability_strictlyBelow_median_lt_half (1 / 2)
      _ = 1 := by decide
  rw [sum] at sumLt
  exact sumLt.2 le_rfl

end FiniteMeasure
