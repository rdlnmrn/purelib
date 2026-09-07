import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixWeight
import FiniteMeasure.Measurement

/-!
# A finite Boolean algebra of raw-prefix decisions

`RawEvent` is a finite binary decision tree.  Its valuation is computed by
finite recursion, assigning half of the current symbolic weight to each raw
bit branch.  It is deliberately not a set of completed bit streams and does
not assert that the CCL decoder preserves this symbolic valuation.
-/

namespace CCL.FiniteMeasure

/-- A finite decision tree for an event on raw binary prefixes. -/
inductive RawEvent where
  | empty
  | full
  | branch (falseChild trueChild : RawEvent)
deriving DecidableEq, Repr

namespace RawEvent

/-- Exact fair-bit symbolic weight, computed from a finite decision tree. -/
def weight : RawEvent → Coordinate
  | .empty => 0
  | .full => 1
  | .branch falseChild trueChild =>
      (weight falseChild + weight trueChild) * (1 / 2)

/-- Boolean complement of a finite raw-prefix event. -/
def complement : RawEvent → RawEvent
  | .empty => .full
  | .full => .empty
  | .branch falseChild trueChild =>
      .branch falseChild.complement trueChild.complement

/-- Boolean intersection, aligning only the finitely displayed branches. -/
def inter : RawEvent → RawEvent → RawEvent
  | .empty, _ => .empty
  | .full, right => right
  | .branch _ _, .empty => .empty
  | .branch falseChild trueChild, .full =>
      .branch falseChild trueChild
  | .branch falseChild trueChild, .branch falseRight trueRight =>
      .branch (inter falseChild falseRight) (inter trueChild trueRight)

/-- Boolean union, aligning only the finitely displayed branches. -/
def union : RawEvent → RawEvent → RawEvent
  | .empty, right => right
  | .full, _ => .full
  | .branch falseChild trueChild, .empty =>
      .branch falseChild trueChild
  | .branch _ _, .full => .full
  | .branch falseChild trueChild, .branch falseRight trueRight =>
      .branch (union falseChild falseRight) (union trueChild trueRight)

theorem weight_nonneg : ∀ event : RawEvent, 0 ≤ event.weight
  | .empty => le_rfl
  | .full => by decide
  | .branch falseChild trueChild =>
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (add_nonneg (weight_nonneg falseChild) (weight_nonneg trueChild))
        (by decide)

theorem weight_le_one : ∀ event : RawEvent, event.weight ≤ 1
  | .empty => by decide
  | .full => le_rfl
  | .branch falseChild trueChild => by
      have sumLe : falseChild.weight + trueChild.weight ≤
          (1 : Coordinate) + 1 :=
        RFAP.ConstructiveFraction.add_le_add_direct
          (weight_le_one falseChild) (weight_le_one trueChild)
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          sumLe (by decide : (0 : Coordinate) ≤ 1 / 2)
      calc
        (RawEvent.branch falseChild trueChild).weight =
            (falseChild.weight + trueChild.weight) * (1 / 2) := rfl
        _ ≤ ((1 : Coordinate) + 1) * (1 / 2) := scaled
        _ = 1 := by decide

theorem weight_complement : ∀ event : RawEvent,
    event.complement.weight = 1 - event.weight
  | .empty => by decide
  | .full => by decide
  | .branch falseChild trueChild => by
      rw [complement, weight, weight_complement falseChild,
        weight_complement trueChild, weight]
      let half : Coordinate := 1 / 2
      have halves : half + half = 1 := by decide
      change ((1 - falseChild.weight) + (1 - trueChild.weight)) * half =
        1 - (falseChild.weight + trueChild.weight) * half
      calc
        ((1 - falseChild.weight) + (1 - trueChild.weight)) * half =
            (half + half) -
              (falseChild.weight + trueChild.weight) * half := by ring1
        _ = 1 - (falseChild.weight + trueChild.weight) * half := by
          rw [halves]

theorem complement_complement : ∀ event : RawEvent,
    event.complement.complement = event
  | .empty => rfl
  | .full => rfl
  | .branch falseChild trueChild => by
      simp only [complement]
      rw [complement_complement falseChild, complement_complement trueChild]

/-- Finite inclusion-exclusion for the exact raw-prefix valuation. -/
theorem weight_union_add_inter : ∀ left right : RawEvent,
    (left.union right).weight + (left.inter right).weight =
      left.weight + right.weight
  | .empty, right => by
      simp only [union, inter, weight, zero_add, add_zero]
  | .full, right => by
      simp only [union, inter, weight]
  | .branch falseChild trueChild, .empty => by
      simp only [union, inter, weight, add_zero]
  | .branch falseChild trueChild, .full => by
      simp only [union, inter, weight]
      exact add_comm 1
        ((falseChild.weight + trueChild.weight) * (1 / 2))
  | .branch falseChild trueChild, .branch falseRight trueRight => by
      rw [union, inter, weight, weight, weight, weight]
      have falseIdentity := weight_union_add_inter falseChild falseRight
      have trueIdentity := weight_union_add_inter trueChild trueRight
      let half : Coordinate := 1 / 2
      change
        ((falseChild.union falseRight).weight +
            (trueChild.union trueRight).weight) * half +
          ((falseChild.inter falseRight).weight +
            (trueChild.inter trueRight).weight) * half =
        (falseChild.weight + trueChild.weight) * half +
          (falseRight.weight + trueRight.weight) * half
      calc
        ((falseChild.union falseRight).weight +
              (trueChild.union trueRight).weight) * half +
            ((falseChild.inter falseRight).weight +
              (trueChild.inter trueRight).weight) * half =
            (((falseChild.union falseRight).weight +
                (falseChild.inter falseRight).weight) +
              ((trueChild.union trueRight).weight +
                (trueChild.inter trueRight).weight)) * half := by ring1
        _ = ((falseChild.weight + falseRight.weight) +
              (trueChild.weight + trueRight.weight)) * half := by
          rw [falseIdentity, trueIdentity]
        _ = (falseChild.weight + trueChild.weight) * half +
              (falseRight.weight + trueRight.weight) * half := by ring1

theorem weight_union_of_inter_weight_zero {left right : RawEvent}
    (disjoint : (left.inter right).weight = 0) :
    (left.union right).weight = left.weight + right.weight := by
  have valuation := weight_union_add_inter left right
  rw [disjoint, add_zero] at valuation
  exact valuation

/-- Classify one supplied finite query word.  A short query may remain
unresolved; no continuation is manufactured. -/
def classify : RawEvent → Word → _root_.FiniteMeasure.Status
  | .empty, _ => .outside
  | .full, _ => .inside
  | .branch _ _, [] => .unresolved
  | .branch falseChild trueChild, bit :: remaining =>
      if bit then trueChild.classify remaining
      else falseChild.classify remaining

theorem classify_complement : ∀ (event : RawEvent) (word : Word),
    event.complement.classify word =
      match event.classify word with
      | .inside => .outside
      | .outside => .inside
      | .unresolved => .unresolved
  | .empty, _ => rfl
  | .full, _ => rfl
  | .branch _ _, [] => rfl
  | .branch falseChild trueChild, bit :: remaining => by
      cases bit <;>
        simp only [complement, classify, Bool.false_eq_true, ↓reduceIte] <;>
        apply classify_complement

/-- The finite event that accepts exactly after following the displayed raw
prefix; sibling branches are rejected immediately. -/
def ofPrefix : Word → RawEvent
  | [] => .full
  | false :: remaining => .branch (ofPrefix remaining) .empty
  | true :: remaining => .branch .empty (ofPrefix remaining)

theorem ofPrefix_weight : ∀ word : Word,
    (ofPrefix word).weight = rawPrefixWeight word
  | [] => rfl
  | false :: remaining => by
      rw [ofPrefix, weight, ofPrefix_weight remaining, weight]
      simp only [rawPrefixWeight, List.length_cons, pow_succ, add_zero]
  | true :: remaining => by
      rw [ofPrefix, weight, ofPrefix_weight remaining, weight]
      simp only [rawPrefixWeight, List.length_cons, pow_succ, zero_add]

theorem ofPrefix_classify_append (stem suffix : Word) :
    (ofPrefix stem).classify (stem ++ suffix) =
      _root_.FiniteMeasure.Status.inside := by
  induction stem with
  | nil => rfl
  | cons bit remaining inductionHypothesis =>
      cases bit <;>
        simp only [ofPrefix, List.cons_append, classify,
          Bool.false_eq_true, ↓reduceIte] <;>
        exact inductionHypothesis

theorem ofPrefix_classify_self (stem : Word) :
    (ofPrefix stem).classify stem = _root_.FiniteMeasure.Status.inside := by
  simpa only [List.append_nil] using ofPrefix_classify_append stem []

theorem ofPrefix_children_weight (stem : Word) :
    (ofPrefix (stem ++ [false])).weight +
      (ofPrefix (stem ++ [true])).weight = (ofPrefix stem).weight := by
  rw [ofPrefix_weight, ofPrefix_weight, ofPrefix_weight]
  exact rawPrefixWeight_children_add stem

/-! ## Executing a finite decision tree as a classified prefix frontier -/

/-- Classify every word in one supplied finite raw-prefix frontier. -/
def classifyFrontier (event : RawEvent) (frontier : List Word) :
    List (_root_.FiniteMeasure.Classified Word) :=
  frontier.map fun word => rawClassified word (event.classify word)

/-- The generic binary content split specialized to the classifications
computed by a finite decision tree. -/
def classifySplit (event : RawEvent) (word : Word)
    (unresolved : event.classify word =
      _root_.FiniteMeasure.Status.unresolved) :
    _root_.FiniteMeasure.Split (β := Word)
      (rawClassified word (event.classify word)) where
  children := rawBinaryChildren word
    (event.classify (word ++ [false]))
    (event.classify (word ++ [true]))
  conserved := by
    simp only [rawBinaryChildren, rawClassified, rawPrefixAtom,
      _root_.FiniteMeasure.classifiedWeight, add_zero]
    exact rawPrefixWeight_children_add word
  statuses := by
    rw [unresolved]
    intro child member
    trivial

/-- Splitting one unresolved raw query into its two children is a certified
finite event-frontier refinement. -/
theorem classifyFrontier_split_refines (event : RawEvent)
    (before after : List Word) (word : Word)
    (unresolved : event.classify word =
      _root_.FiniteMeasure.Status.unresolved) :
    _root_.FiniteMeasure.FrontierRefines
      (classifyFrontier event (splitRawFrontier before after word))
      (classifyFrontier event (before ++ [word] ++ after)) := by
  simpa only [classifyFrontier, splitRawFrontier, List.map_append,
    List.map_cons, List.map_nil, classifySplit, rawBinaryChildren] using
      (_root_.FiniteMeasure.FrontierRefines.split
        (before.map fun candidate =>
          rawClassified candidate (event.classify candidate))
        (after.map fun candidate =>
          rawClassified candidate (event.classify candidate))
        (rawClassified word (event.classify word))
        (classifySplit event word unresolved))

/-- Terminal classified prefixes produced by executing all branches of the
displayed finite decision tree below one supplied stem. -/
def terminalFrontierAt (stem : Word) : RawEvent →
    List (_root_.FiniteMeasure.Classified Word)
  | .empty => [rawClassified stem _root_.FiniteMeasure.Status.outside]
  | .full => [rawClassified stem _root_.FiniteMeasure.Status.inside]
  | .branch falseChild trueChild =>
      terminalFrontierAt (stem ++ [false]) falseChild ++
        terminalFrontierAt (stem ++ [true]) trueChild

theorem terminalFrontierAt_weight : ∀ (event : RawEvent) (stem : Word),
    _root_.FiniteMeasure.classifiedWeight (terminalFrontierAt stem event) =
      rawPrefixWeight stem
  | .empty, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.classifiedWeight,
        rawClassified, rawPrefixAtom, add_zero]
  | .full, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.classifiedWeight,
        rawClassified, rawPrefixAtom, add_zero]
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt,
        _root_.FiniteMeasure.classifiedWeight_append,
        terminalFrontierAt_weight falseChild,
        terminalFrontierAt_weight trueChild]
      exact rawPrefixWeight_children_add stem

theorem terminalFrontierAt_lower : ∀ (event : RawEvent) (stem : Word),
    _root_.FiniteMeasure.lowerWeight (terminalFrontierAt stem event) =
      rawPrefixWeight stem * event.weight
  | .empty, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.lowerWeight,
        rawClassified, rawPrefixAtom, weight, mul_zero, add_zero]
  | .full, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.lowerWeight,
        rawClassified, rawPrefixAtom, weight, mul_one, add_zero]
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, _root_.FiniteMeasure.lowerWeight_append,
        terminalFrontierAt_lower falseChild,
        terminalFrontierAt_lower trueChild,
        rawPrefixWeight_child, rawPrefixWeight_child, weight]
      let half : Coordinate := 1 / 2
      change rawPrefixWeight stem * half * falseChild.weight +
          rawPrefixWeight stem * half * trueChild.weight =
        rawPrefixWeight stem *
          ((falseChild.weight + trueChild.weight) * half)
      ring1

theorem terminalFrontierAt_upper : ∀ (event : RawEvent) (stem : Word),
    _root_.FiniteMeasure.upperWeight (terminalFrontierAt stem event) =
      rawPrefixWeight stem * event.weight
  | .empty, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.upperWeight,
        rawClassified, rawPrefixAtom, weight, mul_zero, add_zero]
  | .full, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.upperWeight,
        rawClassified, rawPrefixAtom, weight, mul_one, add_zero]
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, _root_.FiniteMeasure.upperWeight_append,
        terminalFrontierAt_upper falseChild,
        terminalFrontierAt_upper trueChild,
        rawPrefixWeight_child, rawPrefixWeight_child, weight]
      let half : Coordinate := 1 / 2
      change rawPrefixWeight stem * half * falseChild.weight +
          rawPrefixWeight stem * half * trueChild.weight =
        rawPrefixWeight stem *
          ((falseChild.weight + trueChild.weight) * half)
      ring1

theorem terminalFrontierAt_unresolved : ∀ (event : RawEvent) (stem : Word),
    _root_.FiniteMeasure.unresolvedWeight (terminalFrontierAt stem event) = 0
  | .empty, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.unresolvedWeight,
        rawClassified, rawPrefixAtom, add_zero]
  | .full, stem => by
      simp only [terminalFrontierAt, _root_.FiniteMeasure.unresolvedWeight,
        rawClassified, rawPrefixAtom, add_zero]
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, _root_.FiniteMeasure.unresolvedWeight_append,
        terminalFrontierAt_unresolved falseChild,
        terminalFrontierAt_unresolved trueChild, add_zero]

/-- Execute every branch starting at the empty raw prefix. -/
def terminalFrontier (event : RawEvent) :
    List (_root_.FiniteMeasure.Classified Word) :=
  terminalFrontierAt [] event

theorem terminalFrontier_weight (event : RawEvent) :
    _root_.FiniteMeasure.classifiedWeight event.terminalFrontier = 1 := by
  rw [terminalFrontier, terminalFrontierAt_weight, rawPrefixWeight_nil]

theorem terminalFrontier_lower (event : RawEvent) :
    _root_.FiniteMeasure.lowerWeight event.terminalFrontier = event.weight := by
  rw [terminalFrontier, terminalFrontierAt_lower, rawPrefixWeight_nil,
    RFAP.ConstructiveFraction.one_mul]

theorem terminalFrontier_upper (event : RawEvent) :
    _root_.FiniteMeasure.upperWeight event.terminalFrontier = event.weight := by
  rw [terminalFrontier, terminalFrontierAt_upper, rawPrefixWeight_nil,
    RFAP.ConstructiveFraction.one_mul]

theorem terminalFrontier_unresolved (event : RawEvent) :
    _root_.FiniteMeasure.unresolvedWeight event.terminalFrontier = 0 :=
  terminalFrontierAt_unresolved event []

/-- Retain one terminal classified cell as the payload of a weighted row. -/
def terminalWeighted
    (entry : _root_.FiniteMeasure.Classified Word) :
    _root_.FiniteMeasure.Weighted (_root_.FiniteMeasure.Classified Word) where
  item := entry
  weight := entry.atom.weight
  nonnegative := entry.atom.nonnegative

/-- Executable event selecting exactly the terminal cells classified inside. -/
def terminalInside
    (entry : _root_.FiniteMeasure.Classified Word) : Bool :=
  match entry.status with
  | .inside => true
  | .outside | .unresolved => false

private theorem totalWeight_terminalWeighted
    (entries : List (_root_.FiniteMeasure.Classified Word)) :
    _root_.FiniteMeasure.totalWeight (entries.map terminalWeighted) =
      _root_.FiniteMeasure.classifiedWeight entries := by
  induction entries with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      simp only [List.map_cons, _root_.FiniteMeasure.totalWeight,
        terminalWeighted, _root_.FiniteMeasure.classifiedWeight,
        inductionHypothesis]

private theorem eventWeight_terminalInside
    (entries : List (_root_.FiniteMeasure.Classified Word)) :
    _root_.FiniteMeasure.eventWeight (entries.map terminalWeighted)
        terminalInside =
      _root_.FiniteMeasure.lowerWeight entries := by
  induction entries with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [List.map_cons, _root_.FiniteMeasure.eventWeight,
          terminalWeighted, terminalInside, _root_.FiniteMeasure.lowerWeight,
          inductionHypothesis]

/-- Exact finite probability distribution on the terminal classified cells
of a raw decision tree.  Its varying-depth rows retain their own prefix
weights and sum to one. -/
def terminalDistribution (event : RawEvent) :
    _root_.FiniteMeasure.Distribution (_root_.FiniteMeasure.Classified Word)
    where
  atoms := event.terminalFrontier.map terminalWeighted
  total_one := by
    rw [totalWeight_terminalWeighted, event.terminalFrontier_weight]

/-- The finite terminal distribution realizes the decision tree's symbolic
weight as an ordinary exact event probability. -/
theorem terminalDistribution_probability_inside (event : RawEvent) :
    event.terminalDistribution.probability terminalInside = event.weight := by
  unfold terminalDistribution _root_.FiniteMeasure.Distribution.probability
  rw [eventWeight_terminalInside, event.terminalFrontier_lower]

/-- The terminal probability table has exactly one row for every displayed
leaf of the finite decision tree. -/
theorem terminalDistribution_atoms_length (event : RawEvent) :
    event.terminalDistribution.atoms.length =
      event.terminalFrontier.length := by
  simp only [terminalDistribution, List.length_map]

/-- A finite raw decision tree compiles to an exact zero-width generic event
bound at its symbolic rational valuation. -/
theorem terminalFrontier_eventBound (event : RawEvent) :
    _root_.FiniteMeasure.eventBound event.terminalFrontier =
      _root_.FiniteMeasure.Bound.exact event.weight := by
  apply _root_.FiniteMeasure.Bound.ext
  · exact event.terminalFrontier_lower
  · exact event.terminalFrontier_upper

/-- A finite raw decision tree is an exact zero-uncertainty event process.
The tree is executed only to its displayed finite terminal frontier. -/
def toEventProcess (event : RawEvent) :
    _root_.FiniteMeasure.EventProcess Word where
  State := Unit
  frontier _ := event.terminalFrontier
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive :=
    _root_.FiniteMeasure.FrontierRefines.refl _
  accurate state epsilon positive := by
    unfold _root_.FiniteMeasure.Resolves
    rw [event.terminalFrontier_unresolved]
    exact positive
  refinesInitial state := _root_.FiniteMeasure.FrontierRefines.refl _

theorem toEventProcess_bound (event : RawEvent) :
    _root_.FiniteMeasure.eventBound
        (event.toEventProcess.frontier event.toEventProcess.initial) =
      _root_.FiniteMeasure.Bound.exact event.weight :=
  event.terminalFrontier_eventBound

end RawEvent

end CCL.FiniteMeasure
