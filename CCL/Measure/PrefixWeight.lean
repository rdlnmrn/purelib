import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.Basic
import FiniteMeasure.Valuation

/-!
# Symbolic dyadic weight of raw CCL prefixes

This is the fair-bit valuation on the raw binary address tree.  It is a
symbolic prefix weight, not geometric area and not the pushforward of
Lebesgue measure through the CCL decoder.  The distinction is explicit in the
API.
-/

namespace CCL.FiniteMeasure

abbrev Word := List Bool

/-- Fair-bit symbolic mass of one finite raw prefix. -/
def rawPrefixWeight (word : Word) : Coordinate :=
  (1 / 2 : Coordinate) ^ word.length

theorem rawPrefixWeight_nonneg (word : Word) :
    0 ≤ rawPrefixWeight word :=
  RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) word.length

theorem rawPrefixWeight_pos (word : Word) :
    0 < rawPrefixWeight word :=
  RFAP.ConstructiveFraction.pow_pos_direct (by decide) word.length

@[simp] theorem rawPrefixWeight_nil : rawPrefixWeight [] = 1 := by
  simp only [rawPrefixWeight, List.length_nil, pow_zero]

theorem rawPrefixWeight_append (left right : Word) :
    rawPrefixWeight (left ++ right) =
      rawPrefixWeight left * rawPrefixWeight right := by
  simp only [rawPrefixWeight, List.length_append, pow_add]

theorem rawPrefixWeight_child (word : Word) (bit : Bool) :
    rawPrefixWeight (word ++ [bit]) = rawPrefixWeight word * (1 / 2) := by
  rw [rawPrefixWeight_append]
  change rawPrefixWeight word * (1 / 2 : Coordinate) ^ 1 = _
  rw [pow_one]

/-- The two raw-bit children conserve their parent's symbolic mass exactly. -/
theorem rawPrefixWeight_children_add (word : Word) :
    rawPrefixWeight (word ++ [false]) +
      rawPrefixWeight (word ++ [true]) = rawPrefixWeight word := by
  rw [rawPrefixWeight_child, rawPrefixWeight_child]
  calc
    rawPrefixWeight word * (1 / 2) + rawPrefixWeight word * (1 / 2) =
        rawPrefixWeight word * ((1 / 2 : Coordinate) + 1 / 2) := by ring1
    _ = rawPrefixWeight word * 1 := by
      have halves : (1 / 2 : Coordinate) + 1 / 2 = 1 := by decide
      rw [halves]
    _ = rawPrefixWeight word := by ring1

/-- Extending a raw prefix cannot increase its symbolic fair-bit mass. -/
theorem rawPrefixWeight_le_of_prefix {stem word : Word}
    (isPrefix : stem.IsPrefix word) :
    rawPrefixWeight word ≤ rawPrefixWeight stem := by
  rcases isPrefix with ⟨suffix, equal⟩
  rw [← equal, rawPrefixWeight_append]
  have suffixLeOne : rawPrefixWeight suffix ≤ 1 := by
    have bound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 2)
      (by decide : (1 / 2 : Coordinate) ≤ 1) suffix.length
    simpa only [rawPrefixWeight, one_pow] using bound
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    suffixLeOne (rawPrefixWeight_nonneg stem)
  simpa only [mul_one] using scaled

/-- Total symbolic mass of a finite raw-prefix frontier. -/
def rawFrontierWeight (frontier : List Word) : Coordinate :=
  (frontier.map rawPrefixWeight).sum

/-- One raw prefix as a generic nonnegative weighted cell. -/
def rawPrefixAtom (word : Word) : _root_.FiniteMeasure.Weighted Word where
  item := word
  weight := rawPrefixWeight word
  nonnegative := rawPrefixWeight_nonneg word

/-- A raw-prefix frontier as an exact generic finite content. -/
def rawPrefixContent (frontier : List Word) :
    _root_.FiniteMeasure.FiniteContent Word where
  atoms := frontier.map rawPrefixAtom

theorem rawPrefixContent_total (frontier : List Word) :
    (rawPrefixContent frontier).total = rawFrontierWeight frontier := by
  induction frontier with
  | nil => rfl
  | cons word remaining inductionHypothesis =>
      simp only [rawPrefixContent, _root_.FiniteMeasure.FiniteContent.total,
        _root_.FiniteMeasure.totalWeight, List.map_cons, rawPrefixAtom,
        rawFrontierWeight, List.sum_cons] at *
      rw [inductionHypothesis]

theorem rawFrontierWeight_nonneg (frontier : List Word) :
    0 ≤ rawFrontierWeight frontier := by
  induction frontier with
  | nil => exact le_rfl
  | cons word remaining inductionHypothesis =>
      simp only [rawFrontierWeight, List.map_cons, List.sum_cons] at *
      exact add_nonneg (rawPrefixWeight_nonneg word) inductionHypothesis

/-- Replace one displayed raw prefix by its two children. -/
def splitRawFrontier (before after : List Word) (word : Word) : List Word :=
  before ++ [word ++ [false], word ++ [true]] ++ after

/-- Every finite raw-prefix split conserves symbolic fair-bit mass. -/
theorem splitRawFrontier_weight (before after : List Word) (word : Word) :
    rawFrontierWeight (splitRawFrontier before after word) =
      rawFrontierWeight (before ++ [word] ++ after) := by
  dsimp only [splitRawFrontier, rawFrontierWeight]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [rawPrefixWeight_children_add]

theorem splitRawFrontier_content_total
    (before after : List Word) (word : Word) :
    (rawPrefixContent (splitRawFrontier before after word)).total =
      (rawPrefixContent (before ++ [word] ++ after)).total := by
  rw [rawPrefixContent_total, rawPrefixContent_total,
    splitRawFrontier_weight]

/-! ## Event bounds on raw-prefix frontiers -/

/-- Attach a finite event status to one fair-bit raw prefix. -/
def rawClassified (word : Word) (status : _root_.FiniteMeasure.Status) :
    _root_.FiniteMeasure.Classified Word where
  atom := rawPrefixAtom word
  status := status

/-- The two binary children of a raw prefix with explicitly supplied event
statuses. -/
def rawBinaryChildren (word : Word)
    (falseStatus trueStatus : _root_.FiniteMeasure.Status) :
    List (_root_.FiniteMeasure.Classified Word) :=
  [rawClassified (word ++ [false]) falseStatus,
    rawClassified (word ++ [true]) trueStatus]

/-- Splitting an unresolved raw prefix into its two binary children is a
certified finite content split for arbitrary constructive child statuses. -/
def rawUnresolvedSplit (word : Word)
    (falseStatus trueStatus : _root_.FiniteMeasure.Status) :
    _root_.FiniteMeasure.Split (β := Word)
      (rawClassified word _root_.FiniteMeasure.Status.unresolved) where
  children := rawBinaryChildren word falseStatus trueStatus
  conserved := by
    simp only [rawBinaryChildren, rawClassified, rawPrefixAtom,
      _root_.FiniteMeasure.classifiedWeight, add_zero]
    exact rawPrefixWeight_children_add word
  statuses := by
    intro child member
    simp only [rawBinaryChildren, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> trivial

/-- Every constructive binary classification of an unresolved raw prefix
narrows its exact lower/upper fair-bit event bound. -/
theorem rawUnresolvedSplit_eventBound_refines
    (word : Word) (falseStatus trueStatus : _root_.FiniteMeasure.Status) :
    _root_.FiniteMeasure.Bound.Refines
      (_root_.FiniteMeasure.eventBound
        (rawBinaryChildren word falseStatus trueStatus))
      (_root_.FiniteMeasure.eventBound
        [rawClassified word _root_.FiniteMeasure.Status.unresolved]) :=
  (rawUnresolvedSplit word falseStatus trueStatus).eventBound_refines

end CCL.FiniteMeasure
