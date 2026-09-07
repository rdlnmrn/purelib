import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixWeight
import FiniteMeasure.Normalization
import FiniteMeasure.Moments
import FiniteMeasure.LawCoupling

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace CCL.FiniteMeasure

/-- Complete binary frontier at exactly the displayed finite depth below a
raw prefix. -/
def rawExtensions (stem : Word) : Nat → List Word
  | 0 => [stem]
  | depth + 1 =>
      rawExtensions (stem ++ [false]) depth ++
        rawExtensions (stem ++ [true]) depth

/-- Number of rows of one displayed finite frontier selected by an executable
Boolean event. -/
def rawFrontierEventCount : List Word → (Word → Bool) → Nat
  | [], _ => 0
  | word :: remaining, event =>
      (if event word then 1 else 0) + rawFrontierEventCount remaining event

/-- Remove the final bit of a displayed raw word.  The empty word is kept
empty, making this a total finite operation. -/
def rawParent : Word → Word
  | [] => []
  | [_] => []
  | head :: next :: remaining => head :: rawParent (next :: remaining)

theorem rawParent_append_bit (word : Word) (bit : Bool) :
    rawParent (word ++ [bit]) = word := by
  induction word with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next tail =>
          change head :: rawParent ((next :: tail) ++ [bit]) =
            head :: next :: tail
          rw [inductionHypothesis]

/-- Final displayed bit of a nonempty raw word; the empty word receives the
total default `false`. -/
def rawLastBit : Word → Bool
  | [] => false
  | [bit] => bit
  | _ :: next :: remaining => rawLastBit (next :: remaining)

theorem rawLastBit_append_bit (word : Word) (bit : Bool) :
    rawLastBit (word ++ [bit]) = bit := by
  induction word with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next tail =>
          change rawLastBit ((next :: tail) ++ [bit]) = bit
          exact inductionHypothesis

/-- Remove exactly the supplied finite number of final bits. -/
def rawAncestor : Nat → Word → Word
  | 0, word => word
  | count + 1, word => rawAncestor count (rawParent word)

/-- The displayed pair of one-step children of a raw prefix. -/
def rawChildren (word : Word) : List Word :=
  [word ++ [false], word ++ [true]]

/-- Exact rational average of an observable over the two displayed children
of one raw prefix. -/
def rawChildMean (value : Word → Coordinate) (word : Word) : Coordinate :=
  (1 / 2 : Coordinate) * value (word ++ [false]) +
    (1 / 2 : Coordinate) * value (word ++ [true])

/-- Squaring after an explicit two-child average is bounded by averaging the
two displayed squares. -/
theorem rawChildMean_sq_le (value : Word → Coordinate) (word : Word) :
    rawChildMean value word ^ 2 ≤
      rawChildMean (fun child => value child ^ 2) word := by
  let half : Coordinate := 1 / 2
  let leftValue := value (word ++ [false])
  let rightValue := value (word ++ [true])
  change (half * leftValue + half * rightValue) ^ 2 ≤
    half * leftValue ^ 2 + half * rightValue ^ 2
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  have halfSubSquare : half - half ^ 2 = half ^ 2 := by
    decide
  have differenceIdentity :
      half * leftValue ^ 2 + half * rightValue ^ 2 -
          (half * leftValue + half * rightValue) ^ 2 =
        half ^ 2 * (leftValue - rightValue) ^ 2 := by
    calc
      half * leftValue ^ 2 + half * rightValue ^ 2 -
            (half * leftValue + half * rightValue) ^ 2 =
          (half - half ^ 2) * leftValue ^ 2 +
            (half - half ^ 2) * rightValue ^ 2 -
              2 * half ^ 2 * leftValue * rightValue := by ring1
      _ = half ^ 2 * leftValue ^ 2 + half ^ 2 * rightValue ^ 2 -
            2 * half ^ 2 * leftValue * rightValue := by
        rw [halfSubSquare]
      _ = half ^ 2 * (leftValue - rightValue) ^ 2 := by ring1
  rw [differenceIdentity]
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.sq_nonneg_direct half)
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- Iterate the explicit two-child averaging operation exactly the supplied
finite number of times.  This is a backward value table, not a limit. -/
def rawBackwardMean : Nat → (Word → Coordinate) → Word → Coordinate
  | 0, value => value
  | extra + 1, value => rawBackwardMean extra (rawChildMean value)

/-- Exact within-child variance of the two displayed child values. -/
def rawChildVariance (value : Word → Coordinate) (word : Word) : Coordinate :=
  rawChildMean (fun child => value child ^ 2) word -
    rawChildMean value word ^ 2

theorem rawChildVariance_nonnegative
    (value : Word → Coordinate) (word : Word) :
    0 ≤ rawChildVariance value word :=
  RFAP.ConstructiveFraction.sub_nonneg_direct (rawChildMean_sq_le value word)

theorem rawChildMean_nonnegative (value : Word → Coordinate)
    (nonnegative : ∀ word, 0 ≤ value word) (word : Word) :
    0 ≤ rawChildMean value word := by
  unfold rawChildMean
  exact add_nonneg
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (nonnegative (word ++ [false])))
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (nonnegative (word ++ [true])))

/-- Explicit residual variance accumulated while folding a payoff backward
through a displayed finite number of binary levels. -/
def rawBackwardVariance : Nat → (Word → Coordinate) → Word → Coordinate
  | 0, _ => fun _ => 0
  | extra + 1, value => fun word =>
      rawBackwardMean extra (rawChildVariance value) word +
        rawBackwardVariance extra (rawChildMean value) word

/-- Pointwise equality is sufficient for equality of the displayed
two-child means at any requested word. -/
theorem rawChildMean_congr (left right : Word → Coordinate)
    (pointwise : ∀ word, left word = right word) (word : Word) :
    rawChildMean left word = rawChildMean right word := by
  unfold rawChildMean
  rw [pointwise (word ++ [false]), pointwise (word ++ [true])]

/-- Pointwise equality is sufficient for equality of the displayed
two-child variances at any requested word. -/
theorem rawChildVariance_congr (left right : Word → Coordinate)
    (pointwise : ∀ word, left word = right word) (word : Word) :
    rawChildVariance left word = rawChildVariance right word := by
  unfold rawChildVariance
  rw [rawChildMean_congr _ _
      (fun child => congrArg (fun value => value ^ 2) (pointwise child)) word,
    rawChildMean_congr left right pointwise word]

/-- The finite backward mean respects pointwise equality without requiring
equality of the function-valued input. -/
theorem rawBackwardMean_congr (left right : Word → Coordinate)
    (pointwise : ∀ word, left word = right word) :
    ∀ (extra : Nat) (word : Word),
      rawBackwardMean extra left word = rawBackwardMean extra right word
  | 0, word => pointwise word
  | extra + 1, word =>
      rawBackwardMean_congr (rawChildMean left) (rawChildMean right)
        (rawChildMean_congr left right pointwise) extra word

/-- The finite backward variance respects pointwise equality without
requiring equality of the function-valued input. -/
theorem rawBackwardVariance_congr (left right : Word → Coordinate)
    (pointwise : ∀ word, left word = right word) :
    ∀ (extra : Nat) (word : Word),
      rawBackwardVariance extra left word =
        rawBackwardVariance extra right word
  | 0, word => rfl
  | extra + 1, word => by
      change
        rawBackwardMean extra (rawChildVariance left) word +
            rawBackwardVariance extra (rawChildMean left) word =
          rawBackwardMean extra (rawChildVariance right) word +
            rawBackwardVariance extra (rawChildMean right) word
      rw [rawBackwardMean_congr _ _
          (rawChildVariance_congr left right pointwise) extra word,
        rawBackwardVariance_congr (rawChildMean left) (rawChildMean right)
          (rawChildMean_congr left right pointwise) extra word]

theorem rawBackwardMean_nonnegative (value : Word → Coordinate)
    (nonnegative : ∀ word, 0 ≤ value word) :
    ∀ (extra : Nat) (word : Word),
      0 ≤ rawBackwardMean extra value word
  | 0, word => nonnegative word
  | extra + 1, word =>
      rawBackwardMean_nonnegative (rawChildMean value)
        (rawChildMean_nonnegative value nonnegative) extra word

theorem rawBackwardVariance_nonnegative (value : Word → Coordinate) :
    ∀ (extra : Nat) (word : Word),
      0 ≤ rawBackwardVariance extra value word
  | 0, _ => le_rfl
  | extra + 1, word =>
      add_nonneg
        (rawBackwardMean_nonnegative (rawChildVariance value)
          (rawChildVariance_nonnegative value) extra word)
        (rawBackwardVariance_nonnegative (rawChildMean value) extra word)

/-- Averaging a payoff already determined by the displayed parent returns
that parent payoff exactly. -/
theorem rawChildMean_parent (value : Word → Coordinate) (word : Word) :
    rawChildMean (fun child => value (rawParent child)) word = value word := by
  unfold rawChildMean
  change (1 / 2 : Coordinate) * value (rawParent (word ++ [false])) +
      (1 / 2 : Coordinate) * value (rawParent (word ++ [true])) = value word
  rw [rawParent_append_bit, rawParent_append_bit]
  have halves : (1 / 2 : Coordinate) + 1 / 2 = 1 := by decide
  calc
    (1 / 2 : Coordinate) * value word + 1 / 2 * value word =
        ((1 / 2 : Coordinate) + 1 / 2) * value word := by ring1
    _ = 1 * value word := by rw [halves]
    _ = value word := by ring1

/-- A payoff already determined by the displayed parent has zero within-
child variance. -/
theorem rawChildVariance_parent (value : Word → Coordinate) (word : Word) :
    rawChildVariance (fun child => value (rawParent child)) word = 0 := by
  unfold rawChildVariance
  rw [rawChildMean_parent (fun item => value item ^ 2),
    rawChildMean_parent value]
  ring1

theorem rawBackwardMean_zero : ∀ (extra : Nat) (word : Word),
    rawBackwardMean extra (fun _ => 0) word = 0
  | 0, word => rfl
  | extra + 1, word => by
      change rawBackwardMean extra
          (rawChildMean (fun _ => 0)) word = 0
      calc
        rawBackwardMean extra (rawChildMean (fun _ => 0)) word =
            rawBackwardMean extra (fun _ => 0) word :=
          rawBackwardMean_congr _ _ (fun candidate => by
            unfold rawChildMean
            ring1) extra word
        _ = 0 := rawBackwardMean_zero extra word

/-- Folding back an observable pulled from the displayed ancestor recovers
the original shallower observable pointwise. -/
theorem rawBackwardMean_ancestor (value : Word → Coordinate) :
    ∀ (extra : Nat) (word : Word),
      rawBackwardMean extra
          (fun descendant => value (rawAncestor extra descendant)) word =
        value word
  | 0, word => rfl
  | extra + 1, word => by
      change rawBackwardMean extra
          (rawChildMean (fun descendant =>
            value (rawAncestor extra (rawParent descendant)))) word =
        value word
      calc
        rawBackwardMean extra
              (rawChildMean (fun descendant =>
                value (rawAncestor extra (rawParent descendant)))) word =
            rawBackwardMean extra
              (fun candidate => value (rawAncestor extra candidate)) word :=
          rawBackwardMean_congr _ _ (fun candidate =>
            rawChildMean_parent
              (fun item => value (rawAncestor extra item)) candidate) extra word
        _ = value word := rawBackwardMean_ancestor value extra word

/-- A payoff pulled from the displayed ancestor loses no variance under
finite truncation: its explicit residual variance is pointwise zero. -/
theorem rawBackwardVariance_ancestor (value : Word → Coordinate) :
    ∀ (extra : Nat) (word : Word),
      rawBackwardVariance extra
          (fun descendant => value (rawAncestor extra descendant)) word = 0
  | 0, word => rfl
  | extra + 1, word => by
      change
        rawBackwardMean extra
            (rawChildVariance (fun descendant =>
              value (rawAncestor extra (rawParent descendant)))) word +
          rawBackwardVariance extra
            (rawChildMean (fun descendant =>
              value (rawAncestor extra (rawParent descendant)))) word = 0
      rw [rawBackwardMean_congr _ _ (fun candidate =>
          rawChildVariance_parent
            (fun item => value (rawAncestor extra item)) candidate) extra word,
        rawBackwardVariance_congr _ _ (fun candidate =>
          rawChildMean_parent
            (fun item => value (rawAncestor extra item)) candidate) extra word,
        rawBackwardMean_zero,
        rawBackwardVariance_ancestor value extra word]
      ring1

/-- Advancing one finite depth is equivalently the displayed replacement of
every current frontier word by its two children. -/
theorem rawExtensions_succ_children (stem : Word) : ∀ depth : Nat,
    rawExtensions stem (depth + 1) =
      (rawExtensions stem depth).flatMap rawChildren
  | 0 => rfl
  | depth + 1 => by
      change
        rawExtensions (stem ++ [false]) (depth + 1) ++
            rawExtensions (stem ++ [true]) (depth + 1) =
          (rawExtensions (stem ++ [false]) depth ++
            rawExtensions (stem ++ [true]) depth).flatMap rawChildren
      rw [rawExtensions_succ_children (stem ++ [false]) depth,
        rawExtensions_succ_children (stem ++ [true]) depth,
        List.flatMap_append]

/-- The frontier contains exactly a finite power-of-two number of words. -/
theorem rawExtensions_length (stem : Word) : ∀ depth : Nat,
    (rawExtensions stem depth).length = 2 ^ depth
  | 0 => rfl
  | depth + 1 => by
      rw [rawExtensions, List.length_append,
        rawExtensions_length (stem ++ [false]) depth,
        rawExtensions_length (stem ++ [true]) depth, pow_succ]
      ring1

/-- Every generated word has precisely the requested additional length. -/
theorem rawExtensions_word_length (stem : Word) :
    ∀ (depth : Nat) (word : Word), word ∈ rawExtensions stem depth →
      word.length = stem.length + depth
  | 0, word, member => by
      simp only [rawExtensions, List.mem_cons, List.not_mem_nil,
        or_false] at member
      subst word
      ring1
  | depth + 1, word, member => by
      simp only [rawExtensions, List.mem_append] at member
      rcases member with left | right
      · rw [rawExtensions_word_length (stem ++ [false]) depth word left,
          List.length_append]
        simp only [List.length_cons, List.length_nil]
        ring1
      · rw [rawExtensions_word_length (stem ++ [true]) depth word right,
          List.length_append]
        simp only [List.length_cons, List.length_nil]
        ring1

/-- Every row at one displayed extension depth carries the same dyadic
symbolic weight: the stem weight times one half-power for the added bits. -/
theorem rawExtensions_member_weight (stem : Word) (depth : Nat)
    (word : Word) (member : word ∈ rawExtensions stem depth) :
    rawPrefixWeight word =
      rawPrefixWeight stem * (1 / 2 : Coordinate) ^ depth := by
  unfold rawPrefixWeight
  rw [rawExtensions_word_length stem depth word member, pow_add]

/-- Every generated word visibly extends the supplied raw prefix. -/
theorem rawExtensions_isPrefix (stem : Word) :
    ∀ (depth : Nat) (word : Word), word ∈ rawExtensions stem depth →
      stem.IsPrefix word
  | 0, word, member => by
      simp only [rawExtensions, List.mem_cons, List.not_mem_nil,
        or_false] at member
      subst word
      exact ⟨[], by simp only [List.append_nil]⟩
  | depth + 1, word, member => by
      simp only [rawExtensions, List.mem_append] at member
      rcases member with left | right
      · rcases rawExtensions_isPrefix (stem ++ [false]) depth word left with
          ⟨suffix, equal⟩
        exact ⟨[false] ++ suffix, by
          simpa only [List.append_assoc] using equal⟩
      · rcases rawExtensions_isPrefix (stem ++ [true]) depth word right with
          ⟨suffix, equal⟩
        exact ⟨[true] ++ suffix, by
          simpa only [List.append_assoc] using equal⟩

/-- Dyadic content is conserved at every displayed finite extension depth. -/
theorem rawExtensions_weight (stem : Word) : ∀ depth : Nat,
    rawFrontierWeight (rawExtensions stem depth) = rawPrefixWeight stem
  | 0 => by
      simp only [rawExtensions, rawFrontierWeight, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | depth + 1 => by
      simp only [rawExtensions, rawFrontierWeight, List.map_append,
        List.sum_append]
      change rawFrontierWeight (rawExtensions (stem ++ [false]) depth) +
          rawFrontierWeight (rawExtensions (stem ++ [true]) depth) =
        rawPrefixWeight stem
      rw [rawExtensions_weight (stem ++ [false]) depth,
        rawExtensions_weight (stem ++ [true]) depth,
        rawPrefixWeight_children_add]

private theorem eventWeight_rawChildren_parent
    (word : Word) (event : Word → Bool) :
    _root_.FiniteMeasure.eventWeight
        ((rawChildren word).map rawPrefixAtom)
        (fun child => event (rawParent child)) =
      match event word with
      | true => rawPrefixWeight word
      | false => 0 := by
  cases selected : event word
  · simp only [rawChildren, List.map_cons, List.map_nil,
      _root_.FiniteMeasure.eventWeight, rawPrefixAtom,
      rawParent_append_bit, selected, zero_add]
  · simp only [rawChildren, List.map_cons, List.map_nil,
      _root_.FiniteMeasure.eventWeight, rawParent_append_bit, selected,
      rawPrefixAtom, add_zero]
    exact rawPrefixWeight_children_add word

private theorem eventWeight_rawChildFrontier_parent
    (event : Word → Bool) : ∀ words : List Word,
    _root_.FiniteMeasure.eventWeight
        ((words.flatMap rawChildren).map rawPrefixAtom)
        (fun child => event (rawParent child)) =
      _root_.FiniteMeasure.eventWeight (words.map rawPrefixAtom) event
  | [] => rfl
  | word :: remaining => by
      rw [List.flatMap_cons, List.map_append,
        _root_.FiniteMeasure.eventWeight_append,
        eventWeight_rawChildren_parent word event,
        eventWeight_rawChildFrontier_parent event remaining]
      rfl

private theorem eventWeight_rawChildren_lastTrue_parent
    (word : Word) (event : Word → Bool) :
    _root_.FiniteMeasure.eventWeight
        ((rawChildren word).map rawPrefixAtom)
        (fun child => rawLastBit child && event (rawParent child)) =
      (1 / 2 : Coordinate) *
        (match event word with
        | true => rawPrefixWeight word
        | false => 0) := by
  cases selected : event word
  · simp only [rawChildren, List.map_cons, List.map_nil,
      _root_.FiniteMeasure.eventWeight, rawPrefixAtom,
      rawLastBit_append_bit, rawParent_append_bit, selected,
      Bool.and_false, zero_add, mul_zero]
  · simp only [rawChildren, List.map_cons, List.map_nil,
      _root_.FiniteMeasure.eventWeight, rawPrefixAtom,
      rawLastBit_append_bit, rawParent_append_bit, selected,
      Bool.false_and, Bool.true_and, add_zero, rawPrefixWeight_child]
    ring1

private theorem eventWeight_rawChildFrontier_lastTrue_parent
    (event : Word → Bool) : ∀ words : List Word,
    _root_.FiniteMeasure.eventWeight
        ((words.flatMap rawChildren).map rawPrefixAtom)
        (fun child => rawLastBit child && event (rawParent child)) =
      (1 / 2 : Coordinate) *
        _root_.FiniteMeasure.eventWeight (words.map rawPrefixAtom) event
  | [] => by
      simp only [List.flatMap_nil, List.map_nil,
        _root_.FiniteMeasure.eventWeight, mul_zero]
  | word :: remaining => by
      rw [List.flatMap_cons, List.map_append,
        _root_.FiniteMeasure.eventWeight_append,
        eventWeight_rawChildren_lastTrue_parent word event,
        eventWeight_rawChildFrontier_lastTrue_parent event remaining]
      simp only [List.map_cons, _root_.FiniteMeasure.eventWeight,
        rawPrefixAtom]
      cases event word <;> simp only [zero_add] <;> ring1

private theorem expectationWeight_rawChildren_parent
    (word : Word) (value : Word → Coordinate) :
    _root_.FiniteMeasure.Distribution.expectationWeight
        ((rawChildren word).map rawPrefixAtom)
        (fun child => value (rawParent child)) =
      rawPrefixWeight word * value word := by
  simp only [rawChildren, List.map_cons, List.map_nil,
    _root_.FiniteMeasure.Distribution.expectationWeight,
    rawParent_append_bit, rawPrefixAtom, add_zero]
  rw [← add_mul, rawPrefixWeight_children_add]

private theorem expectationWeight_rawChildFrontier_parent
    (value : Word → Coordinate) : ∀ words : List Word,
    _root_.FiniteMeasure.Distribution.expectationWeight
        ((words.flatMap rawChildren).map rawPrefixAtom)
        (fun child => value (rawParent child)) =
      _root_.FiniteMeasure.Distribution.expectationWeight
        (words.map rawPrefixAtom) value
  | [] => rfl
  | word :: remaining => by
      rw [List.flatMap_cons, List.map_append,
        _root_.FiniteMeasure.expectationWeight_append,
        expectationWeight_rawChildren_parent word value,
        expectationWeight_rawChildFrontier_parent value remaining]
      rfl

private theorem expectationWeight_rawChildren_value
    (word : Word) (value : Word → Coordinate) :
    _root_.FiniteMeasure.Distribution.expectationWeight
        ((rawChildren word).map rawPrefixAtom) value =
      rawPrefixWeight word * rawChildMean value word := by
  simp only [rawChildren, List.map_cons, List.map_nil,
    _root_.FiniteMeasure.Distribution.expectationWeight,
    rawPrefixAtom, add_zero]
  rw [rawPrefixWeight_child, rawPrefixWeight_child]
  unfold rawChildMean
  ring1

private theorem expectationWeight_rawChildFrontier_value
    (value : Word → Coordinate) : ∀ words : List Word,
    _root_.FiniteMeasure.Distribution.expectationWeight
        ((words.flatMap rawChildren).map rawPrefixAtom) value =
      _root_.FiniteMeasure.Distribution.expectationWeight
        (words.map rawPrefixAtom) (rawChildMean value)
  | [] => rfl
  | word :: remaining => by
      rw [List.flatMap_cons, List.map_append,
        _root_.FiniteMeasure.expectationWeight_append,
        expectationWeight_rawChildren_value word value,
        expectationWeight_rawChildFrontier_value value remaining]
      rfl

/-- The exact finite content carried by a raw-prefix extension frontier. -/
def rawExtensionContent (stem : Word) (depth : Nat) :
    _root_.FiniteMeasure.FiniteContent Word :=
  rawPrefixContent (rawExtensions stem depth)

theorem rawExtensionContent_total (stem : Word) (depth : Nat) :
    (rawExtensionContent stem depth).total = rawPrefixWeight stem := by
    rw [rawExtensionContent, rawPrefixContent_total,
    rawExtensions_weight]

/-- Forgetting the final displayed bit preserves every finite event weight
between two successive raw extension depths. -/
theorem rawExtensionContent_measure_parent
    (stem : Word) (depth : Nat) (event : Word → Bool) :
    (rawExtensionContent stem (depth + 1)).measure
        (fun word => event (rawParent word)) =
      (rawExtensionContent stem depth).measure event := by
  unfold rawExtensionContent rawPrefixContent
  change _root_.FiniteMeasure.eventWeight
      ((rawExtensions stem (depth + 1)).map rawPrefixAtom)
        (fun word => event (rawParent word)) =
    _root_.FiniteMeasure.eventWeight
      ((rawExtensions stem depth).map rawPrefixAtom) event
  rw [rawExtensions_succ_children]
  exact eventWeight_rawChildFrontier_parent event (rawExtensions stem depth)

/-- The analogous finite consistency law for exact rational evaluations. -/
theorem rawExtensionContent_integral_parent
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionContent stem (depth + 1)).integral
        (fun word => value (rawParent word)) =
      (rawExtensionContent stem depth).integral value := by
  unfold rawExtensionContent rawPrefixContent
  change _root_.FiniteMeasure.Distribution.expectationWeight
      ((rawExtensions stem (depth + 1)).map rawPrefixAtom)
        (fun word => value (rawParent word)) =
    _root_.FiniteMeasure.Distribution.expectationWeight
      ((rawExtensions stem depth).map rawPrefixAtom) value
  rw [rawExtensions_succ_children]
  exact expectationWeight_rawChildFrontier_parent value
    (rawExtensions stem depth)

/-- Integrating the explicit two-child average at one frontier is exactly
the same finite calculation as integrating the original observable at the
next frontier. -/
theorem rawExtensionContent_integral_childMean
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionContent stem depth).integral (rawChildMean value) =
      (rawExtensionContent stem (depth + 1)).integral value := by
  unfold rawExtensionContent rawPrefixContent
  change _root_.FiniteMeasure.Distribution.expectationWeight
      ((rawExtensions stem depth).map rawPrefixAtom) (rawChildMean value) =
    _root_.FiniteMeasure.Distribution.expectationWeight
      ((rawExtensions stem (depth + 1)).map rawPrefixAtom) value
  rw [rawExtensions_succ_children]
  exact (expectationWeight_rawChildFrontier_value value
    (rawExtensions stem depth)).symm

/-- Normalize the complete displayed extension frontier below one supplied
raw prefix.  This is a finite conditional distribution at one explicit
depth, not a probability space of infinite continuations. -/
def rawExtensionDistribution (stem : Word) (depth : Nat) :
    _root_.FiniteMeasure.Distribution Word :=
  (rawExtensionContent stem depth).normalize (by
    rw [rawExtensionContent_total]
    exact rawPrefixWeight_pos stem)

theorem rawExtensionDistribution_atoms_length (stem : Word) (depth : Nat) :
    (rawExtensionDistribution stem depth).atoms.length = 2 ^ depth := by
  rw [rawExtensionDistribution,
    _root_.FiniteMeasure.FiniteContent.normalize_atoms_length]
  simp only [rawExtensionContent, rawPrefixContent, List.length_map,
    rawExtensions_length]

/-- Every executable event in the normalized finite extension table is the
corresponding exact extension content divided by the prefix weight. -/
theorem rawExtensionDistribution_probability
    (stem : Word) (depth : Nat) (event : Word → Bool) :
    (rawExtensionDistribution stem depth).probability event =
      (rawExtensionContent stem depth).measure event /
        rawPrefixWeight stem := by
  unfold rawExtensionDistribution
  rw [_root_.FiniteMeasure.FiniteContent.normalize_probability,
    rawExtensionContent_total]

private theorem eventWeight_map_rawPrefixAtom_eq_count_mul
    (words : List Word) (event : Word → Bool) (unit : Coordinate)
    (equalWeight : ∀ word, word ∈ words → rawPrefixWeight word = unit) :
    _root_.FiniteMeasure.eventWeight (words.map rawPrefixAtom) event =
      (rawFrontierEventCount words event : Coordinate) * unit := by
  induction words with
  | nil =>
      simp only [List.map_nil, _root_.FiniteMeasure.eventWeight,
        rawFrontierEventCount, Nat.cast_zero, zero_mul]
  | cons word remaining inductionHypothesis =>
      have headWeight := equalWeight word List.mem_cons_self
      have tailWeight : ∀ candidate, candidate ∈ remaining →
          rawPrefixWeight candidate = unit := by
        intro candidate member
        exact equalWeight candidate (List.mem_cons_of_mem word member)
      have tail := inductionHypothesis tailWeight
      cases selected : event word
      · simp only [List.map_cons, _root_.FiniteMeasure.eventWeight,
          rawPrefixAtom, selected, rawFrontierEventCount, Bool.false_eq_true,
          ↓reduceIte, zero_add] at *
        exact tail
      · simp only [List.map_cons, _root_.FiniteMeasure.eventWeight,
          rawPrefixAtom, selected, rawFrontierEventCount, ↓reduceIte,
          Nat.cast_add, Nat.cast_one]
        rw [headWeight, tail]
        ring1

/-- At every supplied finite depth, the normalized extension law is exactly
uniform: an event's probability is its displayed selected-row count times
the dyadic mass of one depth-`depth` row. -/
theorem rawExtensionDistribution_probability_eq_count_mul
    (stem : Word) (depth : Nat) (event : Word → Bool) :
    (rawExtensionDistribution stem depth).probability event =
      (rawFrontierEventCount (rawExtensions stem depth) event : Coordinate) *
        (1 / 2 : Coordinate) ^ depth := by
  rw [rawExtensionDistribution_probability]
  change _root_.FiniteMeasure.eventWeight
      ((rawExtensions stem depth).map rawPrefixAtom) event /
        rawPrefixWeight stem = _
  rw [eventWeight_map_rawPrefixAtom_eq_count_mul
    (rawExtensions stem depth) event
    (rawPrefixWeight stem * (1 / 2 : Coordinate) ^ depth) (by
      intro word member
      exact rawExtensions_member_weight stem depth word member)]
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (rawPrefixWeight_pos stem).ne'
  calc
    ((rawFrontierEventCount (rawExtensions stem depth) event : Coordinate) *
          (rawPrefixWeight stem * (1 / 2 : Coordinate) ^ depth) /
        rawPrefixWeight stem) * rawPrefixWeight stem =
      (rawFrontierEventCount (rawExtensions stem depth) event : Coordinate) *
        (rawPrefixWeight stem * (1 / 2 : Coordinate) ^ depth) :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (rawPrefixWeight_pos stem).ne'
    _ = ((rawFrontierEventCount
          (rawExtensions stem depth) event : Coordinate) *
        (1 / 2 : Coordinate) ^ depth) * rawPrefixWeight stem := by ring1

/-- Successive normalized finite prefix tables are projectively consistent
for every executable event under the explicit final-bit parent map. -/
theorem rawExtensionDistribution_probability_parent
    (stem : Word) (depth : Nat) (event : Word → Bool) :
    (rawExtensionDistribution stem (depth + 1)).probability
        (fun word => event (rawParent word)) =
      (rawExtensionDistribution stem depth).probability event := by
  rw [rawExtensionDistribution_probability,
    rawExtensionDistribution_probability,
    rawExtensionContent_measure_parent]

/-- The newly displayed final bit is a fair finite choice independent of
every executable event on its displayed parent frontier. -/
theorem rawExtensionDistribution_probability_lastTrue_and_parent
    (stem : Word) (depth : Nat) (event : Word → Bool) :
    (rawExtensionDistribution stem (depth + 1)).probability
        (fun word => rawLastBit word && event (rawParent word)) =
      (1 / 2 : Coordinate) *
        (rawExtensionDistribution stem depth).probability event := by
  rw [rawExtensionDistribution_probability,
    rawExtensionDistribution_probability]
  change (_root_.FiniteMeasure.eventWeight
      ((rawExtensions stem (depth + 1)).map rawPrefixAtom)
        (fun word => rawLastBit word && event (rawParent word))) /
      rawPrefixWeight stem =
    (1 / 2 : Coordinate) *
      (_root_.FiniteMeasure.eventWeight
        ((rawExtensions stem depth).map rawPrefixAtom) event /
          rawPrefixWeight stem)
  rw [rawExtensions_succ_children,
    eventWeight_rawChildFrontier_lastTrue_parent]
  change ((1 / 2 : Coordinate) *
      _root_.FiniteMeasure.eventWeight
        ((rawExtensions stem depth).map rawPrefixAtom) event) *
      (rawPrefixWeight stem)⁻¹ =
    (1 / 2 : Coordinate) *
      (_root_.FiniteMeasure.eventWeight
        ((rawExtensions stem depth).map rawPrefixAtom) event *
          (rawPrefixWeight stem)⁻¹)
  exact RFAP.ConstructiveFraction.mul_assoc _ _ _

/-- In particular, the newest displayed bit has exact probability one half
of being true at every supplied finite depth below every stem. -/
theorem rawExtensionDistribution_probability_lastBit_true
    (stem : Word) (depth : Nat) :
    (rawExtensionDistribution stem (depth + 1)).probability rawLastBit =
      1 / 2 := by
  have factorization :=
    rawExtensionDistribution_probability_lastTrue_and_parent stem depth
      (fun _ => true)
  have eventEqual :
      (rawExtensionDistribution stem (depth + 1)).probability
          (fun word => rawLastBit word &&
            (fun _ : Word => true) (rawParent word)) =
        (rawExtensionDistribution stem (depth + 1)).probability rawLastBit :=
    (rawExtensionDistribution stem (depth + 1)).probability_congr _ _
      (fun word => by simp only [Bool.and_true])
  rw [eventEqual,
    (rawExtensionDistribution stem depth).probability_true,
    mul_one] at factorization
  exact factorization

/-- Projective consistency also holds for every displayed rational
observable, not only Boolean events. -/
theorem rawExtensionDistribution_expectation_parent
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionDistribution stem (depth + 1)).expectation
        (fun word => value (rawParent word)) =
      (rawExtensionDistribution stem depth).expectation value := by
  unfold rawExtensionDistribution
  rw [_root_.FiniteMeasure.FiniteContent.normalize_expectation,
    _root_.FiniteMeasure.FiniteContent.normalize_expectation,
    rawExtensionContent_total, rawExtensionContent_total,
    rawExtensionContent_integral_parent]

/-- One-step finite tower law: average the two displayed child values first,
or enumerate the next frontier directly. -/
theorem rawExtensionDistribution_expectation_childMean
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionDistribution stem depth).expectation (rawChildMean value) =
      (rawExtensionDistribution stem (depth + 1)).expectation value := by
  unfold rawExtensionDistribution
  rw [_root_.FiniteMeasure.FiniteContent.normalize_expectation,
    _root_.FiniteMeasure.FiniteContent.normalize_expectation,
    rawExtensionContent_total, rawExtensionContent_total,
    rawExtensionContent_integral_childMean]

/-- Arbitrary displayed finite-depth tower law.  A deep payoff may be folded
back by an explicitly supplied number of binary averaging steps, and its
shallower expectation is exactly the direct deep-frontier expectation. -/
theorem rawExtensionDistribution_expectation_backward
    (stem : Word) (depth : Nat) (value : Word → Coordinate) : ∀ extra : Nat,
    (rawExtensionDistribution stem depth).expectation
        (rawBackwardMean extra value) =
      (rawExtensionDistribution stem (depth + extra)).expectation value
  | 0 => rfl
  | extra + 1 => by
      change
        (rawExtensionDistribution stem depth).expectation
            (rawBackwardMean extra (rawChildMean value)) =
          (rawExtensionDistribution stem (depth + (extra + 1))).expectation
            value
      rw [rawExtensionDistribution_expectation_backward stem depth
        (rawChildMean value) extra]
      simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
        rawExtensionDistribution_expectation_childMean
          stem (depth + extra) value

/-- One-step finite variance contraction under explicit child averaging. -/
theorem rawExtensionDistribution_variance_childMean
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionDistribution stem depth).variance (rawChildMean value) ≤
      (rawExtensionDistribution stem (depth + 1)).variance value := by
  rw [(rawExtensionDistribution stem depth).variance_eq_secondMoment_sub_sq,
    (rawExtensionDistribution stem
      (depth + 1)).variance_eq_secondMoment_sub_sq]
  have secondMomentBound :
      (rawExtensionDistribution stem depth).expectation
          (fun word => rawChildMean value word ^ 2) ≤
        (rawExtensionDistribution stem (depth + 1)).expectation
          (fun word => value word ^ 2) := by
    calc
      (rawExtensionDistribution stem depth).expectation
            (fun word => rawChildMean value word ^ 2) ≤
          (rawExtensionDistribution stem depth).expectation
            (rawChildMean fun word => value word ^ 2) := by
        apply (rawExtensionDistribution stem depth).expectation_mono
        intro atom member
        exact rawChildMean_sq_le value atom.item
      _ = (rawExtensionDistribution stem (depth + 1)).expectation
            (fun word => value word ^ 2) :=
        rawExtensionDistribution_expectation_childMean stem depth _
  have meanEqual :=
    rawExtensionDistribution_expectation_childMean stem depth value
  rw [meanEqual]
  exact RFAP.ConstructiveFraction.sub_le_sub_right_direct secondMomentBound _

/-- Exact one-step finite law of total variance: next-frontier dispersion is
the current average within-child dispersion plus the dispersion of the two-
child means. -/
theorem rawExtensionDistribution_totalVariance_child
    (stem : Word) (depth : Nat) (value : Word → Coordinate) :
    (rawExtensionDistribution stem (depth + 1)).variance value =
      (rawExtensionDistribution stem depth).expectation
          (rawChildVariance value) +
        (rawExtensionDistribution stem depth).variance
          (rawChildMean value) := by
  rw [(rawExtensionDistribution stem
      (depth + 1)).variance_eq_secondMoment_sub_sq,
    (rawExtensionDistribution stem depth).variance_eq_secondMoment_sub_sq]
  unfold rawChildVariance
  rw [(rawExtensionDistribution stem depth).expectation_sub,
    rawExtensionDistribution_expectation_childMean stem depth
      (fun word => value word ^ 2),
    rawExtensionDistribution_expectation_childMean stem depth value]
  ring1

/-- Folding a payoff backward through any displayed finite number of levels
cannot increase its exact rational variance. -/
theorem rawExtensionDistribution_variance_backward
    (stem : Word) (depth : Nat) (value : Word → Coordinate) : ∀ extra : Nat,
    (rawExtensionDistribution stem depth).variance
        (rawBackwardMean extra value) ≤
      (rawExtensionDistribution stem (depth + extra)).variance value
  | 0 => le_rfl
  | extra + 1 => by
      change
        (rawExtensionDistribution stem depth).variance
            (rawBackwardMean extra (rawChildMean value)) ≤
          (rawExtensionDistribution stem (depth + (extra + 1))).variance
            value
      exact
        (rawExtensionDistribution_variance_backward stem depth
          (rawChildMean value) extra).trans (by
            simpa only [Nat.add_assoc, Nat.add_comm 1 extra] using
              rawExtensionDistribution_variance_childMean
                stem (depth + extra) value)

/-- Exact finite-depth variance decomposition.  Deep dispersion is the
shallower dispersion of the backward payoff plus the explicitly averaged
residual variance discarded by that finite truncation. -/
theorem rawExtensionDistribution_totalVariance_backward
    (stem : Word) (depth : Nat) (value : Word → Coordinate) : ∀ extra : Nat,
    (rawExtensionDistribution stem (depth + extra)).variance value =
      (rawExtensionDistribution stem depth).expectation
          (rawBackwardVariance extra value) +
        (rawExtensionDistribution stem depth).variance
          (rawBackwardMean extra value)
  | 0 => by
      change (rawExtensionDistribution stem depth).variance value =
        (rawExtensionDistribution stem depth).expectation (fun _ => 0) +
          (rawExtensionDistribution stem depth).variance value
      rw [(rawExtensionDistribution stem depth).expectation_constant]
      ring1
  | extra + 1 => by
      change
        (rawExtensionDistribution stem (depth + (extra + 1))).variance value =
          (rawExtensionDistribution stem depth).expectation
              (fun word =>
                rawBackwardMean extra (rawChildVariance value) word +
                  rawBackwardVariance extra (rawChildMean value) word) +
            (rawExtensionDistribution stem depth).variance
              (rawBackwardMean extra (rawChildMean value))
      calc
        (rawExtensionDistribution stem
              (depth + (extra + 1))).variance value =
            (rawExtensionDistribution stem (depth + extra + 1)).variance
              value := by
          congr 2
        _ = (rawExtensionDistribution stem (depth + extra)).expectation
              (rawChildVariance value) +
            (rawExtensionDistribution stem (depth + extra)).variance
              (rawChildMean value) :=
          rawExtensionDistribution_totalVariance_child
            stem (depth + extra) value
        _ = (rawExtensionDistribution stem depth).expectation
              (rawBackwardMean extra (rawChildVariance value)) +
            ((rawExtensionDistribution stem depth).expectation
                (rawBackwardVariance extra (rawChildMean value)) +
              (rawExtensionDistribution stem depth).variance
                (rawBackwardMean extra (rawChildMean value))) := by
          rw [← rawExtensionDistribution_expectation_backward stem depth
              (rawChildVariance value) extra,
            rawExtensionDistribution_totalVariance_backward stem depth
              (rawChildMean value) extra]
        _ = (rawExtensionDistribution stem depth).expectation
              (fun word =>
                rawBackwardMean extra (rawChildVariance value) word +
                  rawBackwardVariance extra (rawChildMean value) word) +
            (rawExtensionDistribution stem depth).variance
              (rawBackwardMean extra (rawChildMean value)) := by
          rw [(rawExtensionDistribution stem depth).expectation_add]
          ring1

/-- Projective consistency across any explicitly supplied finite depth gap
for executable events. -/
theorem rawExtensionDistribution_probability_ancestor
    (stem : Word) (depth : Nat) (event : Word → Bool) : ∀ extra : Nat,
    (rawExtensionDistribution stem (depth + extra)).probability
        (fun word => event (rawAncestor extra word)) =
      (rawExtensionDistribution stem depth).probability event
  | 0 => rfl
  | extra + 1 => by
      change
        (rawExtensionDistribution stem ((depth + extra) + 1)).probability
            (fun word => event (rawAncestor extra (rawParent word))) =
          (rawExtensionDistribution stem depth).probability event
      rw [rawExtensionDistribution_probability_parent stem (depth + extra)
        (fun word => event (rawAncestor extra word))]
      exact rawExtensionDistribution_probability_ancestor stem depth event
        extra

/-- Projective consistency across any displayed finite depth gap for
rational observables. -/
theorem rawExtensionDistribution_expectation_ancestor
    (stem : Word) (depth : Nat) (value : Word → Coordinate) : ∀ extra : Nat,
    (rawExtensionDistribution stem (depth + extra)).expectation
        (fun word => value (rawAncestor extra word)) =
      (rawExtensionDistribution stem depth).expectation value
  | 0 => rfl
  | extra + 1 => by
      change
        (rawExtensionDistribution stem ((depth + extra) + 1)).expectation
            (fun word => value (rawAncestor extra (rawParent word))) =
          (rawExtensionDistribution stem depth).expectation value
      rw [rawExtensionDistribution_expectation_parent stem (depth + extra)
        (fun word => value (rawAncestor extra word))]
      exact rawExtensionDistribution_expectation_ancestor stem depth value
        extra

/-- The pushforward of a deeper finite prefix table by explicit ancestor
truncation agrees in every evaluation with the named shallower table. -/
theorem rawExtensionDistribution_mapAncestor_evaluationEquivalent
    (stem : Word) (depth extra : Nat) :
    _root_.FiniteMeasure.Distribution.EvaluationEquivalent
      ((rawExtensionDistribution stem (depth + extra)).map
        (rawAncestor extra))
      (rawExtensionDistribution stem depth) where
  probability_eq event := by
    rw [_root_.FiniteMeasure.Distribution.map_probability]
    exact rawExtensionDistribution_probability_ancestor
      stem depth event extra
  expectation_eq value := by
    rw [_root_.FiniteMeasure.Distribution.map_expectation]
    exact rawExtensionDistribution_expectation_ancestor
      stem depth value extra

/-- Explicit named-law coupling between two displayed finite prefix depths:
each deep word is paired with its computed finite ancestor. -/
def rawExtensionAncestorLawCoupling
    (stem : Word) (depth extra : Nat) :
    _root_.FiniteMeasure.LawCoupling
      (rawExtensionDistribution stem (depth + extra))
      (rawExtensionDistribution stem depth) := by
  let graphWitness := _root_.FiniteMeasure.LawCoupling.graph
    (rawExtensionDistribution stem (depth + extra)) (rawAncestor extra)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (rawExtensionDistribution_mapAncestor_evaluationEquivalent
          stem depth extra) }

/-- Executable relation recognizing the supplied ancestor pairing. -/
def rawAncestorRelation (extra : Nat) (deep shallow : Word) : Bool :=
  decide (rawAncestor extra deep = shallow)

/-- The explicit finite ancestor coupling has exactly zero mismatch mass. -/
theorem rawExtensionAncestorLawCoupling_mismatchProbability
    (stem : Word) (depth extra : Nat) :
    (rawExtensionAncestorLawCoupling stem depth extra).mismatchProbability
        (rawAncestorRelation extra) = 0 := by
  unfold rawExtensionAncestorLawCoupling
  change
    (_root_.FiniteMeasure.Coupling.graph
      (rawExtensionDistribution stem (depth + extra))
      (rawAncestor extra)).mismatchProbability
        (rawAncestorRelation extra) = 0
  apply _root_.FiniteMeasure.Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  unfold rawAncestorRelation
  simp only [decide_true]

/-- Explicit normalized fair-bit distribution at one displayed finite raw
depth. -/
def fairDepthDistribution (depth : Nat) :
    _root_.FiniteMeasure.Distribution Word where
  atoms := (rawExtensions [] depth).map rawPrefixAtom
  total_one := by
    change (rawExtensionContent [] depth).total = 1
    rw [rawExtensionContent_total, rawPrefixWeight_nil]

theorem fairDepthDistribution_atoms_length (depth : Nat) :
    (fairDepthDistribution depth).atoms.length = 2 ^ depth := by
  simp only [fairDepthDistribution, List.length_map,
    rawExtensions_length]

end CCL.FiniteMeasure
