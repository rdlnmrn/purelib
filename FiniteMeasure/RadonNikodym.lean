import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Density
import FiniteMeasure.Consolidation

/-!
# Finite rational Radon--Nikodym witnesses

For two atom tables presented on the same explicit rows, absolute continuity
is the rowwise condition that a zero source weight forces a zero target
weight.  When row payloads do not repeat, the target/source quotient is an
executable rational density and reconstructs every target integral exactly.

There is no almost-everywhere quotient or existence argument over an
unbounded carrier.  The witness is calculated from the displayed finite
table.
-/

namespace FiniteMeasure

/-- One aligned source/target atomic row. -/
structure AtomicChangeRow (α : Type) where
  item : α
  sourceWeight : Coordinate
  targetWeight : Coordinate
  source_nonnegative : 0 ≤ sourceWeight
  target_nonnegative : 0 ≤ targetWeight
  target_zero_of_source_zero : sourceWeight = 0 → targetWeight = 0

/-- A payload does not occur in a displayed aligned row list. -/
def AtomicRowPayloadAbsent {α : Type} (item : α) :
    List (AtomicChangeRow α) → Prop
  | [] => True
  | row :: remaining =>
      item ≠ row.item ∧ AtomicRowPayloadAbsent item remaining

/-- No payload occurs twice in an aligned atomic table. -/
def NoRepeatedAtomicRows {α : Type} : List (AtomicChangeRow α) → Prop
  | [] => True
  | row :: remaining =>
      AtomicRowPayloadAbsent row.item remaining ∧
        NoRepeatedAtomicRows remaining

/-- An explicitly aligned finite source/target pair. -/
structure AtomicChange (α : Type) where
  rows : List (AtomicChangeRow α)
  noRepeated : NoRepeatedAtomicRows rows

namespace AtomicChange

def sourceAtoms {α : Type} :
    List (AtomicChangeRow α) → List (Weighted α)
  | [] => []
  | row :: remaining =>
      { item := row.item
        weight := row.sourceWeight
        nonnegative := row.source_nonnegative } :: sourceAtoms remaining

def targetAtoms {α : Type} :
    List (AtomicChangeRow α) → List (Weighted α)
  | [] => []
  | row :: remaining =>
      { item := row.item
        weight := row.targetWeight
        nonnegative := row.target_nonnegative } :: targetAtoms remaining

/-- Source finite content displayed by the aligned table. -/
def source {α : Type} (change : AtomicChange α) : FiniteContent α :=
  ⟨sourceAtoms change.rows⟩

/-- Target finite content displayed by the aligned table. -/
def target {α : Type} (change : AtomicChange α) : FiniteContent α :=
  ⟨targetAtoms change.rows⟩

/-- Executable quotient density looked up in the aligned finite table. -/
def densityFromRows {α : Type} [DecidableEq α] :
    List (AtomicChangeRow α) → α → Coordinate
  | [], _ => 0
  | row :: remaining, item =>
      if item = row.item then
        if row.sourceWeight = 0 then 0
        else row.targetWeight / row.sourceWeight
      else densityFromRows remaining item

def density {α : Type} [DecidableEq α]
    (change : AtomicChange α) : α → Coordinate :=
  densityFromRows change.rows

theorem densityFromRows_nonnegative {α : Type} [DecidableEq α] :
    ∀ (rows : List (AtomicChangeRow α)) (item : α),
      0 ≤ densityFromRows rows item
  | [], item => le_rfl
  | row :: remaining, item => by
      by_cases same : item = row.item
      · by_cases zero : row.sourceWeight = 0
        · simp only [densityFromRows, same, ↓reduceIte, zero]
          exact le_rfl
        · simp only [densityFromRows, same, ↓reduceIte, zero]
          exact RFAP.ConstructiveFraction.div_nonneg_direct
            row.target_nonnegative row.source_nonnegative
      · simp only [densityFromRows, same, ↓reduceIte]
        exact densityFromRows_nonnegative remaining item

theorem density_nonnegative {α : Type} [DecidableEq α]
    (change : AtomicChange α) (item : α) :
    0 ≤ change.density item :=
  densityFromRows_nonnegative change.rows item

private theorem source_mul_densityFromRows_head
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α) (remaining : List (AtomicChangeRow α)) :
    row.sourceWeight * densityFromRows (row :: remaining) row.item =
      row.targetWeight := by
  by_cases zero : row.sourceWeight = 0
  · have targetZero := row.target_zero_of_source_zero zero
    simp only [densityFromRows, ↓reduceIte, zero, zero_mul, targetZero]
  · simp only [densityFromRows, ↓reduceIte, zero]
    calc
      row.sourceWeight * (row.targetWeight / row.sourceWeight) =
          (row.targetWeight / row.sourceWeight) * row.sourceWeight := by
        ring1
      _ = row.targetWeight :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          row.targetWeight row.sourceWeight zero

private theorem densityFromRows_cons_of_ne
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α) (remaining : List (AtomicChangeRow α))
    (item : α) (different : item ≠ row.item) :
    densityFromRows (row :: remaining) item =
      densityFromRows remaining item := by
  simp only [densityFromRows, different, ↓reduceIte]

private theorem expectationWeight_density_prepend
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α)
    (lookupRows : List (AtomicChangeRow α)) :
    ∀ (atoms : List (AtomicChangeRow α)),
      AtomicRowPayloadAbsent row.item atoms →
      ∀ value : α → Coordinate,
        Distribution.expectationWeight (sourceAtoms atoms)
            (fun item => densityFromRows (row :: lookupRows) item * value item) =
          Distribution.expectationWeight (sourceAtoms atoms)
            (fun item => densityFromRows lookupRows item * value item)
  | [], absent, value => rfl
  | current :: remaining, absent, value => by
      rcases absent with ⟨headDifferent, tailAbsent⟩
      have currentDifferent : current.item ≠ row.item :=
        fun same => headDifferent same.symm
      simp only [sourceAtoms, Distribution.expectationWeight]
      rw [densityFromRows_cons_of_ne row lookupRows
        current.item currentDifferent]
      rw [expectationWeight_density_prepend row lookupRows remaining
        tailAbsent value]

/-- The quotient density reconstructs every target integral by a direct
finite row calculation. -/
theorem expectationWeight_densityFromRows
    {α : Type} [DecidableEq α] :
    ∀ (rows : List (AtomicChangeRow α)),
      NoRepeatedAtomicRows rows →
      ∀ value : α → Coordinate,
        Distribution.expectationWeight (sourceAtoms rows)
            (fun item => densityFromRows rows item * value item) =
          Distribution.expectationWeight (targetAtoms rows) value
  | [], noRepeated, value => rfl
  | row :: remaining, noRepeated, value => by
      rcases noRepeated with ⟨headAbsent, tailNoRepeated⟩
      simp only [sourceAtoms, targetAtoms,
        Distribution.expectationWeight]
      have headDensity := source_mul_densityFromRows_head row remaining
      have tailDensity := expectationWeight_density_prepend row remaining
        remaining headAbsent value
      have tailIntegral := expectationWeight_densityFromRows remaining
        tailNoRepeated value
      calc
        row.sourceWeight *
              (densityFromRows (row :: remaining) row.item * value row.item) +
            Distribution.expectationWeight (sourceAtoms remaining)
              (fun item =>
                densityFromRows (row :: remaining) item * value item) =
            (row.sourceWeight *
                densityFromRows (row :: remaining) row.item) *
                value row.item +
              Distribution.expectationWeight (sourceAtoms remaining)
                (fun item =>
                  densityFromRows (row :: remaining) item * value item) := by
          ring1
        _ = row.targetWeight * value row.item +
              Distribution.expectationWeight (sourceAtoms remaining)
                (fun item =>
                  densityFromRows (row :: remaining) item * value item) := by
          rw [headDensity]
        _ = row.targetWeight * value row.item +
              Distribution.expectationWeight (sourceAtoms remaining)
                (fun item => densityFromRows remaining item * value item) := by
          rw [tailDensity]
        _ = row.targetWeight * value row.item +
              Distribution.expectationWeight (targetAtoms remaining) value := by
          rw [tailIntegral]

/-- A finite Radon--Nikodym witness is an explicit nonnegative rational
density reconstructing all target integrals from the source content. -/
structure Witness {α : Type} (source target : FiniteContent α) where
  density : α → Coordinate
  nonnegative : ∀ item, 0 ≤ density item
  integral_eq : ∀ value : α → Coordinate,
    target.integral value =
      source.integral (fun item => density item * value item)

/-- Construct the Radon--Nikodym witness from the displayed aligned rows. -/
def witness {α : Type} [DecidableEq α]
    (change : AtomicChange α) : Witness change.source change.target where
  density := change.density
  nonnegative := change.density_nonnegative
  integral_eq value :=
    (expectationWeight_densityFromRows change.rows change.noRepeated value).symm

theorem Witness.measure_eq {α : Type}
    {source target : FiniteContent α}
    (witness : Witness source target) (event : α → Bool) :
    target.measure event =
      source.integral (fun item =>
        witness.density item * Distribution.indicator event item) := by
  rw [← target.integral_indicator event]
  exact witness.integral_eq (Distribution.indicator event)

theorem Witness.total_eq {α : Type}
    {source target : FiniteContent α}
    (witness : Witness source target) :
    target.total = source.integral witness.density := by
  calc
    target.total = target.integral (fun _ => 1) := by
      rw [target.integral_constant, mul_one]
    _ = source.integral (fun item => witness.density item * 1) :=
      witness.integral_eq (fun _ => 1)
    _ = source.integral witness.density :=
      source.integral_congr _ _ (fun item => by ring1)

private theorem integral_density_indicator_atomEvent
    {α : Type} [DecidableEq α] (content : FiniteContent α)
    (density : α → Coordinate) (item : α) :
    content.integral (fun candidate =>
        density candidate * Distribution.indicator (atomEvent item) candidate) =
      content.measure (atomEvent item) * density item := by
  calc
    content.integral (fun candidate =>
          density candidate *
            Distribution.indicator (atomEvent item) candidate) =
        content.integral (fun candidate =>
          density item *
            Distribution.indicator (atomEvent item) candidate) :=
      content.integral_congr _ _ (fun candidate => by
        cases selected : atomEvent item candidate
        · simp only [Distribution.indicator, selected, mul_zero]
        · have same : candidate = item := by
            unfold atomEvent at selected
            exact of_decide_eq_true selected
          rw [same])
    _ = content.measure (atomEvent item) * density item := by
      rw [content.integral_scale, content.integral_indicator]
      ring1

/-- Finite Radon--Nikodym uniqueness: two reconstructing densities agree at
every payload carrying positive source mass. -/
theorem Witness.density_eq_of_positive_atom
    {α : Type} [DecidableEq α]
    {source target : FiniteContent α}
    (first second : Witness source target) (item : α)
    (positive : 0 < source.measure (atomEvent item)) :
    first.density item = second.density item := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne positive.ne'
  calc
    first.density item * source.measure (atomEvent item) =
        source.measure (atomEvent item) * first.density item := by
      ring1
    _ = source.integral (fun candidate =>
          first.density candidate *
            Distribution.indicator (atomEvent item) candidate) :=
      (integral_density_indicator_atomEvent source first.density item).symm
    _ = target.integral (Distribution.indicator (atomEvent item)) :=
      (first.integral_eq (Distribution.indicator (atomEvent item))).symm
    _ = source.integral (fun candidate =>
          second.density candidate *
            Distribution.indicator (atomEvent item) candidate) :=
      second.integral_eq (Distribution.indicator (atomEvent item))
    _ = source.measure (atomEvent item) * second.density item :=
      integral_density_indicator_atomEvent source second.density item
    _ = second.density item * source.measure (atomEvent item) := by
      ring1

/-- Reweighting by the constructed density reproduces every target integral. -/
theorem reweight_integral_eq_target {α : Type} [DecidableEq α]
    (change : AtomicChange α) (value : α → Coordinate) :
    (change.source.reweight change.density change.density_nonnegative).integral
        value = change.target.integral value := by
  rw [change.source.reweight_integral]
  exact expectationWeight_densityFromRows change.rows change.noRepeated value

/-- Reweighting by the constructed density reproduces every target event
measure. -/
theorem reweight_measure_eq_target {α : Type} [DecidableEq α]
    (change : AtomicChange α) (event : α → Bool) :
    (change.source.reweight change.density change.density_nonnegative).measure
        event = change.target.measure event := by
  rw [← (change.source.reweight change.density
    change.density_nonnegative).integral_indicator event]
  rw [change.reweight_integral_eq_target]
  exact change.target.integral_indicator event

/-- The aligned row hypothesis also yields finite absolute continuity: every
zero-source event has zero target content. -/
theorem target_measure_eq_zero_of_source_measure_eq_zero
    {α : Type} [DecidableEq α] (change : AtomicChange α)
    (event : α → Bool) (zero : change.source.measure event = 0) :
    change.target.measure event = 0 := by
  rw [← change.reweight_measure_eq_target event]
  exact change.source.reweight_measure_zero change.density
    change.density_nonnegative event zero

end AtomicChange

end FiniteMeasure
