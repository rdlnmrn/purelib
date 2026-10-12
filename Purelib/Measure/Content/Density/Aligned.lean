module
meta import Purelib.Elab.ConstructiveInjectivity
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Density.Basic
public import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Content.Integral
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

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

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain one payload with its nonnegative source and target weights and transfer of zero source weight.

The zero-transfer witness permits the density ratio to return zero at a zero source weight while preserving the
target-weight reconstruction identity. -/
structure AtomicChangeRow (α : Type) where
  /-- The exact payload shared by this source-target row. -/ item : α
  /-- The retained source mass at this payload. -/ sourceWeight : Fraction.Rational
  /-- The retained target mass at this payload. -/ targetWeight : Fraction.Rational
  /-- The retained source weight is nonnegative. -/ source_nonnegative : 0 ≤ sourceWeight
  /-- The retained target weight is nonnegative. -/ target_nonnegative : 0 ≤ targetWeight
  /-- A zero retained source weight forces this same row's target weight to vanish. -/ target_zero_of_source_zero :
    sourceWeight = 0 → targetWeight = 0

constructive_injectivity AtomicChangeRow

/-- Require the supplied payload to differ from every exact aligned row payload. -/
def AtomicRowPayloadAbsent {α : Type} (item : α) :
    List (AtomicChangeRow α) → Prop
  | [] => True
  | row :: remaining =>
      item ≠ row.item ∧ AtomicRowPayloadAbsent item remaining

/-- Require pairwise distinct payloads in the retained aligned row list. -/
def NoRepeatedAtomicRows {α : Type} : List (AtomicChangeRow α) → Prop
  | [] => True
  | row :: remaining =>
      AtomicRowPayloadAbsent row.item remaining ∧
        NoRepeatedAtomicRows remaining

set_option genInjectivity false in
/-- Retain a finite aligned source-target row list with no repeated payloads.

Each row owns both nonnegative weights and their zero-transfer certificate. Both content owners and the density lookup
are read from this same ordered list. -/
structure AtomicChange (α : Type) where
  /-- The exact ordered list of aligned source-target rows. -/ rows : List (AtomicChangeRow α)
  /-- No payload repeats in the retained aligned row list. -/ noRepeated : NoRepeatedAtomicRows rows

constructive_injectivity AtomicChange

namespace AtomicChange

/-- Read the original row payloads and source weights as weighted atoms in retained row order. -/
def sourceAtoms {α : Type} :
    List (AtomicChangeRow α) → List (Weighted α)
  | [] => []
  | row :: remaining =>
      { item := row.item
        weight := row.sourceWeight
        nonnegative := row.source_nonnegative } :: sourceAtoms remaining

/-- Read the original row payloads and target weights as weighted atoms in retained row order. -/
def targetAtoms {α : Type} :
    List (AtomicChangeRow α) → List (Weighted α)
  | [] => []
  | row :: remaining =>
      { item := row.item
        weight := row.targetWeight
        nonnegative := row.target_nonnegative } :: targetAtoms remaining

/-- Form the source content from the exact aligned source-atom readback. -/
def source {α : Type} (change : AtomicChange α) : Content α :=
  ⟨sourceAtoms change.rows⟩

/-- Form the target content from the exact aligned target-atom readback. -/
def target {α : Type} (change : AtomicChange α) : Content α :=
  ⟨targetAtoms change.rows⟩

section
open Purelib.Data.Rat
/-- Look up the first matching aligned row and return its target-to-source weight ratio.

Return zero when no row matches or when the matching source weight is zero. The recursive lookup retains the original
row order. -/
def densityFromRows {α : Type} [DecidableEq α] :
    List (AtomicChangeRow α) → α → Fraction.Rational
  | [], _ => 0
  | row :: remaining, item =>
      if item = row.item then
        if row.sourceWeight = 0 then 0
        else row.targetWeight / row.sourceWeight
      else densityFromRows remaining item

/-- Read the density ratio from this exact aligned change's retained rows. -/
def density {α : Type} [DecidableEq α]
    (change : AtomicChange α) : α → Fraction.Rational :=
  densityFromRows change.rows

/-- Each selected aligned-row ratio is invariant under the supplied equality procedure. -/
theorem densityFromRows_eq_of_decidableEq {α : Type}
    (first second : DecidableEq α) (rows : List (AtomicChangeRow α)) (item : α) :
    @densityFromRows α first rows item = @densityFromRows α second rows item := by
  induction rows with
  | nil => rfl
  | cons row remaining ih =>
      change (@ite Fraction.Rational (item = row.item) (first item row.item)
        (if row.sourceWeight = 0 then 0 else row.targetWeight / row.sourceWeight)
        (@densityFromRows α first remaining item)) =
        (@ite Fraction.Rational (item = row.item) (second item row.item)
          (if row.sourceWeight = 0 then 0 else row.targetWeight / row.sourceWeight)
          (@densityFromRows α second remaining item))
      cases first item row.item with
      | isTrue same =>
          rewrite [if_pos same, if_pos same]
          rfl
      | isFalse different =>
          rewrite [if_neg different, if_neg different]
          exact ih

end

/-- Equal retained rows and selected items give the same ratio under either equality procedure. -/
private theorem densityFromRows_agreement {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (rows rows' : List (AtomicChangeRow α))
    (rows_equal : rows = rows') (item item' : α) (items_equal : item = item') :
    @densityFromRows α first rows item = @densityFromRows α second rows' item' := by
  cases rows_equal
  cases items_equal
  exact densityFromRows_eq_of_decidableEq first second rows item

open Lean Elab Command in
run_elab do
  let name := Name.str ``densityFromRows "congr_simp"
  let kinds : Array Meta.CongrArgKind := #[.fixed, .subsingletonInst, .eq, .eq]
  let .thmInfo info ← getConstInfo ``densityFromRows_agreement
    | throwError "pointwise certificate is not a safe theorem"
  let operationInfo ← getConstInfo ``densityFromRows
  let .forallE alpha _ operationType _ := operationInfo.type
    | throwError "equality procedure owner has no type binder"
  let .forallE procedure _ operationType _ := operationType
    | throwError "equality procedure owner has no procedure binder"
  let .forallE left _ operationType _ := operationType
    | throwError "equality procedure owner has no first input"
  let .forallE right _ _ _ := operationType
    | throwError "equality procedure owner has no second input"
  let names := #[alpha, procedure, procedure, left, left,
    left.appendBefore "e_", right, right,
    right.appendBefore "e_"]
  let rec retainNames (type : Expr) (index : Nat) : Expr :=
    match type with
    | .forallE original domain body mode =>
        .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
    | other => other
  setEnv (← (← getEnv).enableRealizationsForConst (← getOptions) ``densityFromRows_agreement)
  Meta.realizeConst ``densityFromRows_agreement name do
    addDecl (.thmDecl {
      name, type := retainNames info.type 0, levelParams := info.levelParams
      value := info.value
    }) (forceExpose := true)
    modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
  let some congrThm ← Meta.mkCongrSimpForConst? ``densityFromRows []
    | throwError "registered original congruence lookup failed"
  unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
    throwError "automatic lookup changed the original public certificate"

open Purelib.Data.Rat in
/-- Every ratio returned by the aligned-row density lookup is nonnegative. -/
theorem densityFromRows_nonnegative {α : Type} [DecidableEq α] :
    ∀ (rows : List (AtomicChangeRow α)) (item : α),
      0 ≤ densityFromRows rows item
  | [], item => Fraction.Order.Basic.le_refl 0
  | row :: remaining, item => by
      simp only [densityFromRows, -eq_self, -iff_self]
      by_cases same : item = row.item
      · rewrite [if_pos same]
        by_cases zero : row.sourceWeight = 0
        · rewrite [if_pos zero]
          exact Fraction.Order.Basic.le_refl 0
        · rewrite [if_neg zero]
          exact Fraction.Order.Field.div_nonneg_direct
            row.target_nonnegative row.source_nonnegative
      · rewrite [if_neg same]
        exact densityFromRows_nonnegative remaining item

/-- The density of an aligned change is nonnegative at every payload. -/
theorem density_nonnegative {α : Type} [DecidableEq α]
    (change : AtomicChange α) (item : α) :
    0 ≤ change.density item :=
  densityFromRows_nonnegative change.rows item

open Purelib.Data.Rat in
/-- Multiplying the head's source weight by its exact density lookup reconstructs its target weight. -/
private theorem source_mul_densityFromRows_head
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α) (remaining : List (AtomicChangeRow α)) :
    row.sourceWeight * densityFromRows (row :: remaining) row.item =
      row.targetWeight := by
  simp only [densityFromRows, -eq_self, -iff_self]
  rewrite [if_pos rfl]
  by_cases zero : row.sourceWeight = 0
  · rewrite [if_pos zero, zero, Fraction.Field.zero_mul_direct]
    exact (row.target_zero_of_source_zero zero).symm
  · rewrite [if_neg zero]
    exact (Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne
        row.targetWeight row.sourceWeight zero)

/-- Prepending a row with a different payload leaves the original payload's density lookup unchanged. -/
private theorem densityFromRows_cons_of_ne
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α) (remaining : List (AtomicChangeRow α))
    (item : α) (different : item ≠ row.item) :
    densityFromRows (row :: remaining) item =
      densityFromRows remaining item := by
  simp only [densityFromRows, -eq_self, -iff_self]
  rewrite [if_neg different]
  rfl

section
open Purelib.Data.Rat
/-- Prepending a lookup row absent from all retained atom payloads leaves their density-weighted integral unchanged. -/
private theorem expectationWeight_density_prepend
    {α : Type} [DecidableEq α]
    (row : AtomicChangeRow α)
    (lookupRows : List (AtomicChangeRow α)) :
    ∀ (atoms : List (AtomicChangeRow α)),
      AtomicRowPayloadAbsent row.item atoms →
      ∀ value : α → Fraction.Rational,
        Distribution.expectationWeight (sourceAtoms atoms)
            (fun item => densityFromRows (row :: lookupRows) item * value item) =
          Distribution.expectationWeight (sourceAtoms atoms)
            (fun item => densityFromRows lookupRows item * value item)
  | [], absent, value => rfl
  | current :: remaining, absent, value => by
      rcases absent with ⟨headDifferent, tailAbsent⟩
      have currentDifferent : current.item ≠ row.item :=
        fun same => headDifferent same.symm
      simp only [sourceAtoms, Distribution.expectationWeight, -eq_self, -iff_self]
      rw [densityFromRows_cons_of_ne row lookupRows
        current.item currentDifferent]
      rw [expectationWeight_density_prepend row lookupRows remaining
        tailAbsent value]

/-- For distinct aligned payloads, source integration against the row density equals exact target integration.

The proof reconstructs the current target weight and preserves the original tail lookup on all remaining payloads. -/
theorem expectationWeight_densityFromRows
    {α : Type} [DecidableEq α] :
    ∀ (rows : List (AtomicChangeRow α)),
      NoRepeatedAtomicRows rows →
      ∀ value : α → Fraction.Rational,
        Distribution.expectationWeight (sourceAtoms rows)
            (fun item => densityFromRows rows item * value item) =
          Distribution.expectationWeight (targetAtoms rows) value
  | [], noRepeated, value => rfl
  | row :: remaining, noRepeated, value => by
      rcases noRepeated with ⟨headAbsent, tailNoRepeated⟩
      simp only [sourceAtoms, targetAtoms,
        Distribution.expectationWeight, -eq_self, -iff_self]
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
          exact congrArg (fun head => head +
            Distribution.expectationWeight (sourceAtoms remaining)
              (fun item => densityFromRows (row :: remaining) item * value item))
            (Fraction.Field.mul_assoc _ _ _).symm
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

end

/-- Certify the exact aligned source and target contents using their retained row density.

Nonnegativity and equality of every weighted integral are attached to the same density lookup and original content
readbacks. -/
def witness {α : Type} [DecidableEq α]
    (change : AtomicChange α) : Witness change.source change.target where
  density := change.density
  nonnegative := change.density_nonnegative
  integral_eq value :=
    (expectationWeight_densityFromRows change.rows change.noRepeated value).symm

open Purelib.Data.Rat in
/-- Integrating after density reweighting of the exact aligned source equals integration in its exact target. -/
theorem reweight_integral_eq_target {α : Type} [DecidableEq α]
    (change : AtomicChange α) (value : α → Fraction.Rational) :
    (change.source.reweight change.density change.density_nonnegative).integral
        value = change.target.integral value := by
  rw [change.source.reweight_integral]
  exact expectationWeight_densityFromRows change.rows change.noRepeated value

/-- Measuring an event after aligned density reweighting equals its exact target measurement. -/
theorem reweight_measure_eq_target {α : Type} [DecidableEq α]
    (change : AtomicChange α) (event : α → Bool) :
    (change.source.reweight change.density change.density_nonnegative).measure
        event = change.target.measure event := by
  rw [← (change.source.reweight change.density
    change.density_nonnegative).integral_indicator event]
  rw [change.reweight_integral_eq_target]
  exact change.target.integral_indicator event

/-- An aligned change transfers every null event from its exact source content to its exact target. -/
theorem target_measure_eq_zero_of_source_measure_eq_zero
    {α : Type} [DecidableEq α] (change : AtomicChange α)
    (event : α → Bool) (zero : change.source.measure event = 0) :
    change.target.measure event = 0 := by
  rw [← change.reweight_measure_eq_target event]
  exact change.source.reweight_measure_zero change.density
    change.density_nonnegative event zero

end AtomicChange

end Purelib.Measure

end
