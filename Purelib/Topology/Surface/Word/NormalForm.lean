module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Shear.Integral.Lift

import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Topology.Surface.Word.Surgery
public import Purelib.Topology.Surface.Word.Selection
public import Purelib.LinearAlgebra.Alternating.Reduction.Lift
import Purelib.LinearAlgebra.Alternating.UnitPivot
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Automatic integral normal form of a balanced signed word

Each selected handle removes four actual occurrences. The remaining word
therefore supplies a terminating recursive construction. Previously removed
handles are retained as orthogonal blocks, not silently discarded.
-/

namespace Purelib.Topology.Surface.Word.NormalForm

open Purelib

open Purelib.LinearAlgebra.Alternating.Reduction.Basic

open Purelib.LinearAlgebra.Alternating.Reduction.Lift

open Purelib.LinearAlgebra.Matrix.Shear.Integral

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.Pairing

open Purelib.Topology.Surface.Word.SignedWord

open Purelib.Topology.Surface.Word.Surgery

open Purelib.Topology.Surface.Word.SignedWord (SignedGenerator)
open Purelib.Topology.Surface.Word.Surgery (InterlacedWord IntegralWordSignature)
open Purelib.Topology.Surface.Word.Selection (WordRotation WordSelection InterlacedAt selectWord)

open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)

variable {count : Nat}

/-- Rotating a signed word preserves its occurrence count. -/
theorem WordRotation.length {source target : List (SignedWord.SignedGenerator count)} (rotation : Selection.WordRotation
  source target) :
    target.length = source.length := by
  rcases rotation with ⟨first, last, source_eq, target_eq⟩
  rw [source_eq, target_eq, Data.List.Append.length_append, Data.List.Append.length_append]
  omega

namespace InterlacedWord

/-- Handle removal cannot increase any signed letter's occurrence count. -/
theorem after_occurrences_le (cut : Surgery.InterlacedWord count) (needle : SignedWord.SignedGenerator count) :
    needle.occurrences cut.after ≤ needle.occurrences cut.before := by
  rw [cut.occurrences_after, cut.occurrences_before]
  omega

/-- Unique signed occurrences leave both handle generators absent after surgery. -/
theorem after_pivot_absent (cut : Surgery.InterlacedWord count)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (index : Fin count) (pivot : index = cut.first ∨ index = cut.last) (reversed : Bool) :
    SignedGenerator.occurrences ⟨index, reversed⟩ cut.after = 0 := by
  have bounded := unique index reversed
  rw [cut.occurrences_before] at bounded
  rw [cut.occurrences_after]
  dsimp only at bounded
  rcases pivot with first | last
  · rw [if_pos first] at bounded; omega
  · rw [if_pos last] at bounded; omega

/-- Both orientations of each selected handle generator occur before surgery. -/
theorem pivot_present (cut : Surgery.InterlacedWord count) (index : Fin count)
    (pivot : index = cut.first ∨ index = cut.last) (reversed : Bool) :
    0 < SignedGenerator.occurrences ⟨index, reversed⟩ cut.before := by
  rw [cut.occurrences_before]
  dsimp only
  rcases pivot with first | last
  · rw [if_pos first]; omega
  · rw [if_pos last]; omega

/-- Recover the shorter word's signature from the already computed matrix step. The canonical word calculation occurs
only in the proof specification; executable code subtracts the single handle from the cached reduced matrix. -/
@[expose] def afterIntegral (cut : Surgery.InterlacedWord count) (source : Surgery.IntegralWordSignature cut.before)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ cut.before ≤ 1)
    (closed : ∀ index, Pairing.totalAt (cut.before.map SignedGenerator.coefficients) index = 0)
    (reduced : LinearAlgebra.Matrix.IntegralMatrix count)
    (reduced_eq : ∀ row column, reduced row column = (cut.unitPivot source unique).reduced row column) :
    Surgery.IntegralWordSignature cut.after :=
  let matrix := LinearAlgebra.Matrix.matrixOfFn fun row column => reduced row column -
    Handle.Basic.handleEntry [(cut.first, cut.last)] row column
  have spec (row column : Fin count) : 2 * matrix row column =
      Pairing.pairingAt (cut.after.map SignedGenerator.coefficients) row column := by
    let canonical := IntegralWordSignature.build (Signature.build (cut.after.map SignedGenerator.coefficients))
      (fun index => (cut.after_total index).trans (closed index))
    have surgery := cut.reduced_eq_handle_add source canonical unique closed row column
    rw [← reduced_eq] at surgery
    have target := canonical.spec row column
    rw [LinearAlgebra.Matrix.matrixOfFn_apply]
    omega
  { signature :=
      { total := source.signature.total
        total_eq := fun index => (source.signature.total_eq index).trans (cut.after_total index).symm
        matrix := LinearAlgebra.Matrix.matrixOfFn fun row column => 2 * matrix row column
        matrix_eq := fun row column => (LinearAlgebra.Matrix.matrixOfFn_apply _ row
          column).trans (spec row column) }
    matrix := matrix
    twice := fun row column => (LinearAlgebra.Matrix.matrixOfFn_apply (fun i j => 2 * matrix i
      j) row column).symm }

end InterlacedWord

/-- A single handle block is zero in rows and columns outside its two pivot indices. -/
theorem single_handle_clear (first last row column : Fin count)
    (rowFirst : row ≠ first) (rowLast : row ≠ last)
    (columnFirst : column ≠ first) (columnLast : column ≠ last) :
    Lift.ClearAt (LinearAlgebra.Matrix.matrixOfFn (Handle.Basic.handleEntry [(first, last)]))
      row column := by
  have rowZero (index : Fin count) (notFirst : index ≠ first) (notLast : index ≠ last) (other : Fin count) :
      LinearAlgebra.Matrix.matrixOfFn (Handle.Basic.handleEntry [(first, last)]) index other =
        0 := by
    rw [LinearAlgebra.Matrix.matrixOfFn_apply]
    change (if index = first ∧ other = last then (1 : Int) else 0) -
      (if index = last ∧ other = first then (1 : Int) else 0) + 0 = 0
    rw [if_neg (fun equal => notFirst equal.1), if_neg (fun equal => notLast equal.1)]
    rfl
  have columnZero (index : Fin count) (notFirst : index ≠ first) (notLast : index ≠ last) (other : Fin count) :
      LinearAlgebra.Matrix.matrixOfFn (Handle.Basic.handleEntry [(first, last)]) other index =
        0 := by
    rw [LinearAlgebra.Matrix.matrixOfFn_apply]
    change (if other = first ∧ index = last then (1 : Int) else 0) -
      (if other = last ∧ index = first then (1 : Int) else 0) + 0 = 0
    rw [if_neg (fun equal => notLast equal.2), if_neg (fun equal => notFirst equal.2)]
    rfl
  exact ⟨rowZero row rowFirst rowLast, rowZero column columnFirst columnLast,
    columnZero row rowFirst rowLast, columnZero column columnFirst columnLast⟩

set_option genInjectivity false in
/-- Retained literal surgery data, with every stage's actual preconditions and the terminal residual's zero certificate.
-/
inductive WordSurgeryTrace : (word : List (SignedWord.SignedGenerator count)) →
    Surgery.IntegralWordSignature word → List (Handle.Basic.PivotIndices count) → Type where
  /-- Finish at the actual residual word with its integral matrix and pointwise zero certificate. -/ | zero {word}
    (integral : Surgery.IntegralWordSignature word) (entries : ∀ row column, integral.matrix row column = 0) :
      Purelib.Topology.Surface.Word.NormalForm.WordSurgeryTrace word integral []
  /-- Retain one interlaced handle, its original occurrence and balance conditions, and the shorter trace. -/ | handle
    {word integral remaining} (selected : Selection.InterlacedAt word)
      (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
      (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
      (target : Surgery.IntegralWordSignature selected.cut.after)
      (tail : Purelib.Topology.Surface.Word.NormalForm.WordSurgeryTrace selected.cut.after target remaining) :
      Purelib.Topology.Surface.Word.NormalForm.WordSurgeryTrace word integral ((selected.cut.first, selected.cut.last)
        :: remaining)

constructive_injectivity WordSurgeryTrace

namespace WordSurgeryTrace

/-- Read the actual residual word at the end of the retained surgery trace. -/
@[expose] def terminalWord : {word : List (SignedWord.SignedGenerator count)} → {integral :
  Surgery.IntegralWordSignature word} →
    {pivots : List (Handle.Basic.PivotIndices count)} → NormalForm.WordSurgeryTrace word integral pivots → List
      (SignedWord.SignedGenerator count)
  | word, _, _, .zero .. => word
  | _, _, _, .handle _ _ _ _ tail => tail.terminalWord

/-- Read the original integral signature retained for the terminal residual word. -/
@[expose] def terminalIntegral : {word : List (SignedWord.SignedGenerator count)} → {integral :
  Surgery.IntegralWordSignature word} →
    {pivots : List (Handle.Basic.PivotIndices count)} → (trace : NormalForm.WordSurgeryTrace word integral pivots) →
    Surgery.IntegralWordSignature trace.terminalWord
  | _, _, _, .zero integral _ => integral
  | _, _, _, .handle _ _ _ _ tail => tail.terminalIntegral

/-- Every entry of the retained terminal integral matrix is zero. -/
theorem terminal_zero {word : List (SignedWord.SignedGenerator count)} {integral : Surgery.IntegralWordSignature word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots) (row
      column : Fin count) :
    trace.terminalIntegral.matrix row column = 0 := by
  induction trace with
  | zero _ entries => exact entries row column
  | handle _ _ _ _ _ ih => exact ih

/-- Four occurrences per handle are accounted for exactly; the remaining zero-pairing word is retained and may be
nonempty. -/
theorem length_accounting {word : List (SignedWord.SignedGenerator count)} {integral : Surgery.IntegralWordSignature
  word}
    {pivots : List (Handle.Basic.PivotIndices count)} (trace : NormalForm.WordSurgeryTrace word integral pivots) :
    trace.terminalWord.length + 4 * pivots.length = word.length := by
  induction trace with
  | zero =>
      simp only [WordSurgeryTrace.terminalWord, List.length_nil, Nat.mul_zero, Nat.add_zero, -eq_self, -iff_self]
      rfl
  | handle selected _ _ _ tail ih =>
      change tail.terminalWord.length + 4 * (_ + 1) = _
      have shortened := selected.cut.after_length
      have rotated := NormalForm.WordRotation.length selected.rotation
      omega

end WordSurgeryTrace

set_option genInjectivity false in
/-- A full integral congruence normal form and its geometric word trace. -/
structure WordNormalForm (word : List (SignedWord.SignedGenerator count)) (integral : Surgery.IntegralWordSignature
  word) where
  /-- Ordered pivot pairs selected by the literal word surgery. -/ pivots : List (Handle.Basic.PivotIndices count)
  /-- Exact integral normal form of the original word matrix at these pivots. -/ normal :
    LinearAlgebra.Alternating.NormalForm
    integral.matrix pivots
  /-- Every retained handle index occurs positively in the original word. -/ used : ∀ index ∈ Handle.Basic.handleIndices
    pivots, 0 < SignedGenerator.occurrences ⟨index, false⟩ word
  /-- Literal surgery trace on the original word and integral signature. -/ trace : NormalForm.WordSurgeryTrace word
    integral pivots

constructive_injectivity WordNormalForm

/-- An extra integral matrix vanishes on all rows and columns used positively by a signed word. -/
structure ClearOnWord (extra : LinearAlgebra.Matrix.IntegralMatrix count) (word : List
  (SignedWord.SignedGenerator count)) : Prop where
  /-- Every positively used word index selects a zero row in the extra matrix. -/ row : ∀ index, 0 <
    SignedGenerator.occurrences ⟨index, false⟩ word → ∀ other, extra index other = 0
  /-- Every positively used word index selects a zero column in the extra matrix. -/ column : ∀ index, 0 <
    SignedGenerator.occurrences ⟨index, false⟩ word → ∀ other, extra other index = 0

set_option genInjectivity false in
/-- A retained reduction of an augmented word matrix with an unchanged extra summand.

The result keeps disjoint used pivots, their literal surgery trace and the exact output split into the extra matrix and
handle blocks. -/
structure WordTailForm (word : List (SignedWord.SignedGenerator count)) (integral : Surgery.IntegralWordSignature word)
    (extra augmented : LinearAlgebra.Matrix.IntegralMatrix count) where
  /-- Ordered pivots retained from the current word's reduction. -/ pivots : List (Handle.Basic.PivotIndices count)
  /-- Actual integral reduction of the augmented matrix. -/ reduction : LinearAlgebra.Alternating.Reduction augmented
    pivots
  /-- The reduction output is the retained extra matrix plus these handle blocks. -/ entries : ∀ row column,
    reduction.output row column = extra row column + Handle.Basic.handleEntry pivots row column
  /-- All retained handle indices are pairwise distinct. -/ disjoint : (Handle.Basic.handleIndices pivots).Nodup
  /-- Every retained pivot index occurs positively in the current word. -/ used : ∀ index ∈ Handle.Basic.handleIndices
    pivots, 0 < SignedGenerator.occurrences ⟨index, false⟩ word
  /-- Literal surgery trace for the current word and its integral signature. -/ trace : NormalForm.WordSurgeryTrace word
    integral pivots

constructive_injectivity WordTailForm

/-- Adding a removed handle to the extra matrix leaves it clear on the shorter residual word. -/
theorem ClearOnWord.after_handle {word : List (SignedWord.SignedGenerator count)}
    (selected : Selection.InterlacedAt word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (extra : LinearAlgebra.Matrix.IntegralMatrix count) (clear : NormalForm.ClearOnWord extra
      word) :
    NormalForm.ClearOnWord
      (LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
        Handle.Basic.handleEntry [(selected.cut.first, selected.cut.last)] row column)
      selected.cut.after := by
  let cut := selected.cut
  have counts := selected.counts unique
  have retained (index : Fin count) : SignedGenerator.occurrences ⟨index, false⟩ cut.after ≤
      SignedGenerator.occurrences ⟨index, false⟩ word := by
    have bounded := NormalForm.InterlacedWord.after_occurrences_le cut (⟨index, false⟩ : SignedWord.SignedGenerator
      count)
    rw [selected.rotation.occurrences] at bounded
    exact bounded
  have entryClear (index : Fin count) (positive : 0 < SignedGenerator.occurrences ⟨index, false⟩ cut.after) :
      Lift.ClearAt (LinearAlgebra.Matrix.matrixOfFn (Handle.Basic.handleEntry [(cut.first,
        cut.last)])) index index := by
    have notFirst : index ≠ cut.first := by
      intro same; rw [NormalForm.InterlacedWord.after_pivot_absent cut counts index (Or.inl same) false] at positive;
        omega
    have notLast : index ≠ cut.last := by
      intro same; rw [NormalForm.InterlacedWord.after_pivot_absent cut counts index (Or.inr same) false] at positive;
        omega
    exact NormalForm.single_handle_clear cut.first cut.last index index notFirst notLast notFirst notLast
  constructor
  · intro index positive other
    change 0 < SignedGenerator.occurrences ⟨index, false⟩ cut.after at positive
    have original : 0 < SignedGenerator.occurrences ⟨index, false⟩ word := by have := retained index; omega
    have zero := (entryClear index positive).row_first other
    rw [LinearAlgebra.Matrix.matrixOfFn_apply] at zero
    rw [LinearAlgebra.Matrix.matrixOfFn_apply, clear.row index original, zero, zero_add]
  · intro index positive other
    change 0 < SignedGenerator.occurrences ⟨index, false⟩ cut.after at positive
    have original : 0 < SignedGenerator.occurrences ⟨index, false⟩ word := by have := retained index; omega
    have zero := (entryClear index positive).column_first other
    rw [LinearAlgebra.Matrix.matrixOfFn_apply] at zero
    rw [LinearAlgebra.Matrix.matrixOfFn_apply, clear.column index original, zero, zero_add]

set_option genInjectivity false in
/-- The finite handle step retains the matrix, target signature, and its certificates before recursing on the shorter
word. -/
structure PreparedHandle {word : List (SignedWord.SignedGenerator count)}
    (integral : Surgery.IntegralWordSignature word) (extra augmented :
      LinearAlgebra.Matrix.IntegralMatrix count)
    (selected : Selection.InterlacedAt word) where
  /-- Cached integral signature of the actual shorter word. -/ target : Surgery.IntegralWordSignature selected.cut.after
  /-- The selected pivot's matrix step lifted to the augmented matrix. -/ lifted : Reduction.Basic.Step augmented
    (selected.cut.first, selected.cut.last)
  /-- The lifted output splits into the enlarged extra matrix and cached residual signature. -/ nextSplit : ∀ row
    column, lifted.output row column =
    (LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
      Handle.Basic.handleEntry [(selected.cut.first, selected.cut.last)] row column) row column + target.matrix row
        column
  /-- The enlarged extra matrix is clear on every index used by the shorter word. -/ nextClear : NormalForm.ClearOnWord
    (LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
      Handle.Basic.handleEntry [(selected.cut.first, selected.cut.last)] row column) selected.cut.after

constructive_injectivity PreparedHandle

/-- Prepare the selected handle's lifted matrix step and residual word signature.

The construction reuses the computed step output and proves the next extra-matrix split and clearance before recursion.
-/
@[expose] def PreparedHandle.build {word : List (SignedWord.SignedGenerator count)}
    (integral : Surgery.IntegralWordSignature word) (extra augmented :
      LinearAlgebra.Matrix.IntegralMatrix count)
    (split : ∀ row column, augmented row column = extra row column + integral.matrix row column)
    (clear : NormalForm.ClearOnWord extra word) (selected : Selection.InterlacedAt word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) :
    NormalForm.PreparedHandle integral extra augmented selected :=
  let cut := selected.cut
  let counts := selected.counts unique
  let balanced := selected.closed closed
  let source := selected.rotation.integral integral closed
  let step := Step.build integral.matrix (cut.first, cut.last) (cut.unitPivot source counts).value
  let target := NormalForm.InterlacedWord.afterIntegral cut source counts balanced step.output (fun _ _ => rfl)
  have present (index : Fin count) (pivot : index = cut.first ∨ index = cut.last) :
      0 < SignedGenerator.occurrences ⟨index, false⟩ word := by
    rw [← selected.rotation.occurrences]
    exact NormalForm.InterlacedWord.pivot_present cut index pivot false
  have clearPivot : Lift.ClearAt extra cut.first cut.last :=
    ⟨clear.row _ (present _ (Or.inl rfl)), clear.row _ (present _ (Or.inr rfl)),
      clear.column _ (present _ (Or.inl rfl)), clear.column _ (present _ (Or.inr rfl))⟩
  let lifted := LinearAlgebra.Alternating.Reduction.Lift.Step.withExtra step extra augmented split clearPivot
  let nextExtra := LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
    Handle.Basic.handleEntry [(cut.first, cut.last)] row column
  have nextSplit (row column : Fin count) : lifted.output row column = nextExtra row column + target.matrix row column
    := by
    rw [LinearAlgebra.Alternating.Reduction.Lift.Step.withExtra_output step, LinearAlgebra.Matrix.matrixOfFn_apply]
    have surgery := cut.reduced_eq_handle_add source target counts balanced row column
    change step.output row column = _ at surgery
    rw [surgery]
    omega
  { target := target
    lifted := lifted
    nextSplit := nextSplit
    nextClear := clear.after_handle selected unique extra }

/-- Finish the reduction when the retained word's integral matrix is zero. -/
@[expose] def WordTailForm.ofZero {word : List (SignedWord.SignedGenerator count)}
    (integral : Surgery.IntegralWordSignature word) (extra augmented :
      LinearAlgebra.Matrix.IntegralMatrix count)
    (split : ∀ row column, augmented row column = extra row column + integral.matrix row column)
    (entries : ∀ row column, integral.matrix row column = 0) :
    NormalForm.WordTailForm word integral extra augmented :=
  { pivots := []
    reduction := .nil augmented
    entries := fun row column => by change augmented row column = _; rw [split, entries]; rfl
    disjoint := List.nodup_nil
    used := fun _ member => nomatch member
    trace := .zero integral entries }

/-- Prepend a prepared handle to the shorter word's retained reduction.

The original occurrence bounds certify pivot disjointness and retain every used generator and surgery witness. -/
@[expose] def WordTailForm.ofHandle {word : List (SignedWord.SignedGenerator count)}
    (integral : Surgery.IntegralWordSignature word) (extra augmented :
      LinearAlgebra.Matrix.IntegralMatrix count)
    (selected : Selection.InterlacedAt word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (prepared : NormalForm.PreparedHandle integral extra augmented selected)
    (remaining : NormalForm.WordTailForm selected.cut.after prepared.target
      (LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
        Handle.Basic.handleEntry [(selected.cut.first, selected.cut.last)] row column)
      prepared.lifted.output) : NormalForm.WordTailForm word integral extra augmented :=
  let cut := selected.cut
  let counts := selected.counts unique
  have present (index : Fin count) (pivot : index = cut.first ∨ index = cut.last) :
      0 < SignedGenerator.occurrences ⟨index, false⟩ word := by
    rw [← selected.rotation.occurrences]
    exact NormalForm.InterlacedWord.pivot_present cut index pivot false
  have retained (index : Fin count) : SignedGenerator.occurrences ⟨index, false⟩ cut.after ≤
      SignedGenerator.occurrences ⟨index, false⟩ word := by
    have bounded := NormalForm.InterlacedWord.after_occurrences_le cut (⟨index, false⟩ : SignedWord.SignedGenerator
      count)
    rw [selected.rotation.occurrences] at bounded
    exact bounded
  have notUsed (index : Fin count) (pivot : index = cut.first ∨ index = cut.last) :
      index ∉ Handle.Basic.handleIndices remaining.pivots := by
    intro member
    have positive := remaining.used index member
    rw [NormalForm.InterlacedWord.after_pivot_absent cut counts index pivot false] at positive
    omega
  { pivots := (cut.first, cut.last) :: remaining.pivots
    reduction := .cons prepared.lifted remaining.reduction
    entries := fun row column => by
      change remaining.reduction.output row column = _
      rw [remaining.entries, LinearAlgebra.Matrix.matrixOfFn_apply]
      simp only [Handle.Basic.handleEntry, add_zero]
      ring1
    disjoint := by
      change (cut.first :: cut.last :: Handle.Basic.handleIndices remaining.pivots).Nodup
      exact List.pairwise_cons.mpr
        ⟨fun value member equal => (Data.List.Membership.mem_cons.mp member).elim
          (fun same => cut.distinct (equal.trans same))
          (fun tailMember => notUsed _ (Or.inl rfl) (equal ▸ tailMember)),
          List.pairwise_cons.mpr ⟨fun value member equal =>
            notUsed _ (Or.inr rfl) (equal ▸ member), remaining.disjoint⟩⟩
    used := fun index member => by
      change index ∈ cut.first :: cut.last :: Handle.Basic.handleIndices remaining.pivots at member
      rcases Data.List.Membership.mem_cons.mp member with first | tail
      · exact present index (Or.inl first)
      · rcases Data.List.Membership.mem_cons.mp tail with last | rest
        · exact present index (Or.inr last)
        · have positive := remaining.used index rest
          have bounded := retained index
          change 0 < SignedGenerator.occurrences ⟨index, false⟩ cut.after at positive
          omega
    trace := .handle selected unique closed prepared.target remaining.trace }

/-- Removing the four selected interlaced occurrences strictly shortens the original word. -/
theorem InterlacedAt.after_length_lt {word : List (SignedWord.SignedGenerator count)}
    (selected : Selection.InterlacedAt word) : selected.cut.after.length < word.length := by
  have shortened := selected.cut.after_length
  have rotated := NormalForm.WordRotation.length selected.rotation
  omega

/-- Reduce a unique balanced signed word while retaining an orthogonal extra matrix.

Each selected handle removes four actual occurrences, and the zero branch retains the terminal word and its integral
zero certificate. -/
@[expose] def reduceWord (word : List (SignedWord.SignedGenerator count)) (integral : Surgery.IntegralWordSignature
  word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0)
    (extra augmented : LinearAlgebra.Matrix.IntegralMatrix count)
    (split : ∀ row column, augmented row column = extra row column + integral.matrix row column)
    (clear : NormalForm.ClearOnWord extra word) : NormalForm.WordTailForm word integral extra augmented :=
  match Selection.selectWord word integral unique closed with
  | .zero entries => NormalForm.WordTailForm.ofZero integral extra augmented split entries
  | .handle selected =>
      let prepared := NormalForm.PreparedHandle.build integral extra augmented split clear selected unique closed
      let nextExtra := LinearAlgebra.Matrix.matrixOfFn fun row column => extra row column +
        Handle.Basic.handleEntry [(selected.cut.first, selected.cut.last)] row column
      let remaining := Purelib.Topology.Surface.Word.NormalForm.reduceWord selected.cut.after prepared.target
        (selected.cut.after_counts_le (selected.counts unique))
        (fun index => (selected.cut.after_total index).trans ((selected.closed closed) index))
        nextExtra prepared.lifted.output prepared.nextSplit prepared.nextClear
      NormalForm.WordTailForm.ofHandle integral extra augmented selected unique closed prepared remaining
termination_by word.length
decreasing_by
  exact NormalForm.InterlacedAt.after_length_lt selected

/-- Total normal-form construction for every unique balanced signed word. The finite matrix and literal surgery trace
are both returned as data. -/
@[expose] def normalizeWord (word : List (SignedWord.SignedGenerator count)) (integral : Surgery.IntegralWordSignature
  word)
    (unique : ∀ index reversed, SignedGenerator.occurrences ⟨index, reversed⟩ word ≤ 1)
    (closed : ∀ index, Pairing.totalAt (word.map SignedGenerator.coefficients) index = 0) : NormalForm.WordNormalForm
      word integral :=
  let result := NormalForm.reduceWord word integral unique closed
    (LinearAlgebra.Matrix.matrixOfFn fun _ _ => 0) integral.matrix
    (fun row column => by rw [LinearAlgebra.Matrix.matrixOfFn_apply, zero_add])
    ⟨fun _ _ _ => LinearAlgebra.Matrix.matrixOfFn_apply _ _ _, fun _ _ _ =>
      LinearAlgebra.Matrix.matrixOfFn_apply _ _ _⟩
  { pivots := result.pivots
    normal :=
      { reduction := result.reduction
        disjoint := result.disjoint
        entries := fun row column => by have := result.entries row column; rw
          [LinearAlgebra.Matrix.matrixOfFn_apply, zero_add] at this; exact this }
    used := result.used
    trace := result.trace }

end Purelib.Topology.Surface.Word.NormalForm
