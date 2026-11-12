module

public import Purelib.Approximation.Gaussian.Sequence.Selection
public import Purelib.Data.Vector.DependentMatrix
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained finite pair separation for original candidate programs

Every pair keeps its own original programs, certified start indices and
positive squared gap. A dependent matrix materializes those actual certificates
once. Its same stored entries compute a common finite starting stage and
positive gap for stable selection without shifting the original programs.
-/

public section

namespace Purelib.Approximation.Gaussian.Sequence.Selection

open Purelib
open Purelib.Data.Vector (DependentMatrix)
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {count : Nat} {candidates : Fin count → ApproximationData}

set_option genInjectivity false in
/-- A retained tail-gap certificate for two same-index original candidate programs.

The lower bound applies when the original bounded indices differ. Each input
keeps its own original starting stage; the certificate changes no program or
sample index. Diagonal entries retain harmless finite data with an impossible
different-index premise.
-/
structure PairBound (candidates : Fin count → ApproximationData) (first second : Fin count) where
  /-- The retained separation start of the original first candidate. -/
  leftIndex : Nat
  /-- The retained separation start of the original second candidate. -/
  rightIndex : Nat
  /-- The actual retained common squared-gap budget for this pair. -/
  gap : Fraction.Rational
  /-- The retained pair gap is positive. -/
  positive : 0 < gap
  /-- Distinct original indices retain this same gap at every pair of permitted original readings. -/
  lower : first ≠ second → ∀ firstLater secondLater, leftIndex ≤ firstLater → rightIndex ≤ secondLater →
    gap ≤ normSq ((candidates first).sample firstLater - (candidates second).sample secondLater)

constructive_injectivity PairBound

namespace PairBound

/-- Retain a diagonal pair without asserting separation between a program and itself. -/
def diagonal (candidates : Fin count → ApproximationData) (index : Fin count) : PairBound candidates index index :=
  ⟨0, 0, 1, by decide, fun different _ _ _ _ => (different rfl).elim⟩

/-- Reverse the same original pair programs, retained starts and squared-gap certificate. -/
def symm {first second : Fin count} (bound : PairBound candidates first second) : PairBound candidates second first :=
  { leftIndex := bound.rightIndex
    rightIndex := bound.leftIndex
    gap := bound.gap
    positive := bound.positive
    lower := by
      intro different secondLater firstLater secondOrder firstOrder
      have lower := bound.lower (fun equal => different equal.symm) firstLater secondLater firstOrder secondOrder
      have reversed : (candidates second).sample secondLater - (candidates first).sample firstLater =
          -((candidates first).sample firstLater - (candidates second).sample secondLater) := by ring0
      rewrite [reversed, Data.Gaussian.Norm.Basic.normSq_neg]
      exact lower }

end PairBound

/-- One stored row-major spine of pair certificates at their original bounded row and column indices.

The finite pair code preserves both original indices and their actual
certificate types. A single dependent spine avoids increasing the universe
once for each dimension of the same finite matrix.
-/
abbrev PairEntries (candidates : Fin count → ApproximationData) :=
  DependentMatrix (fun first second => PairBound candidates first second)

namespace PairEntries

/-- Read the complete stored certificate at its same original row and column. -/
@[expose] def get (entries : PairEntries candidates) (first second : Fin count) : PairBound candidates first second :=
  DependentMatrix.get entries first second

/-- Materialize each original pair certificate once in row-major order. -/
def ofFn (producer : ∀ first second, PairBound candidates first second) : PairEntries candidates :=
  DependentMatrix.ofFn producer

/-- A materialized entry is the complete original producer value at the unchanged pair of bounded indices. -/
theorem get_ofFn (producer : ∀ first second, PairBound candidates first second) (first second : Fin count) :
    get (ofFn producer) first second = producer first second :=
  DependentMatrix.ofFn_get producer first second

/-- Compute a common original stage from both starts of every same stored pair certificate. -/
def commonStart (entries : PairEntries candidates) : Nat :=
  Nat.max
    (DependentMatrix.maximum entries (fun _ _ bound => bound.leftIndex))
    (DependentMatrix.maximum entries (fun _ _ bound => bound.rightIndex))

/-- A ceiling on both starts of every original pair bounds the same retained matrix's common start. -/
theorem commonStart_le (entries : PairEntries candidates) (ceiling : Nat)
    (bounded : ∀ first second, (get entries first second).leftIndex ≤ ceiling ∧
      (get entries first second).rightIndex ≤ ceiling) : commonStart entries ≤ ceiling := by
  apply Data.Nat.Order.max_le
  · exact DependentMatrix.maximum_le entries (fun _ _ bound => bound.leftIndex) ceiling
      (fun first second => (bounded first second).1)
  · exact DependentMatrix.maximum_le entries (fun _ _ bound => bound.rightIndex) ceiling
      (fun first second => (bounded first second).2)

/-- Materialize the original stored pair gaps in their original bounded row and column order. -/
def gapRows (entries : PairEntries candidates) : List (List Fraction.Rational) :=
  List.ofFn (fun first : Fin count => List.ofFn (fun second : Fin count => (get entries first second).gap))

/-- Compute the common positive-minimum gap from the same retained original pair entries. -/
def commonGap (entries : PairEntries candidates) : Fraction.Rational :=
  Data.Rat.List.Minimum.positiveMinimum ((gapRows entries).map Data.Rat.List.Minimum.positiveMinimum)

end PairEntries

set_option genInjectivity false in
/-- A materialized original pair matrix with its same-entry starting stage and gap summaries.

The actual dependent entries remain stored. Both summaries retain defining
equalities to those same entries; downstream selection reads the stored
certificates and budgets rather than rerunning pair preparation.
-/
structure Pairs (candidates : Fin count → ApproximationData) where
  /-- The actual original pair certificates, each computed once. -/
  entries : PairEntries candidates
  /-- The cached common original starting stage. -/
  start : Nat
  /-- The common stage is computed from the same stored original pair starts. -/
  start_eq : start = PairEntries.commonStart entries
  /-- The cached common squared separation budget. -/
  gap : Fraction.Rational
  /-- The common gap is computed from the same stored original pair gaps. -/
  gap_eq : gap = PairEntries.commonGap entries

constructive_injectivity Pairs

namespace Pairs

/-- Cache the common starting stage and gap of these actual retained pair certificates.

Both summaries are computed from the supplied original matrix itself. No
entry producer or numerical separation procedure is called again.
-/
def ofEntries (entries : PairEntries candidates) : Pairs candidates :=
  let start := PairEntries.commonStart entries
  let gap := PairEntries.commonGap entries
  ⟨entries, start, rfl, gap, rfl⟩

/-- Compute every original pair certificate once and cache the summaries of those same retained entries. -/
def ofFn (producer : ∀ first second, PairBound candidates first second) : Pairs candidates :=
  ofEntries (PairEntries.ofFn producer)

/-- Build the complete original pair bank from checked row-major monadic entry reads.

The actual returned certificates determine both cached summaries. The
continuation retains equality to the whole default bank, including every
entry, stage and gap; effects and failures belong to the supplied reader.
-/
def ofFnM {m : Type → Type} [Monad m] {α : Type}
    (producer : ∀ first second, PairBound candidates first second)
    (load : ∀ first second, m {entry : PairBound candidates first second // entry = producer first second})
    (use : {pairs : Pairs candidates // pairs = ofFn producer} → m α) : m α :=
  DependentMatrix.ofFnM producer load fun entries =>
    use ⟨ofEntries entries.val, congrArg ofEntries entries.property⟩

/-- Read the actual original pair certificate at its unchanged bounded row and column indices. -/
@[expose] def get (pairs : Pairs candidates) (first second : Fin count) : PairBound candidates first second :=
  PairEntries.get pairs.entries first second

/-- Reading the materialized pair bank returns the complete original producer certificate at that same pair. -/
theorem ofFn_get (producer : ∀ first second, PairBound candidates first second) (first second : Fin count) :
    (ofFn producer).get first second = producer first second :=
  PairEntries.get_ofFn producer first second

/-- The first original pair start fits the same stored common starting stage. -/
theorem leftIndex_le (pairs : Pairs candidates) (first second : Fin count) :
    (pairs.get first second).leftIndex ≤ pairs.start := by
  have stored := DependentMatrix.get_le_maximum pairs.entries (fun _ _ bound => bound.leftIndex) first second
  have bound : (pairs.get first second).leftIndex ≤ PairEntries.commonStart pairs.entries :=
    stored.trans (Data.Nat.Order.le_max_left _ _)
  exact bound.trans_eq pairs.start_eq.symm

/-- The second original pair start fits the same stored common starting stage. -/
theorem rightIndex_le (pairs : Pairs candidates) (first second : Fin count) :
    (pairs.get first second).rightIndex ≤ pairs.start := by
  have stored := DependentMatrix.get_le_maximum pairs.entries (fun _ _ bound => bound.rightIndex) first second
  have bound : (pairs.get first second).rightIndex ≤ PairEntries.commonStart pairs.entries :=
    stored.trans (Data.Nat.Order.le_max_right _ _)
  exact bound.trans_eq pairs.start_eq.symm

/-- Positive original pair gaps give a positive cached common gap, including an empty family's unit convention. -/
theorem gap_positive (pairs : Pairs candidates) : 0 < pairs.gap := by
  rewrite [pairs.gap_eq]
  apply Data.Rat.List.Minimum.positiveMinimum_pos
  intro value member
  rcases Data.List.Map.mem_map.mp member with ⟨row, rowMember, rfl⟩
  rcases Data.List.OfFn.Basic.mem_ofFn.mp rowMember with ⟨first, row_eq⟩
  rewrite [← row_eq]
  apply Data.Rat.List.Minimum.positiveMinimum_pos
  intro value member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨second, value_eq⟩
  rewrite [← value_eq]
  exact (pairs.get first second).positive

/-- The cached common gap fits the actual original pair budget at every retained row and column. -/
theorem gap_le (pairs : Pairs candidates) (first second : Fin count) :
    pairs.gap ≤ (pairs.get first second).gap := by
  let row := List.ofFn (fun other : Fin count => (pairs.get first other).gap)
  have rowMember : row ∈ PairEntries.gapRows pairs.entries := Data.List.OfFn.Basic.mem_ofFn.mpr ⟨first, rfl⟩
  have minimumMember : Data.Rat.List.Minimum.positiveMinimum row ∈
      (PairEntries.gapRows pairs.entries).map Data.Rat.List.Minimum.positiveMinimum :=
    Data.List.Map.mem_map_of_mem rowMember
  have outer := Data.Rat.List.Minimum.positiveMinimum_le_of_mem minimumMember
  have inner := Data.Rat.List.Minimum.positiveMinimum_le_of_mem
    (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨second, rfl⟩ : (pairs.get first second).gap ∈ row)
  exact (pairs.gap_eq.trans_le outer).trans inner

/-- Assemble stable-selection separation from the same original retained pair certificates and cached summaries. -/
@[expose] def separated (pairs : Pairs candidates) : Separated candidates where
  gap := pairs.gap
  positive := pairs.gap_positive
  starts := fun _ => pairs.start
  lower first second different firstLater secondLater firstOrder secondOrder :=
    (pairs.gap_le first second).trans ((pairs.get first second).lower different firstLater secondLater
      ((pairs.leftIndex_le first second).trans firstOrder) ((pairs.rightIndex_le first second).trans secondOrder))

end Pairs

end Purelib.Approximation.Gaussian.Sequence.Selection

end
