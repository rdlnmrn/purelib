module

public import Purelib.Polynomial.Recurrence.Mode.Hermite
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift
public import Purelib.Polynomial.Recurrence.Boundary.Shift
public import Purelib.LinearAlgebra.Matrix.NormalForm.Truncation
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained rectangular confluent reading coordinates

One completed original Hermite word supplies both the finite horizon cache
and the actual rectangular normal form. Extra columns complete only a finite
coordinate transformation; the original word and its cached occurrence prefix
still index the selected source columns.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

namespace Rectangle

/-- Repeat the first original tag only as far as needed for a target-coordinate completion. -/
@[expose] def padding {Tag : Type*} : List Tag → Nat → List Tag
  | [], _ => []
  | head :: tail, rows => List.replicate (rows - (tail.length + 1)) head

/-- An already long enough original word needs no auxiliary coordinate columns. -/
theorem padding_eq_nil {Tag : Type*} (word : List Tag) (rows : Nat) (enough : rows ≤ word.length) :
    padding word rows = [] := by
  cases word with
  | nil => rfl
  | cons head tail =>
      change rows ≤ tail.length + 1 at enough
      rw [padding, Nat.sub_eq_zero_of_le enough, List.replicate_zero]

/-- Completing a nonempty shorter word supplies exactly the requested target dimension. -/
theorem completed_length {Tag : Type*} (word : List Tag) (rows : Nat)
    (nonempty : word ≠ []) (short : word.length ≤ rows) :
    (word ++ padding word rows).length = rows := by
  cases word with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      change tail.length + 1 ≤ rows at short
      rw [Append.length_append, padding, Replicate.length_replicate]
      change tail.length + 1 + (rows - (tail.length + 1)) = rows
      omega0

end Rectangle

variable {K : Type*} [CommRing K]

set_option genInjectivity false in
/-- A completed original basis and its cached selected horizon, initial rectangle and coordinate normal form.

The original word retains its own occurrence owner by taking the same cached
prefix. The auxiliary word completes finite coordinates only. Both the actual
initial reading matrix and its existing normal form are retained, with their
identity-block size proved from the computed transforms.
-/
structure Rectangle (blocks : List (Block K)) (differences : SquareMatrix K blocks.length)
    (word : List (Fin blocks.length)) (rows count : Nat) where
  /-- The actual original word with its deterministic auxiliary coordinate suffix. -/
  completed : List (Fin blocks.length)
  /-- The completed cache uses exactly the original word and its selected padding. -/
  completed_eq : completed = word ++ Rectangle.padding word rows
  /-- Original source columns retain bounded coordinates in the same completed word. -/
  word_le : word.length ≤ completed.length
  /-- The one actual prepared Hermite basis of the completed word. -/
  basis : Hermite blocks differences completed
  /-- The original word's occurrence cache, extracted from the same completed cache. -/
  occurrences : Occurrences word
  /-- The original occurrence data are the actual retained completed prefix. -/
  occurrences_eq : occurrences =
    (completed_eq ▸ basis.occurrences).take word (Rectangle.padding word rows)
  /-- The same completed basis's actual finite horizon cache. -/
  readings : Rectangular K count completed.length
  /-- The horizon retains the original prepared initial rows. -/
  readings_eq : readings = basis.horizon count
  /-- The selected original source columns, retained as finite structural vectors. -/
  values : Vec (Vec K count) word.length
  /-- These columns are the actual original prefix of the same retained horizon. -/
  values_eq : values = Rectangular.transpose (Rectangular.takeColumns word_le readings)
  /-- The retained horizon includes every requested initial row. -/
  room : rows ≤ count
  /-- The actual initial reading rectangle on the selected original columns. -/
  initial : Rectangular K rows word.length
  /-- The initial cache reads the same original finite input columns. -/
  initial_eq : initial = Boundary.initial values rows
  /-- The existing original normal form of this exact retained rectangle. -/
  normal : NormalForm initial
  /-- The constructed identity-block size is exactly the smaller original dimension. -/
  rank_eq : normal.rank = Nat.min rows word.length

constructive_injectivity Rectangle

namespace Rectangle

variable {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
variable {word : List (Fin blocks.length)} {rows count : Nat}

/-- The selected finite columns read exactly their original word roots and cached original occurrence orders. -/
theorem values_at (retained : Rectangle blocks differences word rows count)
    (column : Fin word.length) (index : Fin count) :
    retained.values column index =
      entry (point blocks (word[column.val]'column.isLt)) (retained.occurrences.orders column) index.val := by
  cases retained with
  | mk completed completedEq wordLe basis occurrences occurrencesEq readings readingsEq values valuesEq room
      initial initialEq normal rankEq =>
      cases completedEq
      cases occurrencesEq
      cases readingsEq
      cases valuesEq
      rw [Rectangular.transpose_apply, Rectangular.takeColumns_at,
        horizon_prefix word (padding word rows) basis count index column, row_at]

/-- An available natural reading uses the same retained original root and occurrence order. -/
theorem reading_at (retained : Rectangle blocks differences word rows count) (index : Nat)
    (inside : index < count) (column : Fin word.length) :
    sample (retained.values column) index =
      entry (point blocks (word[column.val]'column.isLt)) (retained.occurrences.orders column) index :=
  (sample_at _ ⟨index, inside⟩).trans (retained.values_at column ⟨index, inside⟩)

/-- The selected cached original columns follow their same retained original shift at every available step. -/
theorem follows (retained : Rectangle blocks differences word rows count)
    (shift : Shift blocks word retained.occurrences) : Boundary.Transition retained.values shift.matrix := by
  intro index inside column
  have earlier : index < count := by omega0
  calc
    _ = sumFin (fun middle =>
        entry (point blocks (word[middle.val]'middle.isLt)) (retained.occurrences.orders middle) index *
          shift.matrix middle column) := by
      apply sumFin_congr
      intro middle
      rw [retained.reading_at index earlier middle]
    _ = entry (point blocks (word[column.val]'column.isLt)) (retained.occurrences.orders column) (index + 1) := by
      rewrite [shift.matrix_eq]
      exact Shift.row_step (point blocks) word retained.occurrences index column
    _ = _ := (retained.reading_at (index + 1) inside column).symm

/-- Available initial readings of a cached horizon reuse its same prepared structural matrix entries. -/
theorem initial_entry {completed : List (Fin blocks.length)} (basis : Hermite blocks differences completed)
    (cut : Nat) (bound : cut ≤ completed.length) (count rows : Nat)
    (room : rows ≤ count) (initialBound : rows ≤ completed.length) (index : Fin rows) (column : Fin cut) :
    Boundary.initial (Rectangular.transpose (Rectangular.takeColumns bound (basis.horizon count))) rows
        index column =
      basis.matrix ⟨index.val, Nat.lt_of_lt_of_le index.isLt initialBound⟩
        ⟨column.val, Nat.lt_of_lt_of_le column.isLt bound⟩ := by
  let inside : Fin count := ⟨index.val, Nat.lt_of_lt_of_le index.isLt room⟩
  rw [Boundary.initial_at, sample_at _ inside, Rectangular.transpose_apply, Rectangular.takeColumns_at]
  rw [horizon, vectorOfFn_apply, readRow, dif_pos (Nat.lt_of_lt_of_le index.isLt initialBound)]

/-- Construct the actual rectangular confluent coordinates without a rank or basis premise.

One deterministic word completion is prepared through the original Hermite
constructor. Its cached original prefix supplies the requested columns. A
right inverse normalizes initial rows when rows are fewer; a left inverse
normalizes initial columns otherwise. Empty source words retain the zero
rectangle directly.
-/
@[expose] def prepare (blocks : List (Block K)) (differences : SquareMatrix K blocks.length)
    (units : ∀ first second : Fin blocks.length, first ≠ second →
      (point blocks first - point blocks second) * differences first second = 1)
    (word : List (Fin blocks.length)) (rows count : Nat) (room : rows ≤ count) :
    Rectangle blocks differences word rows count := by
  let auxiliary := padding word rows
  let completed := word ++ auxiliary
  let basis := Hermite.prepare blocks differences units completed
  have wordLe : word.length ≤ completed.length := by
    dsimp only [completed]
    rw [Append.length_append]
    exact Nat.le_add_right _ _
  let occurrences := basis.occurrences.take word auxiliary
  let readings := basis.horizon count
  let values := Rectangular.transpose (Rectangular.takeColumns wordLe readings)
  let initial := Boundary.initial values rows
  have coordinates : { normal : NormalForm initial // normal.rank = Nat.min rows word.length } := by
    by_cases smaller : rows ≤ word.length
    · have size : completed.length = word.length := by
        dsimp only [completed, auxiliary]
        rw [padding_eq_nil word rows smaller, Append.append_nil]
      have initialBound : rows ≤ completed.length := Nat.le_trans smaller wordLe
      let reduced := NormalForm.ofInitialRows initialBound basis.inverse basis.inverse_scalar
      let transported := NormalForm.cast rfl size reduced
      have original : Rectangular.cast rfl size (Rectangular.takeRows initialBound basis.matrix) = initial := by
        apply Rectangular.ext
        intro index column
        rw [Rectangular.cast_at, Rectangular.takeRows_at]
        exact (initial_entry basis word.length wordLe count rows room initialBound index column).symm
      let normal := NormalForm.ofEq original transported
      refine ⟨normal, ?_⟩
      have rank : normal.rank = rows :=
        (NormalForm.ofEq_rank original transported).trans
          ((NormalForm.cast_rank rfl size reduced).trans (NormalForm.ofInitialRows_rank _ _ _))
      exact rank.trans (by
        change rows = if rows ≤ word.length then rows else word.length
        exact (if_pos smaller).symm)
    · by_cases empty : word = []
      · have noColumn : ∀ column : Fin word.length, False := by
          intro column
          let position := column.val
          have bound : position < word.length := column.isLt
          have zeroCount : word.length = 0 := congrArg List.length empty
          rw [zeroCount] at bound
          exact Nat.not_lt_zero position bound
        let normal := NormalForm.ofZero initial (fun _ column => (noColumn column).elim)
        refine ⟨normal, ?_⟩
        have minimum : Nat.min rows word.length = 0 := by
          rw [empty]
          cases rows <;> rfl
        exact minimum.symm
      · have lower : word.length ≤ rows := Nat.le_of_lt (Nat.lt_of_not_ge smaller)
        have size : completed.length = rows := completed_length word rows empty lower
        let reduced := NormalForm.ofInitialColumns wordLe basis.inverse basis.inverse_scalar
        let transported := NormalForm.cast size rfl reduced
        have initialBound : rows ≤ completed.length := Nat.le_of_eq size.symm
        have original : Rectangular.cast size rfl (Rectangular.takeColumns wordLe basis.matrix) = initial := by
          apply Rectangular.ext
          intro index column
          rw [Rectangular.cast_at, Rectangular.takeColumns_at]
          exact (initial_entry basis word.length wordLe count rows room initialBound index column).symm
        let normal := NormalForm.ofEq original transported
        refine ⟨normal, ?_⟩
        have rank : normal.rank = word.length :=
          (NormalForm.ofEq_rank original transported).trans
            ((NormalForm.cast_rank size rfl reduced).trans (NormalForm.ofInitialColumns_rank _ _ _))
        exact rank.trans (by
          change word.length = if rows ≤ word.length then rows else word.length
          exact (if_neg smaller).symm)
  exact
    { completed := completed
      completed_eq := rfl
      word_le := wordLe
      basis := basis
      occurrences := occurrences
      occurrences_eq := rfl
      readings := readings
      readings_eq := rfl
      values := values
      values_eq := rfl
      room := room
      initial := initial
      initial_eq := rfl
      normal := coordinates.val
      rank_eq := coordinates.property }

end Rectangle

end Purelib.Polynomial.Recurrence.Mode.Hermite

end
