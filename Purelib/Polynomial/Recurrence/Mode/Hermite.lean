module

public import Purelib.Polynomial.Recurrence.Mode
public import Purelib.Polynomial.Dense.Roots.Word
public import Purelib.Data.List.Occurrences
public import Purelib.LinearAlgebra.Matrix.Triangular.Inverse
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Confluent mode coordinates from original ordered root blocks

Occurrence orders and bounded predecessors belong to the same original word
of block indices. First-order differences lower the first block and act on
other blocks by an upper-triangular unit change of coordinates.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K]

namespace Hermite

/-- Read the scalar of one original bounded root block. -/
abbrev point (blocks : List (Block K)) (index : Fin blocks.length) : K :=
  (blocks[index.val]'index.isLt).point

/-- Materialize one finite original mode row from the same retained roots and occurrence orders. -/
@[expose] def row (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) (index : Nat) : Vec K word.length :=
  vectorOfFn fun column =>
    entry (point blocks (word[column.val]'column.isLt)) (occurrences.orders column) index

/-- Reading an original mode row uses its same original scalar and occurrence order. -/
theorem row_at (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) (index : Nat) (column : Fin word.length) :
    row blocks word occurrences index column =
      entry (point blocks (word[column.val]'column.isLt)) (occurrences.orders column) index :=
  vectorOfFn_apply _ _

/-- Materialize the original initial table using its same original row producer and retained occurrence orders. -/
@[expose] def initial (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) : SquareMatrix K word.length :=
  vectorOfFn fun index => row blocks word occurrences index.val

/-- Reading a retained initial mode matrix returns the same original root and occurrence order. -/
theorem initial_at (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) (row column : Fin word.length) :
    initial blocks word occurrences row column =
      entry (point blocks (word[column.val]'column.isLt)) (occurrences.orders column) row.val :=
  matrixOfFn_apply _ _ _

/-- The original first-order difference matrix retains the first coordinate unchanged. -/
@[expose] def difference (center : K) (size : Nat) : SquareMatrix K size :=
  let opposite := -center
  matrixOfFn fun row column =>
    if row = column then 1 else if column.val + 1 = row.val then opposite else 0

/-- Read a difference entry through its two original bounded coordinates. -/
theorem difference_at (center : K) (size : Nat) (row column : Fin size) :
    difference center size row column =
      if row = column then 1 else if column.val + 1 = row.val then -center else 0 :=
  matrixOfFn_apply _ _ _

/-- The difference matrix is lower triangular at its same original coordinates. -/
theorem difference_lower (center : K) (size : Nat) : Triangular.IsLower (difference center size) := by
  intro row column before
  rw [difference_at]
  have different : row ≠ column := by
    intro equal
    have same := congrArg Fin.val equal
    omega0
  have notPrevious : ¬column.val + 1 = row.val := by omega0
  rw [if_neg different, if_neg notPrevious]

/-- Every original difference diagonal entry is one, including at the zero center. -/
theorem difference_diagonal (center : K) (size : Nat) (index : Fin size) :
    difference center size index index = 1 := by
  rw [difference_at, if_pos rfl]

/-- The difference action retains the original first input coordinate. -/
theorem difference_first (center : K) {size : Nat} (values : Vec K (size + 1)) :
    Rectangular.apply (difference center (size + 1)) values 0 = values 0 := by
  rw [Rectangular.apply_at]
  calc
    _ = sumFin (fun column => if column = 0 then values column else 0) := by
      apply sumFin_congr
      intro column
      rw [difference_at]
      by_cases first : column = 0
      · cases first
        rw [if_pos rfl, if_pos rfl, one_mul]
      · have notPrevious : ¬column.val + 1 = (0 : Fin (size + 1)).val := by
          change ¬column.val + 1 = 0
          exact Nat.succ_ne_zero column.val
        rw [if_neg (Ne.symm first), if_neg first, if_neg notPrevious, zero_mul]
    _ = values 0 := sumFin_ite_eq 0 _

/-- Each remaining difference coordinate is its original successor minus the center-scaled predecessor. -/
theorem difference_succ (center : K) {size : Nat} (values : Vec K (size + 1)) (row : Fin size) :
    Rectangular.apply (difference center (size + 1)) values row.succ =
      values row.succ - center * values row.castSucc := by
  rw [Rectangular.apply_at]
  calc
    _ = sumFin (fun column =>
        (if column = row.succ then values column else 0) +
        (if column = row.castSucc then -center * values column else 0)) := by
      apply sumFin_congr
      intro column
      rw [difference_at]
      by_cases same : column = row.succ
      · cases same
        have different : row.succ ≠ row.castSucc := by
          intro equal
          have values := congrArg Fin.val equal
          change row.val + 1 = row.val at values
          omega0
        rw [if_pos rfl, if_pos rfl, if_neg different, one_mul, add_zero]
      · rw [if_neg (Ne.symm same), if_neg same]
        by_cases previous : column = row.castSucc
        · cases previous
          have adjacent : row.castSucc.val + 1 = row.succ.val := by rfl
          rw [if_pos adjacent, if_pos rfl, zero_add]
        · have notPrevious : ¬column.val + 1 = row.succ.val := by
            intro equal
            exact previous (Fin.ext (Nat.succ.inj equal))
          rw [if_neg notPrevious, if_neg previous, zero_mul, zero_add]
    _ = values row.succ + -center * values row.castSucc := by
      rw [sumFin_add, sumFin_ite_eq, sumFin_ite_eq]
    _ = values row.succ - center * values row.castSucc := by ring0

/-- The first row of a difference product is the same original input row. -/
theorem difference_mul_first (center : K) {size columns : Nat}
    (matrix : Rectangular K (size + 1) columns) (column : Fin columns) :
    Rectangular.mul (difference center (size + 1)) matrix 0 column = matrix 0 column := by
  have action := congrArg (fun values => values (0 : Fin (size + 1)))
    (Rectangular.apply_column (difference center (size + 1)) matrix column)
  rw [difference_first, Rectangular.column_at, Rectangular.column_at] at action
  exact action.symm

/-- A remaining row of a difference product uses its two same original input rows. -/
theorem difference_mul_succ (center : K) {size columns : Nat}
    (matrix : Rectangular K (size + 1) columns) (row : Fin size) (column : Fin columns) :
    Rectangular.mul (difference center (size + 1)) matrix row.succ column =
      matrix row.succ column - center * matrix row.castSucc column := by
  have action := congrArg (fun values => values row.succ)
    (Rectangular.apply_column (difference center (size + 1)) matrix column)
  rw [difference_succ, Rectangular.column_at, Rectangular.column_at,
    Rectangular.column_at] at action
  exact action.symm

/-- The column change induced by taking a difference at the original first root.

The same-root columns are unchanged. Every other root receives its unit root
difference on the diagonal and its retained predecessor at the previous order.
-/
@[expose] def columnChange (blocks : List (Block K)) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (occurrences : Occurrences tail) : SquareMatrix K tail.length :=
  matrixOfFn fun row column =>
    if row = column then
      if tail[column.val]'column.isLt = head then 1
      else point blocks (tail[column.val]'column.isLt) - point blocks head
    else
      match occurrences.predecessors column with
      | some previous => if previous = row ∧ tail[column.val]'column.isLt ≠ head then 1 else 0
      | none => 0

/-- The column-change diagonal is the original root difference or the same-root unit. -/
theorem columnChange_diagonal (blocks : List (Block K)) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (occurrences : Occurrences tail) (index : Fin tail.length) :
    columnChange blocks head tail occurrences index index =
      if tail[index.val]'index.isLt = head then 1
      else point blocks (tail[index.val]'index.isLt) - point blocks head := by
  rw [columnChange, matrixOfFn_apply, if_pos rfl]

/-- Every off-diagonal predecessor in the same original column change lies strictly above the diagonal. -/
theorem columnChange_upper (blocks : List (Block K)) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (occurrences : Occurrences tail) :
    Triangular.IsUpper (columnChange blocks head tail occurrences) := by
  intro row column before
  rw [columnChange, matrixOfFn_apply]
  have different : row ≠ column := by
    intro equal
    have values := congrArg Fin.val equal
    omega0
  rw [if_neg different]
  cases previous : occurrences.predecessors column with
  | none => rfl
  | some index =>
      have facts := occurrences.some_spec column index previous
      have impossible : ¬(index = row ∧ tail[column.val]'column.isLt ≠ head) := by
        intro both
        have sameIndex := congrArg Fin.val both.1
        have earlier := facts.1
        omega0
      change (if index = row ∧ tail[column.val]'column.isLt ≠ head then (1 : K) else 0) = 0
      rw [if_neg impossible]

/-- The retained column change is the sum of its original diagonal and bounded predecessor entries. -/
theorem columnChange_at (blocks : List (Block K)) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (occurrences : Occurrences tail) (row column : Fin tail.length) :
    columnChange blocks head tail occurrences row column =
      (if row = column then
        (if tail[column.val]'column.isLt = head then 1
         else point blocks (tail[column.val]'column.isLt) - point blocks head) else 0) +
      (match occurrences.predecessors column with
       | some previous => if row = previous ∧ tail[column.val]'column.isLt ≠ head then 1 else 0
       | none => 0) := by
  rw [columnChange, matrixOfFn_apply]
  by_cases same : row = column
  · cases same
    rw [if_pos rfl, if_pos rfl]
    cases previous : occurrences.predecessors row with
    | none => exact (add_zero _).symm
    | some index =>
        have facts := occurrences.some_spec row index previous
        have different : row ≠ index := by
          intro equal
          have values := congrArg Fin.val equal
          have before := facts.1
          omega0
        change _ = _ + (if row = index ∧ tail[row.val]'row.isLt ≠ head then (1 : K) else 0)
        have vanishes : (if row = index ∧ tail[row.val]'row.isLt ≠ head then (1 : K) else 0) = 0 :=
          if_neg (fun both => different both.1)
        rw [vanishes, add_zero]
  · rw [if_neg same, if_neg same, zero_add]
    cases previous : occurrences.predecessors column with
    | none => rfl
    | some index =>
        change (if index = row ∧ tail[column.val]'column.isLt ≠ head then (1 : K) else 0) =
          (if row = index ∧ tail[column.val]'column.isLt ≠ head then 1 else 0)
        by_cases selected : row = index ∧ tail[column.val]'column.isLt ≠ head
        · rw [if_pos ⟨selected.1.symm, selected.2⟩, if_pos selected]
        · have reverse : ¬(index = row ∧ tail[column.val]'column.isLt ≠ head) :=
            fun both => selected ⟨both.1.symm, both.2⟩
          rw [if_neg reverse, if_neg selected]

/-- Multiplying by a column change uses exactly the original diagonal and cached predecessor columns. -/
theorem mul_columnChange (blocks : List (Block K)) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (occurrences : Occurrences tail)
    {rows : Nat} (matrix : Rectangular K rows tail.length) (row : Fin rows) (column : Fin tail.length) :
    Rectangular.mul matrix (columnChange blocks head tail occurrences) row column =
      matrix row column *
        (if tail[column.val]'column.isLt = head then 1
         else point blocks (tail[column.val]'column.isLt) - point blocks head) +
      (match occurrences.predecessors column with
       | some previous => if tail[column.val]'column.isLt ≠ head then matrix row previous else 0
       | none => 0) := by
  rw [Rectangular.mul_at]
  cases previous : occurrences.predecessors column with
  | none =>
      calc
        _ = sumFin (fun index => if index = column then
            matrix row index *
              (if tail[column.val]'column.isLt = head then 1
               else point blocks (tail[column.val]'column.isLt) - point blocks head) else 0) := by
          apply sumFin_congr
          intro index
          rw [columnChange_at, previous]
          by_cases same : index = column
          · rw [if_pos same, if_pos same, add_zero]
          · rw [if_neg same, if_neg same, zero_add, mul_zero]
        _ = _ := by rw [sumFin_ite_eq, add_zero]
  | some index =>
      calc
        _ = sumFin (fun position =>
            (if position = column then matrix row position *
              (if tail[column.val]'column.isLt = head then 1
               else point blocks (tail[column.val]'column.isLt) - point blocks head) else 0) +
            (if position = index then
              (if tail[column.val]'column.isLt ≠ head then matrix row position else 0) else 0)) := by
          apply sumFin_congr
          intro position
          rw [columnChange_at, previous, mul_add]
          have diagonal : matrix row position *
              (if position = column then
                (if tail[column.val]'column.isLt = head then 1
                 else point blocks (tail[column.val]'column.isLt) - point blocks head) else 0) =
              (if position = column then matrix row position *
                (if tail[column.val]'column.isLt = head then 1
                 else point blocks (tail[column.val]'column.isLt) - point blocks head) else 0) := by
            by_cases same : position = column
            · rw [if_pos same, if_pos same]
            · rw [if_neg same, if_neg same, mul_zero]
          have predecessorEntry : matrix row position *
              (if position = index ∧ tail[column.val]'column.isLt ≠ head then 1 else 0) =
              (if position = index then
                (if tail[column.val]'column.isLt ≠ head then matrix row position else 0) else 0) := by
            by_cases same : position = index
            · rw [if_pos same]
              by_cases different : tail[column.val]'column.isLt ≠ head
              · have selected : (position = index ∧ tail[column.val]'column.isLt ≠ head) := ⟨same, different⟩
                rw [if_pos selected, if_pos different, mul_one]
              · have absent : ¬(position = index ∧ tail[column.val]'column.isLt ≠ head) :=
                  fun both => different both.2
                rw [if_neg absent, if_neg different, mul_zero]
            · have absent : ¬(position = index ∧ tail[column.val]'column.isLt ≠ head) :=
                fun both => same both.1
              rw [if_neg same, if_neg absent, mul_zero]
          exact (congrArg (fun value => value + matrix row position *
            (if position = index ∧ tail[column.val]'column.isLt ≠ head then 1 else 0)) diagonal).trans
            (congrArg (fun value => _ + value) predecessorEntry)
        _ = _ := by rw [sumFin_add, sumFin_ite_eq, sumFin_ite_eq]

/-- Retain the same inverse root differences on the column-change diagonal. -/
@[expose] def columnInverses (blocks : List (Block K))
    (differences : SquareMatrix K blocks.length) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) : Vec K tail.length :=
  vectorOfFn fun index => if tail[index.val]'index.isLt = head then 1
    else differences (tail[index.val]'index.isLt) head

/-- The retained original root-difference units certify every column-change diagonal unit. -/
theorem columnChange_units (blocks : List (Block K))
    (differences : SquareMatrix K blocks.length)
    (units : ∀ first second : Fin blocks.length, first ≠ second →
      (point blocks first - point blocks second) * differences first second = 1)
    (head : Fin blocks.length) (tail : List (Fin blocks.length)) (occurrences : Occurrences tail)
    (index : Fin tail.length) :
    columnChange blocks head tail occurrences index index * columnInverses blocks differences head tail index = 1 := by
  rw [columnChange_diagonal, columnInverses, vectorOfFn_apply]
  by_cases same : tail[index.val]'index.isLt = head
  · rw [if_pos same, if_pos same, one_mul]
  · rw [if_neg same, if_neg same]
    exact units _ _ same

end Hermite

set_option genInjectivity false in
/-- A retained original confluent mode matrix and its actual scalar-one inverse.

The same original blocks, root-difference table and ordered word index the
construction. Occurrence metadata and the mode matrix are cached explicitly;
the original scaled-inverse certificate refers to that exact retained matrix.
-/
structure Hermite (blocks : List (Block K)) (differences : SquareMatrix K blocks.length)
    (word : List (Fin blocks.length)) where
  /-- The actual cached orders and original predecessor coordinates of the same word. -/
  occurrences : Occurrences word
  /-- The same original initial mode matrix, retained as structural square data. -/
  matrix : SquareMatrix K word.length
  /-- Every retained matrix entry uses the same original block scalar and occurrence order. -/
  matrix_spec : ∀ row column, matrix row column =
    entry (Hermite.point blocks (word[column.val]'column.isLt)) (occurrences.orders column) row.val
  /-- The original inverse record indexed by this exact retained matrix. -/
  inverse : ScaledInverse matrix
  /-- Its retained common scalar is one. -/
  inverse_scalar : inverse.scalar = 1

constructive_injectivity Hermite

namespace Hermite

/-- Taking the first root difference factors the original initial mode matrix through its retained tail.

The tail matrix and occurrence data are those of the original prepared word.
The column change consumes its same bounded predecessors and original root
scalars, including a zero root and repeated nonadjacent occurrences.
-/
theorem prepend_factorization (blocks : List (Block K))
    (differences : SquareMatrix K blocks.length) (head : Fin blocks.length)
    (tail : List (Fin blocks.length)) (retained : Hermite blocks differences tail) :
    let current := initial blocks (head :: tail) (Occurrences.prepend head retained.occurrences)
    Rectangular.mul (difference (point blocks head) (tail.length + 1)) current =
      Blocks.border 1 (Blocks.topRow current) (vectorOfFn fun _ => 0)
        (Rectangular.mul retained.matrix (columnChange blocks head tail retained.occurrences)) := by
  dsimp only
  apply Blocks.ext
  · rw [difference_mul_first, Blocks.border_zero_zero, initial_at]
    change entry (point blocks head) ((Occurrences.prepend head retained.occurrences).orders 0) 0 = 1
    rw [Occurrences.prepend_order_zero, entry_start]
  · intro column
    rw [difference_mul_first, Blocks.border_zero_succ, Blocks.topRow_apply]
  · intro row
    rw [difference_mul_succ, Blocks.border_succ_zero, vectorOfFn_apply, initial_at, initial_at]
    change entry (point blocks head) ((Occurrences.prepend head retained.occurrences).orders 0) (row.val + 1) -
      point blocks head *
        entry (point blocks head) ((Occurrences.prepend head retained.occurrences).orders 0) row.val = 0
    rw [Occurrences.prepend_order_zero, entry_difference_zero, sub_self, zero_mul]
  · intro row column
    rw [difference_mul_succ, Blocks.border_succ_succ, mul_columnChange, initial_at, initial_at]
    change entry (point blocks (tail[column.val]'column.isLt))
        ((Occurrences.prepend head retained.occurrences).orders column.succ) (row.val + 1) -
      point blocks head * entry (point blocks (tail[column.val]'column.isLt))
        ((Occurrences.prepend head retained.occurrences).orders column.succ) row.val = _
    rw [Occurrences.prepend_order_succ]
    by_cases same : head = tail[column.val]'column.isLt
    · have samePoint : point blocks head = point blocks (tail[column.val]'column.isLt) :=
        congrArg (point blocks) same
      rw [if_pos same, if_pos same.symm, samePoint, entry_difference_same]
      rw [retained.matrix_spec, mul_one]
      cases previous : retained.occurrences.predecessors column with
      | none => exact (add_zero _).symm
      | some index =>
          change _ = _ + (if tail[column.val]'column.isLt ≠ head then _ else 0)
          rw [if_neg (fun different => different same.symm), add_zero]
    · have different : tail[column.val]'column.isLt ≠ head := fun equal => same equal.symm
      rw [if_neg same, if_neg different]
      cases previous : retained.occurrences.predecessors column with
      | none =>
          have zeroOrder := retained.occurrences.none_zero column previous
          rw [zeroOrder, entry_difference_zero, retained.matrix_spec, zeroOrder, add_zero, mul_comm]
      | some index =>
          have facts := retained.occurrences.some_spec column index previous
          rw [facts.2.2, entry_difference_succ]
          change _ = retained.matrix row column *
            (point blocks (tail[column.val]'column.isLt) - point blocks head) +
            (if tail[column.val]'column.isLt ≠ head then retained.matrix row index else 0)
          rw [if_pos different, retained.matrix_spec, retained.matrix_spec, facts.2.1, facts.2.2]
          ring0

/-- Prepare the complete original confluent mode matrix and inverse by one tail recursion.

The same original tail preparation supplies the occurrence metadata, mode
matrix and inverse. One retained column change uses the cached difference
units; a unit leading border and first-order difference complete the inverse.
-/
@[expose] def prepare (blocks : List (Block K)) (differences : SquareMatrix K blocks.length)
    (units : ∀ first second : Fin blocks.length, first ≠ second →
      (point blocks first - point blocks second) * differences first second = 1) :
    (word : List (Fin blocks.length)) → Hermite blocks differences word
  | [] =>
      { occurrences := Occurrences.prepare []
        matrix := .nil
        matrix_spec := fun row => Fin.elim0 row
        inverse :=
          { scalar := 1
            inverse := .nil
            left_identity := by
              apply matrix_ext
              intro row
              exact Fin.elim0 row
            right_identity := by
              apply matrix_ext
              intro row
              exact Fin.elim0 row }
        inverse_scalar := rfl }
  | head :: tail => by
      let retained := prepare blocks differences units tail
      let occurrences := Occurrences.prepend head retained.occurrences
      let current := initial blocks (head :: tail) occurrences
      let columns := columnChange blocks head tail retained.occurrences
      let columnInverse := Triangular.inverseUpper columns
        (columnChange_upper blocks head tail retained.occurrences)
        (columnInverses blocks differences head tail)
        (columnChange_units blocks differences units head tail retained.occurrences)
      let tailInverse := retained.inverse.mul retained.inverse_scalar columnInverse.val columnInverse.property
      let top := Blocks.topRow current
      let transformed := Blocks.border 1 top (vectorOfFn fun _ => 0)
        (Rectangular.mul retained.matrix columns)
      let transformedInverse := Triangular.inverseUnitBorder top tailInverse (by rfl)
      let delta := difference (point blocks head) (tail.length + 1)
      have factorization : Rectangular.mul delta current = transformed :=
        prepend_factorization blocks differences head tail retained
      let deltaInverse := Triangular.inverseLower delta
        (difference_lower (point blocks head) (tail.length + 1))
        (vectorOfFn fun _ => 1) (by
          intro index
          rw [difference_diagonal, vectorOfFn_apply, one_mul])
      have deltaLeft : Rectangular.mul deltaInverse.val.inverse delta = Multiplication.scaleIdentity 1 :=
        deltaInverse.val.left_identity.trans (congrArg Multiplication.scaleIdentity deltaInverse.property)
      have recovered : current = Rectangular.mul deltaInverse.val.inverse transformed := by
        rw [← factorization, ← Rectangular.mul_assoc, deltaLeft, Rectangular.unit_mul]
      let actualInverse := Rectangular.mul transformedInverse.inverse delta
      have left : Rectangular.mul actualInverse current = Multiplication.scaleIdentity 1 := by
        change Rectangular.mul (Rectangular.mul transformedInverse.inverse delta) current = _
        rw [Rectangular.mul_assoc, factorization]
        exact transformedInverse.left_identity
      have transformedRight : Rectangular.mul transformed transformedInverse.inverse =
          Multiplication.scaleIdentity 1 := transformedInverse.right_identity
      have right : Rectangular.mul current actualInverse = Multiplication.scaleIdentity 1 := by
        change Rectangular.mul current (Rectangular.mul transformedInverse.inverse delta) = _
        rw [recovered, Rectangular.mul_assoc,
          ← Rectangular.mul_assoc transformed transformedInverse.inverse delta,
          transformedRight, Rectangular.unit_mul]
        exact deltaLeft
      exact
        { occurrences := occurrences
          matrix := current
          matrix_spec := initial_at blocks (head :: tail) occurrences
          inverse := { scalar := 1, inverse := actualInverse, left_identity := left, right_identity := right }
          inverse_scalar := rfl }

/-- Read an original mode row, retaining its prepared initial row whenever it is available.

An index below the original word length returns the same stored structural
row. Later indices alone invoke the original generalized-mode row producer.
-/
@[expose] def readRow {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (index : Nat) :
    Vec K word.length :=
  if earlier : index < word.length then basis.matrix ⟨index, earlier⟩
  else row blocks word basis.occurrences index

/-- Every original row reading has the same root and retained occurrence order. -/
theorem readRow_at {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (index : Nat)
    (column : Fin word.length) : basis.readRow index column =
      entry (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column) index := by
  rewrite [readRow]
  by_cases earlier : index < word.length
  · rewrite [dif_pos earlier]
    exact basis.matrix_spec _ column
  · rewrite [dif_neg earlier, row_at]
    rfl

/-- Retain a finite mode horizon through the same original row selector.

The selector returns already prepared initial rows directly and computes
only later rows with the original generalized-mode producer.
-/
@[expose] def horizon {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (count : Nat) :
    Rectangular K count word.length := vectorOfFn fun index => basis.readRow index.val

/-- Retain only the requested consecutive original rows after the supplied finite start.

The same row selector preserves every available initial cache. No unused
prefix before the requested start is allocated or evaluated.
-/
@[expose] def horizonFrom {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (start count : Nat) :
    Rectangular K count word.length := vectorOfFn fun index => basis.readRow (start + index.val)

/-- A retained consecutive horizon reads the same original mode at its shifted natural index. -/
theorem horizonFrom_at {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (start count : Nat)
    (index : Fin count) (column : Fin word.length) : basis.horizonFrom start count index column =
      entry (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column) (start + index.val) := by
  rewrite [horizonFrom, vectorOfFn_apply, readRow_at]
  rfl

/-- A consecutive horizon starting at zero preserves the complete original horizon. -/
theorem horizonFrom_zero {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (count : Nat) :
    basis.horizonFrom 0 count = basis.horizon count := by
  apply vector_ext
  intro index
  rewrite [horizonFrom, horizon, vectorOfFn_apply, vectorOfFn_apply, Nat.zero_add]
  rfl

/-- Every retained horizon entry reads the same original mode at its finite coordinate. -/
theorem horizon_at {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) (count : Nat)
    (index : Fin count) (column : Fin word.length) :
    basis.horizon count index column =
      entry (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column) index.val := by
  rewrite [horizon, vectorOfFn_apply, readRow_at]
  rfl

/-- An initial horizon is exactly the same retained original matrix. -/
theorem horizon_initial {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word) :
    basis.horizon word.length = basis.matrix := by
  apply vector_ext
  intro index
  rw [horizon, vectorOfFn_apply, readRow, dif_pos index.isLt]

/-- Restricting a prepared concatenation preserves the exact original prefix mode entries. -/
theorem horizon_prefix {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    (first second : List (Fin blocks.length)) (basis : Hermite blocks differences (first ++ second))
    (count : Nat) (index : Fin count) (column : Fin first.length)
    (bound : column.val < (first ++ second).length) :
    basis.horizon count index ⟨column.val, bound⟩ =
      row blocks first (basis.occurrences.take first second) index.val column := by
  rw [horizon_at, row_at, Occurrences.take_order,
    Append.getElem_append_left first second column.val column.isLt]

/-- Extract the unique original mode coefficients from an initial coordinate vector. -/
@[expose] def coordinates {blocks : List (Block K)}
    {differences : SquareMatrix K blocks.length} {word : List (Fin blocks.length)}
    (basis : Hermite blocks differences word) (values : Vec K word.length) : Vec K word.length :=
  Rectangular.apply basis.inverse.inverse values

/-- The retained mode coefficients reconstruct every original initial coordinate. -/
theorem reconstruct {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word)
    (values : Vec K word.length) : Rectangular.apply basis.matrix (basis.coordinates values) = values := by
  change Rectangular.apply basis.matrix (Rectangular.apply basis.inverse.inverse values) = values
  rw [← Rectangular.apply_mul]
  have identity : Rectangular.mul basis.matrix basis.inverse.inverse = Multiplication.scaleIdentity 1 :=
    basis.inverse.right_identity.trans (congrArg Multiplication.scaleIdentity basis.inverse_scalar)
  rw [identity, Rectangular.apply_unit]

/-- Reconstructing and reading coordinates preserves the complete original coefficient vector. -/
theorem coordinates_apply {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word)
    (coefficients : Vec K word.length) : basis.coordinates (Rectangular.apply basis.matrix coefficients) =
      coefficients := by
  change Rectangular.apply basis.inverse.inverse (Rectangular.apply basis.matrix coefficients) = coefficients
  rw [← Rectangular.apply_mul]
  have identity : Rectangular.mul basis.inverse.inverse basis.matrix = Multiplication.scaleIdentity 1 :=
    basis.inverse.left_identity.trans (congrArg Multiplication.scaleIdentity basis.inverse_scalar)
  rw [identity, Rectangular.apply_unit]

/-- Equal original initial mode combinations have equal complete coefficient vectors. -/
theorem independent {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
    {word : List (Fin blocks.length)} (basis : Hermite blocks differences word)
    (first second : Vec K word.length)
    (equal : Rectangular.apply basis.matrix first = Rectangular.apply basis.matrix second) : first = second :=
  (basis.coordinates_apply first).symm.trans
    ((congrArg basis.coordinates equal).trans (basis.coordinates_apply second))

/-- Construct the original polynomial bank's entire degree-sized confluent basis automatically.

The actual expanded word repeats each original block exactly its retained
multiplicity. The bank's same root-difference inverse table supplies all units;
no separate final mode table or inverse certificate is requested.
-/
@[expose] def ofBank [DecidableEq K] {polynomial : Dense.Basic.DensePolynomial K}
    (bank : Bank polynomial) :
    Hermite bank.blocks bank.differenceInverses (Word.expand bank.blocks) :=
  prepare bank.blocks bank.differenceInverses bank.difference_unit (Word.expand bank.blocks)

/-- The automatic original bank basis has exactly the original source-polynomial degree. -/
theorem ofBank_count [DecidableEq K] {polynomial : Dense.Basic.DensePolynomial K} (bank : Bank polynomial) :
    (Word.expand bank.blocks).length = polynomial.natDegree :=
  (Word.length_expand bank.blocks).trans bank.count_eq

/-- Every automatic original bank mode has an order below its retained block multiplicity. -/
theorem ofBank_order_lt [DecidableEq K] {polynomial : Dense.Basic.DensePolynomial K}
    (bank : Bank polynomial) (index : Fin (Word.expand bank.blocks).length) :
    let original := (Word.expand bank.blocks)[index.val]'index.isLt
    (ofBank bank).occurrences.orders index < (bank.blocks[original.val]'original.isLt).multiplicity :=
  Word.order_lt bank.blocks (ofBank bank).occurrences index

end Hermite

end Purelib.Polynomial.Recurrence.Mode
