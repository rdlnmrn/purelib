module

public import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift
public import Purelib.Polynomial.Recurrence.Mode.Roots
import Purelib.Data.Vector.Split
import Purelib.Algebra.FiniteSum.Fin

/-!
# Complete finite recurrence coordinates in the original mode basis

The same retained Hermite inverse extracts initial coordinates. Its original
mode horizons satisfy the source recurrence, reconstruct every supplied finite
solution, and determine their complete coefficient vectors uniquely.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K]
variable {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
variable {word : List (Fin blocks.length)}

/-- Each retained horizon column is exactly its original finite generalized-mode window. -/
theorem horizon_column (basis : Hermite blocks differences word) (count : Nat) (column : Fin word.length) :
    Rectangular.column (basis.horizon count) column =
      window (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column) count := by
  apply vector_ext
  intro index
  rw [Rectangular.column_at, horizon_at, window_at]

/-- An original initial horizon row reuses the same retained initial-matrix row. -/
theorem horizon_initial_row (basis : Hermite blocks differences word) (count : Nat)
    (index : Fin count) (bound : index.val < word.length) (column : Fin word.length) :
    basis.horizon count index column = basis.matrix ⟨index.val, bound⟩ column := by
  rw [horizon, vectorOfFn_apply, readRow, dif_pos bound]

/-- Consecutive original mode rows are the same initial horizon followed by the canonical finite shift power.

The original transition needs no root inverse. Both the cached initial rows
and the requested late rows belong to this same original basis, including
zero-root transients and interleaved repeated roots.
-/
theorem horizonFrom_eq_mul (basis : Hermite blocks differences word) (start count : Nat) :
    basis.horizonFrom start count = Rectangular.mul (basis.horizon count)
      (Arithmetic.power (Shift.transition (point blocks) word basis.occurrences) start) := by
  apply Rectangular.ext
  intro index column
  rewrite [horizonFrom_at, Rectangular.mul_at]
  calc
    _ = entry (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column)
        (index.val + start) := congrArg
          (entry (point blocks (word[column.val]'column.isLt)) (basis.occurrences.orders column))
            (Nat.add_comm start index.val)
    _ = sumFin (fun middle =>
        entry (point blocks (word[middle.val]'middle.isLt)) (basis.occurrences.orders middle) index.val *
          Arithmetic.power (Shift.transition (point blocks) word basis.occurrences) start middle column) :=
      (Shift.row_power (point blocks) word basis.occurrences index.val start column).symm
    _ = _ := by
      apply sumFin_congr
      intro middle
      rewrite [horizon_at]
      rfl

/-- The same original initial inverse extracts the canonically shifted coefficients from a complete late window.

The window contains exactly the original basis dimension consecutive
readings. It uses no preceding horizon allocation, root inverse, geometric
reading or assumption that nonzero formal coefficients remain nonzero.
-/
theorem coordinates_horizonFrom (basis : Hermite blocks differences word) (start : Nat)
    (coefficients : Vec K word.length) :
    basis.coordinates (Rectangular.apply (basis.horizonFrom start word.length) coefficients) =
      Rectangular.apply (Arithmetic.power (Shift.transition (point blocks) word basis.occurrences) start)
        coefficients := by
  rewrite [horizonFrom_eq_mul, horizon_initial, Rectangular.apply_mul]
  exact basis.coordinates_apply _

/-- A complete retained initial segment determines every coefficient in an original finite mode combination. -/
theorem horizon_independent (basis : Hermite blocks differences word) (count : Nat)
    (enough : word.length ≤ count) (first second : Vec K word.length)
    (equal : Rectangular.apply (basis.horizon count) first = Rectangular.apply (basis.horizon count) second) :
    first = second := by
  apply basis.independent first second
  apply vector_ext
  intro index
  have retained := vector_eq_at equal ⟨index.val, Nat.lt_of_lt_of_le index.isLt enough⟩
  rw [Rectangular.apply_at, Rectangular.apply_at] at retained
  have firstRow : sumFin (fun column => basis.horizon count
        ⟨index.val, Nat.lt_of_lt_of_le index.isLt enough⟩ column * first column) =
      Rectangular.apply basis.matrix first index := by
    rw [Rectangular.apply_at]
    apply sumFin_congr
    intro column
    rw [horizon_initial_row basis count _ index.isLt]
  have secondRow : sumFin (fun column => basis.horizon count
        ⟨index.val, Nat.lt_of_lt_of_le index.isLt enough⟩ column * second column) =
      Rectangular.apply basis.matrix second index := by
    rw [Rectangular.apply_at]
    apply sumFin_congr
    intro column
    rw [horizon_initial_row basis count _ index.isLt]
  exact firstRow.symm.trans (retained.trans secondRow)

/-- Extract original mode coordinates from any supplied finite horizon.

A complete initial horizon uses the original prefix and inverse unchanged.
A shorter horizon joins that same retained prefix with zero initial entries,
then applies the same original full inverse. No recurrence extension or new
basis is computed.
-/
@[expose] def coordinatesOfHorizon (basis : Hermite blocks differences word) {count : Nat}
    (values : Vec K count) : Vec K word.length :=
  if enough : word.length ≤ count then basis.coordinates (Split.take enough values)
  else basis.coordinates (Split.join (Nat.le_of_lt (Nat.lt_of_not_ge enough)) values (vectorOfFn fun _ => 0))

/-- A complete initial horizon preserves exactly the original prefix-coordinate operation. -/
theorem coordinatesOfHorizon_of_le (basis : Hermite blocks differences word) {count : Nat}
    (values : Vec K count) (enough : word.length ≤ count) :
    basis.coordinatesOfHorizon values = basis.coordinates (Split.take enough values) := by
  rewrite [coordinatesOfHorizon, dif_pos enough]
  rfl

variable [DecidableEq K] {polynomial : DensePolynomial K}

/-- Every finite combination of displayed bank modes satisfies the original source recurrence. -/
theorem horizon_satisfies (bank : Bank polynomial) (companion : Companion polynomial)
    {word : List (Fin bank.blocks.length)} (basis : Hermite bank.blocks bank.differenceInverses word)
    (orders : ∀ column : Fin word.length,
      basis.occurrences.orders column < (bank.block (word[column.val]'column.isLt)).multiplicity)
    (count : Nat) (coefficients : Vec K word.length) :
    companion.Satisfies (Rectangular.apply (basis.horizon count) coefficients) := by
  apply companion.satisfies_apply
  intro column
  rw [horizon_column]
  exact bank_window_satisfies bank companion (word[column.val]'column.isLt)
    (basis.occurrences.orders column) (orders column) count

/-- The original retained initial inverse reconstructs every finite source-recurrence solution.

The displayed word exhausts the original source degree, and each occurrence
stays within its original root block. Only complete recurrence rows inside the
supplied horizon are used; no completed trajectory or later reading is assumed.
-/
theorem horizon_reconstruct (bank : Bank polynomial) (companion : Companion polynomial)
    {word : List (Fin bank.blocks.length)} (basis : Hermite bank.blocks bank.differenceInverses word)
    (size : word.length = polynomial.natDegree)
    (orders : ∀ column : Fin word.length,
      basis.occurrences.orders column < (bank.block (word[column.val]'column.isLt)).multiplicity)
    {count : Nat} (values : Vec K count) (enough : word.length ≤ count)
    (equations : companion.Satisfies values) :
    Rectangular.apply (basis.horizon count) (basis.coordinates (Split.take enough values)) = values := by
  have degreeBound : polynomial.natDegree ≤ count := size ▸ enough
  let state := Split.take degreeBound values
  let coefficients := basis.coordinates (Split.take enough values)
  let produced := Rectangular.apply (basis.horizon count) coefficients
  have original : values = companion.window state count := by
    apply companion.window_unique state values degreeBound
    · intro column
      exact (Split.take_apply degreeBound values column).symm
    · exact equations
  have producedInitial : ∀ column : Fin polynomial.natDegree,
      produced ⟨column.val, Nat.lt_of_lt_of_le column.isLt degreeBound⟩ = state column := by
    intro column
    have columnBound : column.val < word.length := size.symm ▸ column.isLt
    let originalColumn : Fin word.length := ⟨column.val, columnBound⟩
    have reconstructed := vector_eq_at (basis.reconstruct (Split.take enough values)) originalColumn
    change Rectangular.apply (basis.horizon count) coefficients
      ⟨column.val, Nat.lt_of_lt_of_le column.isLt degreeBound⟩ = _
    rw [Rectangular.apply_at]
    have initialRow : sumFin (fun index => basis.horizon count
          ⟨column.val, Nat.lt_of_lt_of_le column.isLt degreeBound⟩ index * coefficients index) =
        Rectangular.apply basis.matrix coefficients originalColumn := by
      rw [Rectangular.apply_at]
      apply sumFin_congr
      intro index
      rw [horizon_initial_row basis count _ columnBound]
    rw [initialRow]
    change Rectangular.apply basis.matrix (basis.coordinates (Split.take enough values)) originalColumn = _
    rw [reconstructed, Split.take_apply, Split.take_apply]
  have canonical : produced = companion.window state count :=
    companion.window_unique state produced degreeBound producedInitial
      (horizon_satisfies bank companion basis orders count coefficients)
  exact canonical.trans original.symm

/-- The same original full inverse reconstructs every supplied finite source-recurrence horizon.

Complete initial horizons use the original recurrence-uniqueness theorem.
Shorter horizons need only the corresponding rows of the same original
initial inverse; zero-padded unused initial coordinates choose one finite
extension without asserting unique coordinates for a shorter prefix.
-/
theorem horizon_reconstruct_any (bank : Bank polynomial) (companion : Companion polynomial)
    {word : List (Fin bank.blocks.length)} (basis : Hermite bank.blocks bank.differenceInverses word)
    (size : word.length = polynomial.natDegree)
    (orders : ∀ column : Fin word.length,
      basis.occurrences.orders column < (bank.block (word[column.val]'column.isLt)).multiplicity)
    {count : Nat} (values : Vec K count) (equations : companion.Satisfies values) :
    Rectangular.apply (basis.horizon count) (basis.coordinatesOfHorizon values) = values := by
  by_cases enough : word.length ≤ count
  · rewrite [coordinatesOfHorizon_of_le basis values enough]
    exact horizon_reconstruct bank companion basis size orders values enough equations
  · let bound := Nat.le_of_lt (Nat.lt_of_not_ge enough)
    let padded := Split.join bound values (vectorOfFn fun _ => (0 : K))
    rewrite [coordinatesOfHorizon, dif_neg enough]
    apply vector_ext
    intro index
    have initialBound : index.val < word.length := Nat.lt_of_lt_of_le index.isLt bound
    let original : Fin word.length := ⟨index.val, initialBound⟩
    have reconstructed := vector_eq_at (basis.reconstruct padded) original
    rewrite [Rectangular.apply_at] at reconstructed
    rewrite [Rectangular.apply_at]
    calc
      _ = sumFin (fun column => basis.matrix original column * basis.coordinates padded column) := by
        apply sumFin_congr
        intro column
        rewrite [horizon_initial_row basis count index initialBound]
        rfl
      _ = padded original := reconstructed
      _ = values index := Split.join_apply_take bound values (vectorOfFn fun _ => (0 : K)) index

/-- The automatic original bank basis reconstructs every supplied complete finite recurrence solution. -/
theorem ofBank_horizon_reconstruct (bank : Bank polynomial) (companion : Companion polynomial)
    {count : Nat} (values : Vec K count) (enough : (Word.expand bank.blocks).length ≤ count)
    (equations : companion.Satisfies values) :
    Rectangular.apply ((ofBank bank).horizon count)
      ((ofBank bank).coordinates (Split.take enough values)) = values :=
  horizon_reconstruct bank companion (ofBank bank) (ofBank_count bank) (ofBank_order_lt bank)
    values enough equations

end Purelib.Polynomial.Recurrence.Mode.Hermite

end
