module

public import Purelib.Polynomial.Recurrence.Mode.Hermite
public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained shifts of original confluent modes

The same original root supplies each diagonal entry. Its retained immediately
preceding occurrence supplies the unit predecessor entry. Root units permit
one actual upper-triangular inverse; zero-root shifts are not assumed invertible.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List (Occurrences)
open Purelib.Polynomial.Dense.Roots
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K]
variable {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
variable {word : List (Fin blocks.length)} {occurrences : Occurrences word}

namespace Shift

variable {Tag : Type*} [DecidableEq Tag]

/-- Construct the original mode shift from the same retained roots and bounded predecessors. -/
@[expose] def transition (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) : SquareMatrix K word.length :=
  matrixOfFn fun row column => if row = column then roots (word[column.val]'column.isLt)
    else match occurrences.predecessors column with
      | none => 0
      | some previous => if row = previous then 1 else 0

/-- Every original mode-shift diagonal reads its same original root. -/
theorem transition_diagonal (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) (index : Fin word.length) :
    transition roots word occurrences index index = roots (word[index.val]'index.isLt) := by
  rw [transition, matrixOfFn_apply, if_pos rfl]

/-- The original mode shift is upper triangular through its same retained predecessor bounds. -/
theorem transition_upper (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) : Triangular.IsUpper (transition roots word occurrences) := by
  intro row column before
  rw [transition, matrixOfFn_apply]
  have different : row ≠ column := by
    intro equal
    have values := congrArg Fin.val equal
    omega0
  rw [if_neg different]
  cases previous : occurrences.predecessors column with
  | none => rfl
  | some prior =>
      have facts := occurrences.some_spec column prior previous
      have distinct : row ≠ prior := by
        intro equal
        have values := congrArg Fin.val equal
        have earlier := facts.1
        omega0
      change (if row = prior then (1 : K) else 0) = 0
      exact if_neg distinct

/-- The original shift is the sum of its same root diagonal and cached predecessor entries. -/
theorem transition_at (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) (row column : Fin word.length) :
    transition roots word occurrences row column =
      (if row = column then roots (word[column.val]'column.isLt) else 0) +
      (match occurrences.predecessors column with
       | none => 0
       | some previous => if row = previous then 1 else 0) := by
  rw [transition, matrixOfFn_apply]
  by_cases same : row = column
  · cases same
    rw [if_pos rfl, if_pos rfl]
    cases previous : occurrences.predecessors row with
    | none => exact (add_zero _).symm
    | some prior =>
        have facts := occurrences.some_spec row prior previous
        have different : row ≠ prior := by
          intro equal
          have values := congrArg Fin.val equal
          have before := facts.1
          omega0
        change _ = _ + (if row = prior then (1 : K) else 0)
        rw [if_neg different, add_zero]
  · rw [if_neg same, if_neg same, zero_add]

/-- Reading the original transition requires only its same cached root readings and exact zero and one.

The coefficient reading need not preserve general multiplication. The
original word and predecessor table are unchanged; a retained target root
lookup determines every target diagonal without allocating mapped blocks
or a second occurrence cache.
-/
theorem map_transition_at {L : Type*} [CommRing L] (function : K → L)
    (mapZero : function 0 = 0) (mapOne : function 1 = 1) (roots : Tag → K) (observedRoots : Tag → L)
    (root_eq : ∀ tag, function (roots tag) = observedRoots tag) (word : List Tag)
    (occurrences : Occurrences word) (row column : Fin word.length) :
    function (transition roots word occurrences row column) = transition observedRoots word occurrences row column := by
  rewrite [transition, matrixOfFn_apply, transition, matrixOfFn_apply]
  by_cases same : row = column
  · rewrite [if_pos same, if_pos same]
    exact root_eq _
  · rewrite [if_neg same, if_neg same]
    cases previous : occurrences.predecessors column with
    | none => exact mapZero
    | some prior =>
        change function (if row = prior then 1 else 0) = if row = prior then 1 else 0
        by_cases predecessor : row = prior
        · rewrite [if_pos predecessor, if_pos predecessor]
          exact mapOne
        · rewrite [if_neg predecessor, if_neg predecessor]
          exact mapZero

/-- The actual mode shift combines the original same column and its retained predecessor column. -/
theorem mul_transition (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) {rows : Nat}
    (matrix : Rectangular K rows word.length) (row : Fin rows) (column : Fin word.length) :
    Rectangular.mul matrix (transition roots word occurrences) row column =
      matrix row column * roots (word[column.val]'column.isLt) +
      (match occurrences.predecessors column with
       | none => 0
       | some previous => matrix row previous) := by
  rw [Rectangular.mul_at]
  cases previous : occurrences.predecessors column with
  | none =>
      calc
        _ = sumFin (fun index => if index = column then
            matrix row index * roots (word[column.val]'column.isLt) else 0) := by
          apply sumFin_congr
          intro index
          rw [transition_at, previous]
          change matrix row index * ((if index = column then _ else 0) + 0) = _
          rw [add_zero]
          by_cases same : index = column
          · rw [if_pos same, if_pos same]
          · rw [if_neg same, if_neg same, mul_zero]
        _ = _ := by rw [sumFin_ite_eq, add_zero]
  | some prior =>
      calc
        _ = sumFin (fun index =>
            (if index = column then matrix row index * roots (word[column.val]'column.isLt) else 0) +
            (if index = prior then matrix row index else 0)) := by
          apply sumFin_congr
          intro index
          rw [transition_at, previous]
          change matrix row index * ((if index = column then _ else 0) +
            (if index = prior then 1 else 0)) = _
          rw [mul_add]
          have diagonal : matrix row index *
              (if index = column then roots (word[column.val]'column.isLt) else 0) =
              (if index = column then matrix row index * roots (word[column.val]'column.isLt) else 0) := by
            by_cases same : index = column
            · rw [if_pos same, if_pos same]
            · rw [if_neg same, if_neg same, mul_zero]
          have predecessor : matrix row index * (if index = prior then 1 else 0) =
              (if index = prior then matrix row index else 0) := by
            by_cases same : index = prior
            · rw [if_pos same, if_pos same, mul_one]
            · rw [if_neg same, if_neg same, mul_zero]
          exact (congrArg (fun value => value + matrix row index * (if index = prior then 1 else 0))
            diagonal).trans (congrArg (fun value => _ + value) predecessor)
        _ = _ := by rw [sumFin_add, sumFin_ite_eq, sumFin_ite_eq]

end Shift

set_option genInjectivity false in
/-- An actual original mode-shift matrix and its retained scalar-one inverse.

The original word and its retained cache fix the roots, occurrence orders
and bounded predecessors. Its shift is materialized once and passed unchanged to the
original upper-triangular inverse constructor.
-/
structure Shift (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) where
  /-- The actual retained original mode-shift matrix. -/
  matrix : SquareMatrix K word.length
  /-- The complete retained matrix is the same canonical original shift. -/
  matrix_eq : matrix = Shift.transition (point blocks) word occurrences
  /-- The original inverse record refers to that exact retained matrix. -/
  inverse : ScaledInverse matrix
  /-- The retained common inverse scalar is one. -/
  inverse_scalar : inverse.scalar = 1

constructive_injectivity Shift

namespace Shift

variable {Tag : Type*} [DecidableEq Tag]

/-- Prepare one original mode-shift matrix and inverse from its same root-unit table. -/
@[expose] def prepare (blocks : List (Block K)) (word : List (Fin blocks.length))
    (occurrences : Occurrences word) (rootInverses : Vec K word.length)
    (units : ∀ index, point blocks (word[index.val]'index.isLt) * rootInverses index = 1) :
    Shift blocks word occurrences := by
  let matrix := transition (point blocks) word occurrences
  let inverse := Triangular.inverseUpper matrix (transition_upper (point blocks) word occurrences) rootInverses (by
    intro index
    rw [transition_diagonal]
    exact units index)
  exact { matrix := matrix, matrix_eq := rfl, inverse := inverse.val, inverse_scalar := inverse.property }

/-- Every finite original mode row advances by the same retained original shift.

Only the original word, cached occurrence orders and bounded predecessors
enter the identity. No original-word Hermite inverse is required.
-/
theorem row_step (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) (index : Nat) (column : Fin word.length) :
    sumFin (fun position =>
      entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) index *
        (transition roots word occurrences) position column) =
      entry (roots (word[column.val]'column.isLt)) (occurrences.orders column) (index + 1) := by
  let single : Rectangular K 1 word.length := Rectangular.ofFn fun _ position =>
    entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) index
  calc
    _ = Rectangular.mul single (transition roots word occurrences) 0 column := by
      rw [Rectangular.mul_at]
      apply sumFin_congr
      intro position
      rewrite [Rectangular.ofFn_apply]
      rfl
    _ = single 0 column * roots (word[column.val]'column.isLt) +
        (match occurrences.predecessors column with
         | none => 0
         | some prior => single 0 prior) := by
      exact mul_transition roots word occurrences single 0 column
    _ = _ := by
      rewrite [Rectangular.ofFn_apply]
      cases previous : occurrences.predecessors column with
      | none =>
          have zero := occurrences.none_zero column previous
          change entry (roots (word[column.val]'column.isLt)) (occurrences.orders column) index *
              roots (word[column.val]'column.isLt) + 0 = _
          rw [zero, entry_succ_zero, add_zero, mul_comm]
      | some prior =>
          have facts := occurrences.some_spec column prior previous
          change _ + single 0 prior = _
          rewrite [Rectangular.ofFn_apply, facts.2.1, facts.2.2, entry_succ]
          ring0

/-- Every finite power of the original mode transition advances the same original mode row.

The canonical transition uses only retained occurrence predecessors. Its
natural powers and this identity require no inverse for any original root,
including zero roots and repeated occurrences.
-/
theorem row_power (roots : Tag → K) (word : List Tag)
    (occurrences : Occurrences word) (start steps : Nat) (column : Fin word.length) :
    sumFin (fun position =>
      entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) start *
        Arithmetic.power (transition roots word occurrences) steps position column) =
      entry (roots (word[column.val]'column.isLt)) (occurrences.orders column) (start + steps) := by
  induction steps generalizing column with
  | zero =>
      calc
        _ = sumFin (fun position => if position = column then
            entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) start else 0) := by
          apply sumFin_congr
          intro position
          rewrite [Arithmetic.power_zero, Multiplication.scaleIdentity_apply]
          by_cases same : position = column
          · rewrite [if_pos same, if_pos same, mul_one]
            rfl
          · rewrite [if_neg same, if_neg same, mul_zero]
            rfl
        _ = _ := by rewrite [sumFin_ite_eq, Nat.add_zero]; rfl
  | succ steps previous =>
      calc
        _ = sumFin (fun position => sumFin (fun middle =>
            (entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) start *
              Arithmetic.power (transition roots word occurrences) steps position middle) *
                transition roots word occurrences middle column)) := by
          apply sumFin_congr
          intro position
          rewrite [Arithmetic.power_succ, Multiplication.mul_apply, ← sumFin_mul_left]
          apply sumFin_congr
          intro middle
          exact (mul_assoc _ _ _).symm
        _ = sumFin (fun middle => sumFin (fun position =>
            (entry (roots (word[position.val]'position.isLt)) (occurrences.orders position) start *
              Arithmetic.power (transition roots word occurrences) steps position middle) *
                transition roots word occurrences middle column)) := sumFin_swap _
        _ = sumFin (fun middle =>
            entry (roots (word[middle.val]'middle.isLt)) (occurrences.orders middle) (start + steps) *
              transition roots word occurrences middle column) := by
          apply sumFin_congr
          intro middle
          rewrite [sumFin_mul_right, previous]
          rfl
        _ = entry (roots (word[column.val]'column.isLt)) (occurrences.orders column) (start + steps + 1) :=
          row_step roots word occurrences (start + steps) column
        _ = _ := congrArg (entry (roots (word[column.val]'column.isLt)) (occurrences.orders column))
          (Nat.add_assoc start steps 1)

/-- Every finite retained basis horizon consumes that same original shift matrix. -/
theorem horizon_step (basis : Hermite blocks differences word)
    (shift : Shift blocks word basis.occurrences) (count : Nat)
    (index : Fin count) (column : Fin word.length) :
    Rectangular.mul (basis.horizon (count + 1)) shift.matrix index.castSucc column =
      basis.horizon (count + 1) index.succ column := by
  rw [Rectangular.mul_at]
  calc
    _ = sumFin (fun position =>
        entry (point blocks (word[position.val]'position.isLt)) (basis.occurrences.orders position) index.val *
          shift.matrix position column) := by
      apply sumFin_congr
      intro position
      rw [horizon_at]
      rfl
    _ = entry (point blocks (word[column.val]'column.isLt))
        (basis.occurrences.orders column) (index.val + 1) := by
      rewrite [shift.matrix_eq]
      exact row_step (point blocks) word basis.occurrences index.val column
    _ = _ := (basis.horizon_at (count + 1) index.succ column).symm

end Shift
end Purelib.Polynomial.Recurrence.Mode.Hermite
