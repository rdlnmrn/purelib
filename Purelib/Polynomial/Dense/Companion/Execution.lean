module

public import Purelib.Polynomial.Dense.Companion
import Purelib.Data.Vector.Basic
import Purelib.Data.List.GetD
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Rectangular
public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Finite execution of the original cached companion

Every transition consumes the same retained matrix. Finite horizons and
bounded transition paths have exact readbacks and uniqueness; no completed
trajectory is introduced.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Purelib
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix → Mat

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

/-- Apply the original retained companion matrix to the original finite state. -/
@[expose] def step (companion : Companion polynomial) (state : Vec K polynomial.natDegree) :
    Vec K polynomial.natDegree := Mat.Multiplication.matrixVector companion.matrix state

/-- A companion step reads its original shift row or its same cached feedback row. -/
theorem step_at (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (row : Fin polynomial.natDegree) :
    companion.step state row =
      if next : row.val + 1 < polynomial.natDegree then state ⟨row.val + 1, next⟩
      else Fin.sumFin (fun column => companion.feedback column * state column) := by
  rw [step, companion.matrix_eq, Mat.Multiplication.matrixVector_apply]
  by_cases next : row.val + 1 < polynomial.natDegree
  · rw [dif_pos next]
    let target : Fin polynomial.natDegree := ⟨row.val + 1, next⟩
    have terms : Fin.sumFin (fun column => matrixOfFeedback companion.feedback row column * state column) =
        Fin.sumFin (fun column => if column = target then state column else 0) := by
      apply Fin.sumFin_congr
      intro column
      rw [matrixOfFeedback, Mat.matrixOfFn_apply, dif_pos next]
      change (if column = target then 1 else 0) * state column = _
      split
      · rw [one_mul]
      · rw [zero_mul]
    exact terms.trans (Fin.sumFin_ite_eq target state)
  · rw [dif_neg next]
    apply Fin.sumFin_congr
    intro column
    rw [matrixOfFeedback, Mat.matrixOfFn_apply, dif_neg next]

/-- A nonfinal original companion row reads its next original state coordinate. -/
theorem step_shift (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (row : Fin polynomial.natDegree) (next : row.val + 1 < polynomial.natDegree) :
    companion.step state row = state ⟨row.val + 1, next⟩ := by
  rw [step_at, dif_pos next]

/-- Retain the last original bounded state coordinate. -/
@[expose] def lastIndex (companion : Companion polynomial) : Fin polynomial.natDegree :=
  ⟨polynomial.natDegree - 1, by have positive := companion.positive; omega0⟩

/-- The last row is exactly the original cached feedback sum. -/
theorem step_last (companion : Companion polynomial) (state : Vec K polynomial.natDegree) :
    companion.step state companion.lastIndex =
      Fin.sumFin (fun column => companion.feedback column * state column) := by
  have terminal : ¬ companion.lastIndex.val + 1 < polynomial.natDegree := by
    have positive := companion.positive
    change ¬ polynomial.natDegree - 1 + 1 < polynomial.natDegree
    omega0
  rw [step_at, dif_neg terminal]

/-- The original next reading satisfies the retained coefficient equation. -/
theorem step_equation (companion : Companion polynomial) (state : Vec K polynomial.natDegree) :
    Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * state column) +
      polynomial.leadingCoeff * companion.step state companion.lastIndex = 0 := by
  rw [step_last]
  have feedback : Fin.sumFin (fun column : Fin polynomial.natDegree =>
        companion.feedback column * state column) =
      Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * state column) * -companion.leadingInverse := by
    rw [← Fin.sumFin_mul_right]
    apply Fin.sumFin_congr
    intro column
    rw [companion.feedback_eq]
    ring0
  rw [feedback]
  have cancelled := companion.leading_unit
  calc
    _ = (1 - polynomial.leadingCoeff * companion.leadingInverse) *
        Fin.sumFin (fun column : Fin polynomial.natDegree =>
          getD companion.coefficients column.val 0 * state column) := by ring0
    _ = 0 := by rw [cancelled, sub_self, zero_mul]

/-- Iterate the same original companion transition a supplied finite number of times. -/
@[expose] def advance (companion : Companion polynomial) :
    Nat → Vec K polynomial.natDegree → Vec K polynomial.natDegree
  | 0, state => state
  | count + 1, state => companion.step (companion.advance count state)

/-- Zero transitions retain the complete original state. -/
theorem advance_zero (companion : Companion polynomial) (state : Vec K polynomial.natDegree) :
    companion.advance 0 state = state := rfl

/-- A successor transition count appends one original cached-matrix action. -/
theorem advance_succ (companion : Companion polynomial) (count : Nat)
    (state : Vec K polynomial.natDegree) :
    companion.advance (count + 1) state = companion.step (companion.advance count state) := rfl

/-- Two finite transition requests compose with their complete intermediate state. -/
theorem advance_add (companion : Companion polynomial) (first second : Nat)
    (state : Vec K polynomial.natDegree) :
    companion.advance (first + second) state =
      companion.advance second (companion.advance first state) := by
  induction second with
  | zero => rfl
  | succ second previous => exact congrArg companion.step previous

/-- A finite transition count can execute its first step before the remaining count. -/
theorem advance_succ_first (companion : Companion polynomial) (count : Nat)
    (state : Vec K polynomial.natDegree) :
    companion.advance (count + 1) state = companion.advance count (companion.step state) := by
  induction count with
  | zero => rfl
  | succ count previous => exact congrArg companion.step previous

/-- The same finite transition count acts by the original retained companion matrix power.

The matrix and transition procedures consume the same original state and
generator. The proof compares their actual structural vector payloads.
-/
theorem advance_matrix_power (companion : Companion polynomial) (count : Nat)
    (state : Vec K polynomial.natDegree) :
    companion.advance count state =
      Mat.Multiplication.matrixVector (Mat.Arithmetic.power companion.matrix count) state := by
  induction count generalizing state with
  | zero =>
      apply vector_ext
      intro row
      change state row = Mat.Multiplication.matrixVector (Mat.Multiplication.scaleIdentity 1) state row
      have reading := vector_eq_at (Mat.Multiplication.matrixVector_scaleIdentity 1 state) row
      exact ((reading.trans (vectorOfFn_apply _ row)).trans (one_mul _)).symm
  | succ count previous =>
      rewrite [advance_succ_first, previous, step, ← Mat.Multiplication.matrixVector_mul]
      rfl

/-- Read the first coordinate after one requested finite transition count. -/
@[expose] def reading (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) : K := companion.advance count state companion.firstIndex

/-- Readings before the original state dimension recover the same original coordinates. -/
theorem reading_initial (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (index : Nat) (bound : index < polynomial.natDegree) :
    companion.reading state index = state ⟨index, bound⟩ := by
  induction index generalizing state with
  | zero => rfl
  | succ index previous =>
      change companion.advance (index + 1) state companion.firstIndex = _
      rw [advance_succ_first]
      have earlier : index < polynomial.natDegree := Nat.lt_of_succ_lt bound
      have initial := previous (companion.step state) earlier
      exact initial.trans (companion.step_shift state ⟨index, earlier⟩ bound)

/-- A first-row power entry is the same original companion's reading of its identity-column state. -/
theorem power_first_reading (companion : Companion polynomial) (count : Nat)
    (column : Fin polynomial.natDegree) :
    Mat.Arithmetic.power companion.matrix count companion.firstIndex column =
      companion.reading (vectorOfFn fun row => Mat.Multiplication.scaleIdentity (1 : K) row column) count := by
  let state : Vec K polynomial.natDegree :=
    vectorOfFn fun row => Mat.Multiplication.scaleIdentity (1 : K) row column
  have readback : companion.reading state count = companion.advance count state companion.firstIndex := rfl
  rewrite [companion.advance_matrix_power] at readback
  have action := Mat.Multiplication.matrixVector_column_eq_mul_apply
    (Mat.Arithmetic.power companion.matrix count)
    (Mat.Multiplication.scaleIdentity (1 : K)) companion.firstIndex column
  change Mat.Multiplication.matrixVector (Mat.Arithmetic.power companion.matrix count) state
    companion.firstIndex = _ at action
  rewrite [Mat.Multiplication.mul_unit] at action
  exact action.symm.trans readback.symm

/-- The first row of each initial companion power is its original coordinate unit. -/
theorem power_first_entry (companion : Companion polynomial)
    (index column : Fin polynomial.natDegree) :
    Mat.Arithmetic.power companion.matrix index.val companion.firstIndex column =
      if index = column then 1 else 0 := by
  rewrite [power_first_reading, companion.reading_initial _ index.val index.isLt,
    vectorOfFn_apply, Mat.Multiplication.scaleIdentity_apply]
  rfl

/-- Each retained state coordinate is the corresponding later finite reading. -/
theorem advance_at (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) (index : Fin polynomial.natDegree) :
    companion.advance count state index = companion.reading state (count + index.val) := by
  change _ = companion.advance (count + index.val) state companion.firstIndex
  rw [advance_add]
  exact (companion.reading_initial (companion.advance count state) index.val index.isLt).symm

/-- The reading immediately after a full initial state is its original feedback sum. -/
theorem reading_degree (companion : Companion polynomial) (state : Vec K polynomial.natDegree) :
    companion.reading state polynomial.natDegree = companion.step state companion.lastIndex := by
  have positive := companion.positive
  have degree : polynomial.natDegree = (polynomial.natDegree - 1) + 1 := by omega0
  have advanced : companion.advance polynomial.natDegree state =
      companion.advance (polynomial.natDegree - 1) (companion.step state) :=
    (congrArg (fun count => companion.advance count state) degree).trans
      (companion.advance_succ_first (polynomial.natDegree - 1) state)
  calc
    _ = companion.advance (polynomial.natDegree - 1) (companion.step state) companion.firstIndex :=
      congrArg (fun values : Vec K polynomial.natDegree => values companion.firstIndex) advanced
    _ = _ := companion.reading_initial (companion.step state)
      (polynomial.natDegree - 1) companion.lastIndex.isLt

/-- The first row immediately after a full initial state reads the same cached feedback vector. -/
theorem power_degree_first_entry (companion : Companion polynomial)
    (column : Fin polynomial.natDegree) :
    Mat.Arithmetic.power companion.matrix polynomial.natDegree companion.firstIndex column =
      companion.feedback column := by
  rewrite [power_first_reading, reading_degree, step_last]
  calc
    _ = Fin.sumFin (fun index : Fin polynomial.natDegree =>
        if index = column then companion.feedback index else 0) := by
      apply Fin.sumFin_congr
      intro index
      rewrite [vectorOfFn_apply, Mat.Multiplication.scaleIdentity_apply]
      by_cases same : index = column
      · rewrite [if_pos same, if_pos same, mul_one]
        rfl
      · rewrite [if_neg same, if_neg same, mul_zero]
        rfl
    _ = _ := Fin.sumFin_ite_eq column companion.feedback

/-- Every finite reading horizon satisfies the original coefficient recurrence.

The retained lower coefficients and original leading coefficient are used in
ascending order. Their source-shape certificate identifies this same equation
with the original normalized polynomial.
-/
theorem reading_equation (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) :
    Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * companion.reading state (count + column.val)) +
      polynomial.leadingCoeff * companion.reading state (count + polynomial.natDegree) = 0 := by
  have original := companion.step_equation (companion.advance count state)
  have lower : Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * companion.advance count state column) =
      Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * companion.reading state (count + column.val)) := by
    apply Fin.sumFin_congr
    intro column
    rw [advance_at]
  have next : companion.step (companion.advance count state) companion.lastIndex =
      companion.reading state (count + polynomial.natDegree) := by
    change _ = companion.advance (count + polynomial.natDegree) state companion.firstIndex
    rw [advance_add]
    exact (companion.reading_degree (companion.advance count state)).symm
  rw [lower, next] at original
  exact original

/-- Materialize a supplied finite horizon of the original companion readings. -/
@[expose] def window (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) : Vec K count := vectorOfFn fun index => companion.reading state index.val

/-- An original finite horizon entry is its same companion reading. -/
theorem window_at (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) (index : Fin count) :
    companion.window state count index = companion.reading state index.val := vectorOfFn_apply _ _

/-- Two finite horizons agree at every retained common coordinate. -/
theorem window_prefix (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (first second : Nat) (index : Fin first) (bound : index.val < second) :
    companion.window state first index = companion.window state second ⟨index.val, bound⟩ := by
  rw [window_at, window_at]

/-- A finite horizon satisfies every original coefficient row wholly inside it. -/
@[expose] def Satisfies (companion : Companion polynomial) {count : Nat} (values : Vec K count) : Prop :=
  ∀ start (bound : start + polynomial.natDegree < count),
    Fin.sumFin (fun column : Fin polynomial.natDegree =>
      getD companion.coefficients column.val 0 *
        values ⟨start + column.val, Nat.lt_trans (Nat.add_lt_add_left column.isLt start) bound⟩) +
      polynomial.leadingCoeff * values ⟨start + polynomial.natDegree, bound⟩ = 0

/-- A finite weighted combination of original recurrence columns satisfies the same original rows. -/
theorem satisfies_apply (companion : Companion polynomial) {count columns : Nat}
    (matrix : Mat.Rectangular K count columns) (weights : Vec K columns)
    (equations : ∀ column, companion.Satisfies (Mat.Rectangular.column matrix column)) :
    companion.Satisfies (Mat.Rectangular.apply matrix weights) := by
  intro start bound
  have rows : ∀ column : Fin columns,
      Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
        matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) +
        polynomial.leadingCoeff * matrix ⟨start + polynomial.natDegree, bound⟩ column = 0 := by
    intro column
    have original := equations column start bound
    have lower : Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
          Mat.Rectangular.column matrix column
            ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩) =
        Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
          matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) := by
      apply Fin.sumFin_congr
      intro index
      rw [Mat.Rectangular.column_at]
    rw [lower, Mat.Rectangular.column_at] at original
    exact original
  have lower : Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
        Mat.Rectangular.apply matrix weights
          ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩) =
      Fin.sumFin (fun column : Fin columns =>
        Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
          matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) *
            weights column) := by
    calc
      _ = Fin.sumFin (fun index : Fin polynomial.natDegree => Fin.sumFin (fun column : Fin columns =>
          (getD companion.coefficients index.val 0 *
            matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) *
              weights column)) := by
        apply Fin.sumFin_congr
        intro index
        rw [Mat.Rectangular.apply_at, ← Fin.sumFin_mul_left]
        apply Fin.sumFin_congr
        intro column
        exact (mul_assoc _ _ _).symm
      _ = Fin.sumFin (fun column : Fin columns => Fin.sumFin (fun index : Fin polynomial.natDegree =>
          (getD companion.coefficients index.val 0 *
            matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) *
              weights column)) := Fin.sumFin_swap _
      _ = _ := by
        apply Fin.sumFin_congr
        intro column
        exact Fin.sumFin_mul_right _ _
  rw [lower, Mat.Rectangular.apply_at, ← Fin.sumFin_mul_left, ← Fin.sumFin_add]
  calc
    _ = Fin.sumFin (fun column : Fin columns =>
        (Fin.sumFin (fun index : Fin polynomial.natDegree => getD companion.coefficients index.val 0 *
          matrix ⟨start + index.val, Nat.lt_trans (Nat.add_lt_add_left index.isLt start) bound⟩ column) +
            polynomial.leadingCoeff * matrix ⟨start + polynomial.natDegree, bound⟩ column) * weights column) := by
      apply Fin.sumFin_congr
      intro column
      ring0
    _ = Fin.sumFin (fun _ : Fin columns => (0 : K)) := by
      apply Fin.sumFin_congr
      intro column
      rw [rows column, zero_mul]
    _ = 0 := Fin.sumFin_zero

/-- Every executed finite horizon satisfies all of its complete original recurrence rows. -/
theorem window_satisfies (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    (count : Nat) : companion.Satisfies (companion.window state count) := by
  intro start bound
  have lower : Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 *
          companion.window state count
            ⟨start + column.val, Nat.lt_trans (Nat.add_lt_add_left column.isLt start) bound⟩) =
      Fin.sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * companion.reading state (start + column.val)) := by
    apply Fin.sumFin_congr
    intro column
    rw [window_at]
  rw [lower, window_at]
  exact companion.reading_equation state start

/-- A supplied finite horizon is uniquely determined by its original initial coordinates and rows.

The recurrence is used only when its complete coefficient row lies inside the
supplied horizon. No later reading or completed trajectory is assumed.
-/
theorem window_unique (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    {count : Nat} (values : Vec K count) (enough : polynomial.natDegree ≤ count)
    (initial : ∀ column : Fin polynomial.natDegree,
      values ⟨column.val, Nat.lt_of_lt_of_le column.isLt enough⟩ = state column)
    (equations : companion.Satisfies values) : values = companion.window state count := by
  have entries : ∀ index (bound : index < count),
      values ⟨index, bound⟩ = companion.reading state index := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index previous =>
      intro bound
      by_cases early : index < polynomial.natDegree
      · exact (initial ⟨index, early⟩).trans
          (companion.reading_initial state index early).symm
      · let start := index - polynomial.natDegree
        have position : start + polynomial.natDegree = index := by dsimp only [start]; omega0
        have complete : start + polynomial.natDegree < count := position ▸ bound
        have original := equations start complete
        have lower : Fin.sumFin (fun column : Fin polynomial.natDegree =>
              getD companion.coefficients column.val 0 *
                values ⟨start + column.val, (Nat.add_lt_add_left column.isLt start).trans complete⟩) =
            Fin.sumFin (fun column : Fin polynomial.natDegree =>
              getD companion.coefficients column.val 0 * companion.reading state (start + column.val)) := by
          apply Fin.sumFin_congr
          intro column
          have earlier : start + column.val < index := by omega0
          rw [previous (start + column.val) earlier]
        rw [lower] at original
        have canonical := companion.reading_equation state start
        have products : polynomial.leadingCoeff * values ⟨index, bound⟩ =
            polynomial.leadingCoeff * companion.reading state index := by
          have same := original.trans canonical.symm
          have cancelled := add_left_cancel same
          have coordinate : (⟨start + polynomial.natDegree, complete⟩ : Fin count) = ⟨index, bound⟩ :=
            Fin.ext position
          have reading := congrArg (companion.reading state) position
          rw [coordinate, reading] at cancelled
          exact cancelled
        have unit : companion.leadingInverse * polynomial.leadingCoeff = 1 :=
          (mul_comm _ _).trans companion.leading_unit
        calc
          values ⟨index, bound⟩ =
              (companion.leadingInverse * polynomial.leadingCoeff) * values ⟨index, bound⟩ := by
            rw [unit, one_mul]
          _ = companion.leadingInverse * (polynomial.leadingCoeff * values ⟨index, bound⟩) := mul_assoc _ _ _
          _ = companion.leadingInverse * (polynomial.leadingCoeff * companion.reading state index) :=
            congrArg (companion.leadingInverse * ·) products
          _ = (companion.leadingInverse * polynomial.leadingCoeff) * companion.reading state index :=
            (mul_assoc _ _ _).symm
          _ = companion.reading state index := by rw [unit, one_mul]
  apply vector_ext
  intro index
  rw [window_at]
  exact entries index.val index.isLt

/-- Every bounded path satisfying the original transition has the same retained states. -/
theorem advance_unique (companion : Companion polynomial) (state : Vec K polynomial.natDegree)
    {count : Nat} (path : Vec (Vec K polynomial.natDegree) (count + 1))
    (initial : path 0 = state)
    (transitions : ∀ index : Fin count,
      path index.succ = companion.step (path ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩))
    (index : Fin (count + 1)) : path index = companion.advance index.val state := by
  rcases index with ⟨index, bound⟩
  induction index with
  | zero => exact initial
  | succ index previous =>
      have small : index < count := Nat.lt_of_succ_lt_succ bound
      have prior := previous (Nat.lt_succ_of_lt small)
      exact (transitions ⟨index, small⟩).trans (congrArg companion.step prior)

end Purelib.Polynomial.Dense.Companion
