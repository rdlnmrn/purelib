module

public import Purelib.Polynomial.Recurrence.Boundary
public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.LinearAlgebra.Matrix.Rectangular.Identity
import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Original startup rows and finite shift transitions

Actual finite columns determine both their original truncated Laurent rows
and their initial reading rectangle. A retained finite shift transition moves
the same columns forward; the original polynomial recurrence identifies the
startup matrix after that shift with its original upper Toeplitz factor.
-/

public section

namespace Purelib.Polynomial.Recurrence.Boundary

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] {horizon modes : Nat}

/-- Retain each original boundary column once, then transpose their same startup coordinates. -/
@[expose] def matrix (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) : Rectangular K shift modes :=
  let columns := Vec.map (boundary polynomial shift) values
  Rectangular.transpose columns

/-- The retained boundary matrix reads its same original truncated Laurent row and input column. -/
theorem matrix_at (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (index : Fin shift) (column : Fin modes) :
    matrix polynomial shift values index column = row polynomial shift (values column) index.val := by
  rw [matrix, Rectangular.transpose_apply, map_apply, boundary_at]

/-- The actual startup matrix is the original plus rectangle acting on the same retained input columns. -/
theorem matrix_eq_plus_mul (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) :
    matrix polynomial shift values =
      Rectangular.mul (plus polynomial shift shift horizon) (Rectangular.transpose values) := by
  apply Rectangular.ext
  intro index column
  rewrite [matrix_at, row_eq_plus_apply, Rectangular.apply_at, Rectangular.mul_at]
  apply sumFin_congr
  intro coordinate
  rewrite [Rectangular.transpose_apply]
  rfl

/-- The same original startup map acts on a mode combination by its actual combined finite input horizon.

Both finite horizons and their original zero-left convention are retained.
No right-boundary equations are added by this finite matrix identity.
-/
theorem matrix_apply (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (coefficients : Vec K modes) :
    boundary polynomial shift (Rectangular.apply (Rectangular.transpose values) coefficients) =
      Rectangular.apply (matrix polynomial shift values) coefficients := by
  rewrite [matrix_eq_plus_mul, Rectangular.apply_mul]
  apply vector_ext
  intro index
  exact (boundary_at polynomial shift _ index).trans (row_eq_plus_apply polynomial shift shift horizon _ index)

/-- Retain the first requested readings of the original finite columns, with their original zero fallback. -/
@[expose] def initial (values : Vec (Vec K horizon) modes) (count : Nat) : Rectangular K count modes :=
  Rectangular.ofFn fun index column => sample (values column) index.val

/-- A prefix entry is the same original finite input reading. -/
theorem initial_at (values : Vec (Vec K horizon) modes) (count : Nat)
    (index : Fin count) (column : Fin modes) :
    initial values count index column = sample (values column) index.val := Rectangular.ofFn_apply _ _ _

/-- The original finite columns follow the displayed matrix at every available successor reading. -/
@[expose] def Transition (values : Vec (Vec K horizon) modes) (shift : SquareMatrix K modes) : Prop :=
  ∀ index, index + 1 < horizon → ∀ column,
    sumFin (fun middle => sample (values middle) index * shift middle column) =
      sample (values column) (index + 1)

/-- A retained finite transition iterates through the original finite matrix powers.

The supplied bound keeps the entire requested path within the same original
input horizon. No extension of the input columns beyond their finite data is
constructed.
-/
theorem power_reading {values : Vec (Vec K horizon) modes} {shift : SquareMatrix K modes}
    (transition : Transition values shift) (count index : Nat) (inside : index + count < horizon)
    (column : Fin modes) :
    sumFin (fun middle => sample (values middle) index * Arithmetic.power shift count middle column) =
      sample (values column) (index + count) := by
  induction count generalizing column with
  | zero =>
      calc
        _ = sumFin (fun middle => if middle = column then sample (values middle) index else 0) := by
          apply sumFin_congr
          intro middle
          rw [Arithmetic.power_zero, Multiplication.scaleIdentity_apply]
          by_cases same : middle = column
          · rw [if_pos same, if_pos same, mul_one]
          · rw [if_neg same, if_neg same, mul_zero]
        _ = sample (values column) index := sumFin_ite_eq column _
        _ = _ := congrArg (sample (values column)) (Nat.add_zero index).symm
  | succ count previous =>
      have smaller : index + count < horizon := by omega0
      calc
        _ = sumFin (fun middle => sumFin (fun next =>
            (sample (values middle) index * Arithmetic.power shift count middle next) * shift next column)) := by
          apply sumFin_congr
          intro middle
          rw [Arithmetic.power_succ, Multiplication.mul_apply, ← sumFin_mul_left]
          apply sumFin_congr
          intro next
          exact (mul_assoc _ _ _).symm
        _ = sumFin (fun next => sumFin (fun middle =>
            (sample (values middle) index * Arithmetic.power shift count middle next) * shift next column)) :=
          sumFin_swap _
        _ = sumFin (fun next => sample (values next) (index + count) * shift next column) := by
          apply sumFin_congr
          intro next
          rw [sumFin_mul_right, previous smaller next]
        _ = sample (values column) (index + count + 1) := transition _ inside column
        _ = _ := congrArg (sample (values column)) (Nat.add_assoc index count 1)

/-- The first retained startup indices satisfy the original polynomial coefficient recurrence. -/
@[expose] def Equations (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) : Prop :=
  let coefficients := polynomial.coeffs.reverse
  ∀ index : Fin shift, ∀ column : Fin modes,
    sumFin (fun coefficient : Fin coefficients.length =>
      getD coefficients coefficient.val 0 * sample (values column) (index.val + coefficient.val)) = 0

/-- The original zero-shift plus rectangle supplies the upper startup factor with sign minus. -/
@[expose] def upper (polynomial : DensePolynomial K) (shift : Nat) : SquareMatrix K shift :=
  Arithmetic.scale (-1) (plus polynomial 0 shift shift)

/-- A zero-extended prefix reads the original column before its cut and zero afterwards. -/
private theorem sample_prefix (values : Vec K horizon) (count index : Nat) :
    sample (vectorOfFn (fun coordinate : Fin count => sample values coordinate.val)) index =
      if index < count then sample values index else 0 := by
  by_cases inside : index < count
  · rw [sample, dif_pos inside, vectorOfFn_apply, if_pos inside]
  · rw [sample, dif_neg inside, if_neg inside]

/-- A boundary product shifts exactly the admitted original coefficient occurrences. -/
private theorem matrix_power_at (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (step : SquareMatrix K modes)
    (transition : Transition values step) (room : shift + polynomial.coeffs.reverse.length ≤ horizon)
    (index : Fin shift) (column : Fin modes) :
    Rectangular.mul (matrix polynomial shift values) (Arithmetic.power step shift) index column =
      sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        getD polynomial.coeffs.reverse coefficient.val 0 *
          if shift ≤ index.val + coefficient.val then sample (values column) (index.val + coefficient.val) else 0) := by
  rw [Rectangular.mul_at]
  calc
    _ = sumFin (fun middle => sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        (getD polynomial.coeffs.reverse coefficient.val 0 *
          (if shift ≤ index.val + coefficient.val then
            sample (values middle) (index.val + coefficient.val - shift) else 0)) *
              Arithmetic.power step shift middle column)) := by
      apply sumFin_congr
      intro middle
      rw [matrix_at]
      exact (sumFin_mul_right _ _).symm
    _ = sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length => sumFin (fun middle =>
        (getD polynomial.coeffs.reverse coefficient.val 0 *
          (if shift ≤ index.val + coefficient.val then
            sample (values middle) (index.val + coefficient.val - shift) else 0)) *
              Arithmetic.power step shift middle column)) := sumFin_swap _
    _ = _ := by
      apply sumFin_congr
      intro coefficient
      by_cases included : shift ≤ index.val + coefficient.val
      · have inside : index.val + coefficient.val - shift + shift < horizon := by
          have indexBound := index.isLt
          have coefficientBound := coefficient.isLt
          omega0
        have terms : sumFin (fun middle =>
            (getD polynomial.coeffs.reverse coefficient.val 0 *
              (if shift ≤ index.val + coefficient.val then
                sample (values middle) (index.val + coefficient.val - shift) else 0)) *
                  Arithmetic.power step shift middle column) =
            getD polynomial.coeffs.reverse coefficient.val 0 *
              sumFin (fun middle => sample (values middle) (index.val + coefficient.val - shift) *
                Arithmetic.power step shift middle column) := by
          calc
            _ = sumFin (fun middle => getD polynomial.coeffs.reverse coefficient.val 0 *
                (sample (values middle) (index.val + coefficient.val - shift) *
                  Arithmetic.power step shift middle column)) := by
              apply sumFin_congr
              intro middle
              rw [if_pos included, mul_assoc]
            _ = _ := sumFin_mul_left _ _
        rw [terms, power_reading transition shift _ inside column]
        have same : index.val + coefficient.val - shift + shift = index.val + coefficient.val := by omega0
        rw [same, if_pos included]
      · have terms : sumFin (fun middle =>
            (getD polynomial.coeffs.reverse coefficient.val 0 *
              (if shift ≤ index.val + coefficient.val then
                sample (values middle) (index.val + coefficient.val - shift) else 0)) *
                  Arithmetic.power step shift middle column) = 0 := by
          calc
            _ = sumFin (fun _ : Fin modes => (0 : K)) := by
              apply sumFin_congr
              intro middle
              rw [if_neg included, mul_zero, zero_mul]
            _ = 0 := sumFin_zero
        rw [terms, if_neg included, mul_zero]

/-- The actual finite startup matrix factors through the original upper Toeplitz and initial-reading matrices.

The original polynomial recurrence cancels precisely the complementary
coefficient occurrences omitted by the startup rows. All columns, shifts,
powers and finite horizons belong to the same original inputs.
-/
theorem factorization (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (step : SquareMatrix K modes)
    (transition : Transition values step) (room : shift + polynomial.coeffs.reverse.length ≤ horizon)
    (equations : Equations polynomial shift values) :
    Rectangular.mul (matrix polynomial shift values) (Arithmetic.power step shift) =
      Rectangular.mul (upper polynomial shift) (initial values shift) := by
  apply Rectangular.ext
  intro index column
  let initialColumn : Vec K shift := vectorOfFn fun coordinate => sample (values column) coordinate.val
  have low : row polynomial 0 initialColumn index.val =
      sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        getD polynomial.coeffs.reverse coefficient.val 0 *
          if index.val + coefficient.val < shift then sample (values column) (index.val + coefficient.val) else 0) := by
    apply sumFin_congr
    intro coefficient
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, sample_prefix]
  have total : Rectangular.mul (matrix polynomial shift values) (Arithmetic.power step shift) index column +
      row polynomial 0 initialColumn index.val = 0 := by
    rw [matrix_power_at polynomial shift values step transition room index column, low, ← sumFin_add]
    calc
      _ = sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
          getD polynomial.coeffs.reverse coefficient.val 0 * sample (values column) (index.val + coefficient.val)) := by
        apply sumFin_congr
        intro coefficient
        by_cases included : shift ≤ index.val + coefficient.val
        · rw [if_pos included, if_neg (Nat.not_lt_of_ge included), mul_zero, add_zero]
        · rw [if_neg included, if_pos (Nat.lt_of_not_ge included), mul_zero, zero_add]
      _ = 0 := equations index column
  have upperProduct : Rectangular.mul (upper polynomial shift) (initial values shift) index column =
      -row polynomial 0 initialColumn index.val := by
    rw [Rectangular.mul_at]
    calc
      _ = sumFin (fun middle => (-1 : K) *
          (plus polynomial 0 shift shift index middle * initialColumn middle)) := by
        apply sumFin_congr
        intro middle
        rw [upper, Arithmetic.scale_apply, initial_at]
        rw [vectorOfFn_apply, mul_assoc]
      _ = (-1 : K) * Rectangular.apply (plus polynomial 0 shift shift) initialColumn index :=
        by rw [Rectangular.apply_at]; exact sumFin_mul_left _ _
      _ = (-1 : K) * row polynomial 0 initialColumn index.val :=
        congrArg (fun value => (-1 : K) * value) (row_eq_plus_apply polynomial 0 shift shift initialColumn index).symm
      _ = _ := by ring0
  rw [upperProduct]
  exact add_right_cancel (total.trans (by ring0 : (0 : K) = -row polynomial 0 initialColumn index.val +
    row polynomial 0 initialColumn index.val))

end Purelib.Polynomial.Recurrence.Boundary

end
