module

public import Purelib.Polynomial.Dense.Basic
public import Purelib.LinearAlgebra.Matrix.Rectangular
public import Purelib.Data.List.GetD
import Purelib.Data.List.Reverse
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Original truncated Laurent rows

The plus-shift convention reads coefficient k against input n+k and omits
negative input indices. Polynomialization separates the first p actual rows
from the original coefficient recurrence. Rectangular Toeplitz entries use
the opposite coefficient sign, with the exact finite transpose retained.
-/

public section

namespace Purelib.Polynomial.Recurrence

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K]

/-- Read a finite horizon at a natural coordinate, with zero beyond its length. -/
@[expose] def sample {count : Nat} (values : Vec K count) (index : Nat) : K :=
  if bound : index < count then values ⟨index, bound⟩ else 0

/-- An in-range horizon reading is the same retained structural coordinate. -/
theorem sample_at {count : Nat} (values : Vec K count) (index : Fin count) :
    sample values index.val = values index := by
  rw [sample, dif_pos index.isLt]

/-- A finite delta sum reads the retained entry or zero outside its horizon. -/
private theorem delta_sum {count : Nat} (values : Fin count → K) (position : Nat) :
    sumFin (fun index => if index.val = position then values index else 0) =
      if bound : position < count then values ⟨position, bound⟩ else 0 := by
  by_cases bound : position < count
  · rw [dif_pos bound]
    let target : Fin count := ⟨position, bound⟩
    have entries : sumFin (fun index => if index.val = position then values index else 0) =
        sumFin (fun index => if index = target then values index else 0) := by
      apply sumFin_congr
      intro index
      by_cases equal : index.val = position
      · rw [if_pos equal, if_pos (Fin.ext equal)]
      · have different : index ≠ target := fun same => equal (congrArg Fin.val same)
        rw [if_neg equal, if_neg different]
    exact entries.trans (sumFin_ite_eq target values)
  · rw [dif_neg bound]
    have entries : sumFin (fun index : Fin count => if index.val = position then values index else 0) =
        sumFin (fun _ : Fin count => (0 : K)) := by
      apply sumFin_congr
      intro index
      have different : index.val ≠ position := by
        intro equal
        exact bound (equal ▸ index.isLt)
      rw [if_neg different]
    exact entries.trans sumFin_zero

/-- A startup reading has the exact finite delta expansion on the original input horizon. -/
private theorem startup_sum {count : Nat} (values : Vec K count) (shift row coefficient : Nat) :
    (if shift ≤ row + coefficient then sample values (row + coefficient - shift) else 0) =
      sumFin (fun index : Fin count =>
        if index.val + shift = row + coefficient then values index else 0) := by
  by_cases included : shift ≤ row + coefficient
  · rw [if_pos included]
    have terms : sumFin (fun index : Fin count =>
          if index.val + shift = row + coefficient then values index else 0) =
        sumFin (fun index => if index.val = row + coefficient - shift then values index else 0) := by
      apply sumFin_congr
      intro index
      by_cases equal : index.val + shift = row + coefficient
      · have position : index.val = row + coefficient - shift := by omega0
        rw [if_pos equal, if_pos position]
      · have different : index.val ≠ row + coefficient - shift := by omega0
        rw [if_neg equal, if_neg different]
    exact (terms.trans (delta_sum _ _)).symm
  · rw [if_neg included]
    have terms : sumFin (fun index : Fin count =>
          if index.val + shift = row + coefficient then values index else 0) =
        sumFin (fun _ : Fin count => (0 : K)) := by
      apply sumFin_congr
      intro index
      have different : index.val + shift ≠ row + coefficient := by omega0
      rw [if_neg different]
    exact (terms.trans sumFin_zero).symm

/-- Read one actual zero-left Laurent row from the original polynomial table.

The original coefficient table is reversed once into ascending order. Its
jth coefficient is the Laurent coefficient at j-shift; negative input indices
are omitted and readings beyond the supplied finite horizon are zero.
-/
@[expose] def row (polynomial : DensePolynomial K) (shift : Nat)
    {count : Nat} (values : Vec K count) (index : Nat) : K :=
  let coefficients := polynomial.coeffs.reverse
  sumFin fun coefficient : Fin coefficients.length =>
    getD coefficients coefficient.val 0 *
      if shift ≤ index + coefficient.val then
        sample values (index + coefficient.val - shift) else 0

/-- Retain the first p original rows, including the actual zero startup equations. -/
@[expose] def boundary (polynomial : DensePolynomial K) (shift : Nat)
    {count : Nat} (values : Vec K count) : Vec K shift :=
  vectorOfFn fun index => row polynomial shift values index.val

/-- Every boundary coordinate reads its original truncated Laurent row. -/
theorem boundary_at (polynomial : DensePolynomial K) (shift : Nat)
    {count : Nat} (values : Vec K count) (index : Fin shift) :
    boundary polynomial shift values index = row polynomial shift values index.val :=
  vectorOfFn_apply _ _

/-- A zero shift has no retained startup rows. -/
theorem boundary_zero (polynomial : DensePolynomial K) {count : Nat}
    (values : Vec K count) : boundary polynomial 0 values = .nil := rfl

/-- Tail rows are the original plus-shift polynomial recurrence.

The finite coefficient table and input horizon are unchanged. The startup
index subtraction is cancelled at n=p+t, without selecting any root modes.
-/
theorem row_tail (polynomial : DensePolynomial K) (shift : Nat)
    {count : Nat} (values : Vec K count) (index : Nat) :
    row polynomial shift values (shift + index) =
      sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        getD polynomial.coeffs.reverse coefficient.val 0 * sample values (index + coefficient.val)) := by
  apply sumFin_congr
  intro coefficient
  have included : shift ≤ shift + index + coefficient.val := by omega0
  rw [if_pos included]
  have position : shift + index + coefficient.val - shift = index + coefficient.val := by omega0
  rw [position]

/-- Read the conventional Toeplitz coefficient c_(row-column).

The shift converts the signed Laurent exponent into an ascending coefficient
index. A negative index is omitted and an index beyond the source table is zero.
-/
@[expose] def toeplitzEntry (polynomial : DensePolynomial K) (shift row column : Nat) : K :=
  if column ≤ row + shift then getD polynomial.coeffs.reverse (row + shift - column) 0 else 0

/-- Retain the conventional finite Toeplitz rectangle with both explicit horizons. -/
@[expose] def toeplitz (polynomial : DensePolynomial K) (shift rows columns : Nat) :
    Rectangular K rows columns :=
  let coefficients := polynomial.coeffs.reverse
  Rectangular.ofFn fun row column =>
    if column.val ≤ row.val + shift then getD coefficients (row.val + shift - column.val) 0 else 0

/-- A retained conventional entry is the original coefficient c_(row-column). -/
theorem toeplitz_at (polynomial : DensePolynomial K) (shift rows columns : Nat)
    (row : Fin rows) (column : Fin columns) :
    toeplitz polynomial shift rows columns row column =
      toeplitzEntry polynomial shift row.val column.val :=
  Rectangular.ofFn_apply _ _ _

/-- Retain the plus-shift rectangle with original coefficient c_(column-row). -/
@[expose] def plus (polynomial : DensePolynomial K) (shift rows columns : Nat) :
    Rectangular K rows columns :=
  let coefficients := polynomial.coeffs.reverse
  Rectangular.ofFn fun row column =>
    if row.val ≤ column.val + shift then getD coefficients (column.val + shift - row.val) 0 else 0

/-- A plus-shift entry uses the opposite original coefficient sign. -/
theorem plus_at (polynomial : DensePolynomial K) (shift rows columns : Nat)
    (row : Fin rows) (column : Fin columns) :
    plus polynomial shift rows columns row column =
      toeplitzEntry polynomial shift column.val row.val :=
  Rectangular.ofFn_apply _ _ _

/-- The plus-shift rectangle is the conventional rectangle's exact transpose.

The row and column horizons are exchanged. No extra right-boundary row is
included in this finite identity.
-/
theorem plus_transpose (polynomial : DensePolynomial K) (shift rows columns : Nat) :
    plus polynomial shift rows columns =
      Rectangular.transpose (toeplitz polynomial shift columns rows) := by
  apply Rectangular.ext
  intro row column
  rw [plus_at, Rectangular.transpose_apply, toeplitz_at]

/-- The original coefficient row is the corresponding actual plus-matrix product.

Both finite index ranges are retained. Delta expansion and finite sum exchange
identify the coefficient occurrence contributing to each original input entry.
-/
theorem row_eq_plus_apply (polynomial : DensePolynomial K) (shift rows columns : Nat)
    (values : Vec K columns) (index : Fin rows) :
    row polynomial shift values index.val =
      Rectangular.apply (plus polynomial shift rows columns) values index := by
  rw [Rectangular.apply_at]
  change sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
      getD polynomial.coeffs.reverse coefficient.val 0 *
        if shift ≤ index.val + coefficient.val then
          sample values (index.val + coefficient.val - shift) else 0) = _
  calc
    _ = sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
        sumFin (fun input : Fin columns =>
          getD polynomial.coeffs.reverse coefficient.val 0 *
            if input.val + shift = index.val + coefficient.val then values input else 0)) := by
      apply sumFin_congr
      intro coefficient
      rw [startup_sum, sumFin_mul_left]
    _ = sumFin (fun input : Fin columns =>
        sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
          getD polynomial.coeffs.reverse coefficient.val 0 *
            if input.val + shift = index.val + coefficient.val then values input else 0)) :=
      sumFin_swap _
    _ = _ := by
      apply sumFin_congr
      intro input
      rw [plus_at]
      unfold toeplitzEntry
      have factor : sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
            getD polynomial.coeffs.reverse coefficient.val 0 *
              if input.val + shift = index.val + coefficient.val then values input else 0) =
          sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
            if input.val + shift = index.val + coefficient.val then
              getD polynomial.coeffs.reverse coefficient.val 0 else 0) * values input := by
        rw [← sumFin_mul_right]
        apply sumFin_congr
        intro coefficient
        by_cases included : input.val + shift = index.val + coefficient.val
        · rw [if_pos included, if_pos included]
        · rw [if_neg included, if_neg included, mul_zero, zero_mul]
      rw [factor]
      apply congrArg (fun scalar => scalar * values input)
      by_cases included : index.val ≤ input.val + shift
      · rw [if_pos included]
        have terms : sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
              if input.val + shift = index.val + coefficient.val then
                getD polynomial.coeffs.reverse coefficient.val 0 else 0) =
            sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
              if coefficient.val = input.val + shift - index.val then
                getD polynomial.coeffs.reverse coefficient.val 0 else 0) := by
          apply sumFin_congr
          intro coefficient
          by_cases equal : input.val + shift = index.val + coefficient.val
          · have position : coefficient.val = input.val + shift - index.val := by omega0
            rw [if_pos equal, if_pos position]
          · have different : coefficient.val ≠ input.val + shift - index.val := by omega0
            rw [if_neg equal, if_neg different]
        rw [terms, delta_sum]
        split
        · rfl
        · rename_i outside
          exact (getD_eq_default_of_length_le _ _ 0 (Nat.le_of_not_gt outside)).symm
      · rw [if_neg included]
        have terms : sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
              if input.val + shift = index.val + coefficient.val then
                getD polynomial.coeffs.reverse coefficient.val 0 else 0) =
            sumFin (fun _ : Fin polynomial.coeffs.reverse.length => (0 : K)) := by
          apply sumFin_congr
          intro coefficient
          have different : input.val + shift ≠ index.val + coefficient.val := by omega0
          rw [if_neg different]
        exact terms.trans sumFin_zero

end Purelib.Polynomial.Recurrence
