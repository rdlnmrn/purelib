module

public import Purelib.Data.Fin.Fold.Max
import Purelib.Polynomial.Dense.Resource
public import Purelib.Data.Gaussian.Field

import Purelib.Data.Gaussian.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Resource.Slots
import Purelib.Data.List.OfFn.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Vector.Basic

/-!
# Coefficient-slot envelopes for Gaussian polynomial matrices
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots

open Purelib
open Purelib.LinearAlgebra

open Purelib.Polynomial.Dense.Basic.DensePolynomial

public section

/-- Every retained polynomial matrix entry fits within the supplied coefficient-list length bound.

The allowance applies to every pair of original bounded matrix indices. It describes the retained coefficient lists
without rebuilding or normalizing the entries. -/
@[expose] def MatrixSlotsWithin {count : Nat} (matrix : Basic.GaussianNumberMatrix count)
    (slots : Nat) : Prop :=
  ∀ row column, (matrix row column).coeffs.length ≤ slots

/-- A finite Gaussian polynomial sum preserves a common coefficient-list length bound.

The finite sum traverses the original List.ofFn coordinate enumeration. Every supplied coordinate satisfies the common
coefficient-list allowance. -/
private theorem sumFin_slots {count : Nat}
    (values : Fin count → Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) (bound : Nat)
    (valuesBound : ∀ index, (values index).coeffs.length ≤ bound) :
    (PolynomialMatrix.Basic.sumFin values).coeffs.length ≤
      bound := open Purelib.Polynomial in by
  unfold PolynomialMatrix.Basic.sumFin
  apply Purelib.Polynomial.Dense.Gaussian.Resource.Slots.foldl_add_slots _ 0 bound (Nat.zero_le _)
  intro value member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
  exact valuesBound index

/-- A Gaussian polynomial dot product fits within the sum of the two input slot bounds.

Each paired product uses the original left and right coordinate at the same bounded index. Their coefficient counts are
added before the finite common-bound sum. -/
theorem dot_slots {count : Nat}
    (left right : PolynomialMatrix.Basic.Vector
      Data.Gaussian.Basic.Number count)
    (leftBound rightBound : Nat)
    (leftWithin : ∀ index, (left index).coeffs.length ≤ leftBound)
    (rightWithin : ∀ index, (right index).coeffs.length ≤ rightBound) :
    (PolynomialMatrix.Basic.dot left right).coeffs.length ≤
      leftBound + rightBound := open Purelib.Polynomial in by
  apply Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots.sumFin_slots
  intro index
  exact Nat.le_trans
    (Purelib.Polynomial.Dense.Gaussian.Resource.Slots.mul_slots (left index) (right index))
    (Nat.add_le_add (leftWithin index) (rightWithin index))

/-- Compute the finite maximum coefficient-list length across all matrix entries.

The nested bounded-index maxima return zero for an empty matrix. -/
@[expose] def matrixSlotBound {count : Nat} (matrix : Basic.GaussianNumberMatrix count) :
  Nat :=
  Data.Fin.Fold.Max.maxFin count (fun row => Data.Fin.Fold.Max.maxFin count (fun column =>
    (matrix row column).coeffs.length))

/-- A uniform entrywise slot allowance bounds the computed matrix slot maximum. -/
theorem matrixSlotBound_le {count : Nat} {matrix : Basic.GaussianNumberMatrix count}
    {slots : Nat} (within : PolynomialMatrix.Resource.Gaussian.Slots.MatrixSlotsWithin matrix slots) :
    PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix ≤ slots := by
  unfold PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound
  apply Purelib.Data.Fin.Fold.Max.maxFin_le
  intro row
  apply Purelib.Data.Fin.Fold.Max.maxFin_le
  intro column
  exact within row column

/-- Every retained matrix entry fits within the computed matrix slot maximum. -/
theorem matrixSlot_le {count : Nat} (matrix : Basic.GaussianNumberMatrix count)
    (row column : Fin count) :
    (matrix row column).coeffs.length ≤ PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix :=
  Nat.le_trans
    (Data.Fin.Fold.Max.le_maxFin (fun column => (matrix row column).coeffs.length) column)
    (Data.Fin.Fold.Max.le_maxFin (fun row => Data.Fin.Fold.Max.maxFin count (fun column =>
      (matrix row column).coeffs.length)) row)

end

end Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots
