module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.List.OfFn.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Vector.Basic

open Purelib.Data.Gaussian.Resource
open Purelib.Algebra.Field.Resource

/-!
# Retained polynomial inverse resource envelopes

The original Schur and block recurrences retain their scalar, inverse and coefficient
data. Slot and magnitude certificates bound those same stored polynomials.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude

open Purelib
open Purelib.LinearAlgebra
open Purelib.Polynomial

open Purelib.Polynomial.Dense.Resource

public section

/-- Bound coefficient magnitudes through a finite polynomial addition fold.

The initial bound covers zero, the accumulator and every input polynomial; the model advances once per list entry. -/
private theorem foldl_add_within : ∀
    (values : List Dense.Gaussian.NormalizedPolynomial) (accumulator :
      Dense.Gaussian.NormalizedPolynomial)
    (bound : Nat),
    Model.gaussianModel.magnitude 0 ≤ bound →
    (∀ value ∈ values, PolynomialWithin
      Model.gaussianModel value bound) →
    PolynomialWithin Model.gaussianModel accumulator bound →
    PolynomialWithin Model.gaussianModel
      (values.foldl (· + ·) accumulator)
      (Magnitude.grow Model.gaussianModel bound
        values.length)
  | [], _, _, _, _, accumulatorWithin => by
      simpa only [List.foldl_nil, List.length_nil, Magnitude.grow_zero, -eq_self, -iff_self]
        using accumulatorWithin
  | value :: remaining, accumulator, bound, zeroBound, valuesWithin,
      accumulatorWithin => by
      simp only [List.foldl_cons, List.length_cons, -eq_self, -iff_self]
      have next := add_within Model.gaussianModel zeroBound
        accumulatorWithin (valuesWithin value (List.Mem.head _))
      have remainingWithin : ∀ candidate ∈ remaining,
          PolynomialWithin Model.gaussianModel candidate
            (Magnitude.grow Model.gaussianModel bound
              1) := by
        intro candidate member
        exact polynomialWithin_mono Model.gaussianModel
          (valuesWithin candidate (List.Mem.tail value member))
          (Magnitude.bound_le_grow
            Model.gaussianModel bound 1)
      have recursive :=
        Magnitude.foldl_add_within
        remaining (accumulator + value)
        (Magnitude.grow Model.gaussianModel bound 1)
        (zeroBound.trans
          (Magnitude.bound_le_grow
            Model.gaussianModel bound 1))
        remainingWithin next
      rw [Magnitude.grow_add] at recursive
      simpa only [Nat.add_comm, -eq_self, -iff_self] using recursive

/-- Bound a finite Gaussian polynomial sum by advancing the shared coefficient bound once per coordinate. -/
private theorem sumFin_within {count : Nat}
    (values : Fin count → Dense.Gaussian.NormalizedPolynomial) (bound : Nat)
    (zeroBound : Model.gaussianModel.magnitude 0 ≤ bound)
    (valuesWithin : ∀ index, PolynomialWithin
      Model.gaussianModel (values index) bound) :
    PolynomialWithin Model.gaussianModel
      (Basic.sumFin values)
      (Magnitude.grow Model.gaussianModel
        bound count) := by
  unfold Basic.sumFin
  have allWithin : ∀ value ∈ List.ofFn values,
      PolynomialWithin Model.gaussianModel value bound := by
    intro value member
    rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
    exact valuesWithin index
  simpa only [Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] using
    foldl_add_within (List.ofFn values) 0 bound
      zeroBound allWithin
      (zero_within Model.gaussianModel bound)

/-- Bound a Gaussian polynomial dot product using the left coefficient lengths and finite dimension.

The shared magnitude bound covers zero and both vectors; the model pays for multiplication and the finite sum. -/
theorem dot_within {count : Nat}
    (left right : Basic.Vector
      Data.Gaussian.Basic.Number count)
    (bound leftSlots : Nat)
    (zeroBound : Model.gaussianModel.magnitude 0 ≤ bound)
    (leftWithin : ∀ index, PolynomialWithin
      Model.gaussianModel (left index) bound)
    (rightWithin : ∀ index, PolynomialWithin
      Model.gaussianModel (right index) bound)
    (leftSlotBound : ∀ index,
      (left index).coeffs.length ≤ leftSlots) :
    PolynomialWithin Model.gaussianModel
      (Basic.dot left right)
      (Magnitude.grow Model.gaussianModel
        bound
        (2 * leftSlots + count)) := by
  have products : ∀ index, PolynomialWithin
      Model.gaussianModel (left index * right index)
      (Magnitude.grow Model.gaussianModel bound (2 *
        leftSlots)) := by
    intro index
    exact polynomialWithin_mono Model.gaussianModel
      (mul_within Model.gaussianModel zeroBound
        (leftWithin index) (rightWithin index))
      (Magnitude.grow_mono_steps Model.gaussianModel
        bound
        (Nat.mul_le_mul_left 2 (leftSlotBound index)))
  have summed := sumFin_within
    (fun index => left index * right index)
    (Magnitude.grow Model.gaussianModel bound (2 *
      leftSlots))
    (zeroBound.trans
      (Magnitude.bound_le_grow Model.gaussianModel
        bound _)) products
  rw [Magnitude.grow_add] at summed
  exact summed

/-- Every coefficient of every retained Gaussian polynomial matrix entry satisfies the supplied magnitude bound.

Each original bounded row and column selects its stored polynomial. The Gaussian resource model bounds every coefficient
of that polynomial with the shared natural allowance. -/
@[expose] def MatrixWithin {count : Nat} (matrix : Basic.GaussianNumberMatrix count)
    (bound : Nat) : Prop :=
  ∀ row column, PolynomialWithin Model.gaussianModel (matrix
    row column) bound

end

end Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude
