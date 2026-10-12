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
    (values : List Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) (accumulator :
      Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial)
    (bound : Nat),
    Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound →
    (∀ value ∈ values, Dense.Resource.PolynomialWithin
      Purelib.Data.Gaussian.Resource.Model.gaussianModel value bound) →
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel accumulator bound →
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (values.foldl (· + ·) accumulator)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
        values.length)
  | [], _, _, _, _, accumulatorWithin => by
      simpa only [List.foldl_nil, List.length_nil, Algebra.Field.Resource.Magnitude.grow_zero, -eq_self, -iff_self]
        using accumulatorWithin
  | value :: remaining, accumulator, bound, zeroBound, valuesWithin,
      accumulatorWithin => by
      simp only [List.foldl_cons, List.length_cons, -eq_self, -iff_self]
      have next := add_within Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroBound
        accumulatorWithin (valuesWithin value (List.Mem.head _))
      have remainingWithin : ∀ candidate ∈ remaining,
          Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel candidate
            (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound
              1) := by
        intro candidate member
        exact polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
          (valuesWithin candidate (List.Mem.tail value member))
          (Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 1)
      have recursive :=
        Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.foldl_add_within
        remaining (accumulator + value)
        (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 1)
        (zeroBound.trans
          (Algebra.Field.Resource.Magnitude.bound_le_grow
            Purelib.Data.Gaussian.Resource.Model.gaussianModel bound 1))
        remainingWithin next
      rw [Algebra.Field.Resource.Magnitude.grow_add] at recursive
      simpa only [Nat.add_comm, -eq_self, -iff_self] using recursive

/-- Bound a finite Gaussian polynomial sum by advancing the shared coefficient bound once per coordinate. -/
private theorem sumFin_within {count : Nat}
    (values : Fin count → Purelib.Polynomial.Dense.Gaussian.NormalizedPolynomial) (bound : Nat)
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (valuesWithin : ∀ index, Dense.Resource.PolynomialWithin
      Purelib.Data.Gaussian.Resource.Model.gaussianModel (values index) bound) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.sumFin values)
      (Purelib.Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound count) := by
  unfold PolynomialMatrix.Basic.sumFin
  have allWithin : ∀ value ∈ List.ofFn values,
      Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel value bound := by
    intro value member
    rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
    exact valuesWithin index
  simpa only [Data.List.OfFn.Basic.length_ofFn, -eq_self, -iff_self] using
    Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.foldl_add_within (List.ofFn values) 0 bound
      zeroBound allWithin
      (zero_within Purelib.Data.Gaussian.Resource.Model.gaussianModel bound)

/-- Bound a Gaussian polynomial dot product using the left coefficient lengths and finite dimension.

The shared magnitude bound covers zero and both vectors; the model pays for multiplication and the finite sum. -/
theorem dot_within {count : Nat}
    (left right : PolynomialMatrix.Basic.Vector
      Data.Gaussian.Basic.Number count)
    (bound leftSlots : Nat)
    (zeroBound : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude 0 ≤ bound)
    (leftWithin : ∀ index, Dense.Resource.PolynomialWithin
      Purelib.Data.Gaussian.Resource.Model.gaussianModel (left index) bound)
    (rightWithin : ∀ index, Dense.Resource.PolynomialWithin
      Purelib.Data.Gaussian.Resource.Model.gaussianModel (right index) bound)
    (leftSlotBound : ∀ index,
      (left index).coeffs.length ≤ leftSlots) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (PolynomialMatrix.Basic.dot left right)
      (Purelib.Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound
        (2 * leftSlots + count)) := by
  have products : ∀ index, Dense.Resource.PolynomialWithin
      Purelib.Data.Gaussian.Resource.Model.gaussianModel (left index * right index)
      (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 *
        leftSlots)) := by
    intro index
    exact polynomialWithin_mono Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (mul_within Purelib.Data.Gaussian.Resource.Model.gaussianModel zeroBound
        (leftWithin index) (rightWithin index))
      (Algebra.Field.Resource.Magnitude.grow_mono_steps Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound
        (Nat.mul_le_mul_left 2 (leftSlotBound index)))
  have summed := Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude.sumFin_within
    (fun index => left index * right index)
    (Algebra.Field.Resource.Magnitude.grow Purelib.Data.Gaussian.Resource.Model.gaussianModel bound (2 *
      leftSlots))
    (zeroBound.trans
      (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel
        bound _)) products
  rw [Algebra.Field.Resource.Magnitude.grow_add] at summed
  exact summed

/-- Every coefficient of every retained Gaussian polynomial matrix entry satisfies the supplied magnitude bound.

Each original bounded row and column selects its stored polynomial. The Gaussian resource model bounds every coefficient
of that polynomial with the shared natural allowance. -/
@[expose] def MatrixWithin {count : Nat} (matrix : Basic.GaussianNumberMatrix count)
    (bound : Nat) : Prop :=
  ∀ row column, Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel (matrix
    row column) bound

end

end Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Magnitude
