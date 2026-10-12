module
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Matrix.Inverse.SymplecticBlockIdentities
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Vector.Basic

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section

/-! Integral row identities obtained through a certified finite Gaussian inverse. -/
namespace Purelib.LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows

open Purelib.LinearAlgebra
/-- The exact Gaussian rational coefficient type. -/
abbrev Gaussian :=
  Data.Gaussian.Basic.Canonical
attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Equal Gaussian casts of integers imply equal original integers. -/
private theorem cast_injective
  {first last : Int} (equal : (first : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) = (last :
  SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian)) : first = last := open Purelib.Data.Rat in by
  apply Fraction.Cast.Compatibility.intCast_injective_direct
  exact (Data.Gaussian.Cast.gaussian_int_re _).symm.trans ((congrArg Data.Gaussian.Basic.re equal).trans
    (Data.Gaussian.Cast.gaussian_int_re _))

/-- Integer casting commutes with a finite sum of signed coordinate products. -/
private theorem cast_wedge {n :
  Nat} (p q r s : Fin n → Int) :
    ((FiniteSum.Fin.sumFin (fun index => p index * s index - q index * r index) : Int) :
      SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) =
      FiniteSum.Fin.sumFin (fun index => (p index : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) * (s index :
        SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) - (q index :
        SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) * (r index :
        SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian)) := by
  rw [FiniteSum.Fin.cast_sum]
  exact FiniteSum.Fin.sumFin_congr (fun index => by
      rw [Ring.IntCast.sub, Ring.IntCast.intCast_mul, Ring.IntCast.intCast_mul])

/-- Casting an integer coordinate-equality indicator preserves its zero-or-one value. -/
private theorem cast_delta {n :
  Nat} (row column : Fin n) :
    ((if row = column then 1 else 0 : Int) : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) = if row = column
      then 1 else 0 := by
  by_cases same : row = column
  · rw [if_pos same, if_pos same, (show ((1 : Int) : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian) = 1 from
      rfl)]
  · rw [if_neg same, if_neg same, Ring.IntCast.cast_zero]

/-- Integral symplectic column identities imply the corresponding row identities.

The four retained square blocks are cast to exact Gaussian rationals for inverse cancellation and then read back by
injectivity of the integer cast. -/
theorem row_identities {n : Nat}
  (p q r s : SquareMatrix Int n)
    (pp : ∀ row column, FiniteSum.Fin.sumFin (fun index => p index row * r index column - r index row * p index column)
      = 0)
    (qq : ∀ row column, FiniteSum.Fin.sumFin (fun index => q index row * s index column - s index row * q index column)
      = 0)
    (pq : ∀ row column, FiniteSum.Fin.sumFin (fun index => p index row * s index column - r index row * q index column)
      =
      if row = column then 1 else 0) :
    (∀ row column, FiniteSum.Fin.sumFin (fun index => p row index * q column index - q row index * p column index) = 0)
      ∧
    (∀ row column, FiniteSum.Fin.sumFin (fun index => r row index * s column index - s row index * r column index) = 0)
      ∧
    (∀ row column, FiniteSum.Fin.sumFin (fun index => p row index * s column index - q row index * r column index) =
      if row = column then 1 else 0) := by
  let gp := SquareMatrix.matrixOfFn (fun row column => (p row column :
    SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian))
  let gq := SquareMatrix.matrixOfFn (fun row column => (q row column :
    SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian))
  let gr := SquareMatrix.matrixOfFn (fun row column => (r row column :
    SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian))
  let gs := SquareMatrix.matrixOfFn (fun row column => (s row column :
    SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian))
  have gpp (row column : Fin n) : FiniteSum.Fin.sumFin (fun index => gp index row * gr index column - gr index row * gp
    index column) = 0 := by
    simp only [-eq_self, -iff_self, gp, gr, SquareMatrix.matrixOfFn_apply]
    exact (LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).symm.trans
      ((congrArg (fun value : Int => (value : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian)) (pp row
      column)).trans Ring.IntCast.cast_zero)
  have gqq (row column : Fin n) : FiniteSum.Fin.sumFin (fun index => gq index row * gs index column - gs index row * gq
    index column) = 0 := by
    simp only [-eq_self, -iff_self, gq, gs, SquareMatrix.matrixOfFn_apply]
    exact (LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).symm.trans
      ((congrArg (fun value : Int => (value : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian)) (qq row
      column)).trans Ring.IntCast.cast_zero)
  have gpq (row column : Fin n) : FiniteSum.Fin.sumFin (fun index => gp index row * gs index column - gr index row * gq
    index column) =
      if row = column then 1 else 0 := by
    simp only [-eq_self, -iff_self, gp, gq, gr, gs, SquareMatrix.matrixOfFn_apply]
    exact (LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).symm.trans
      ((congrArg (fun value : Int => (value : SquareMatrix.Inverse.IntegralSymplecticRows.Gaussian)) (pq row
      column)).trans (LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_delta row column))
  refine ⟨?_, ?_, ?_⟩
  · intro row column
    have equal := SquareMatrix.Inverse.SymplecticBlockIdentities.first_row_wedges gp gq gr gs gpp gqq gpq row column
    simp only [-eq_self, -iff_self, gp, gq, SquareMatrix.matrixOfFn_apply] at equal
    exact LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_injective
      ((LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).trans (equal.trans
      Ring.IntCast.cast_zero.symm))
  · intro row column
    have equal := SquareMatrix.Inverse.SymplecticBlockIdentities.last_row_wedges gp gq gr gs gpp gqq gpq row column
    simp only [-eq_self, -iff_self, gr, gs, SquareMatrix.matrixOfFn_apply] at equal
    exact LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_injective
      ((LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).trans (equal.trans
      Ring.IntCast.cast_zero.symm))
  · intro row column
    have equal := SquareMatrix.Inverse.SymplecticBlockIdentities.mixed_row_wedges gp gq gr gs gpp gqq gpq row column
    simp only [-eq_self, -iff_self, gp, gq, gr, gs, SquareMatrix.matrixOfFn_apply] at equal
    exact LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_injective
      ((LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_wedge _ _ _ _).trans (equal.trans
      (LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows.cast_delta row column).symm))

end Purelib.LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows
