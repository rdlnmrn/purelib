module

public import Purelib.Polynomial.Recurrence.Boundary.Shift
public import Purelib.LinearAlgebra.Matrix.NormalForm.Reduction
public import Purelib.LinearAlgebra.Matrix.Triangular.Inverse
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Original boundary reductions from initial reading coordinates

The actual finite startup factorization transports retained initial-reading
coordinates to the original boundary rows. Only the original constant unit
and original finite shift inverse are added; all coordinate changes use the
same original inverse records and matrix products.
-/

public section

namespace Purelib.Polynomial.Recurrence.Boundary

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Inverse.Scaled.Basic

variable {K : Type*} [CommRing K] {horizon modes : Nat}

/-- A zero shift has no original startup equations, independently of all root units or shifts. -/
@[expose] def zeroShift (polynomial : DensePolynomial K) (values : Vec (Vec K horizon) modes) :
    NormalForm (matrix polynomial 0 values) :=
  NormalForm.ofZero _ (fun row => Fin.elim0 row)

/-- An empty actual mode bank has no source columns, independently of polynomial units. -/
@[expose] def emptyColumns (polynomial : DensePolynomial K) (shift : Nat) :
    NormalForm (matrix polynomial shift (.nil : Vec (Vec K horizon) 0)) :=
  NormalForm.ofZero _ (fun _ column => Fin.elim0 column)

/-- The upper startup factor retains the original ascending coefficient at column minus row with sign minus. -/
theorem upper_at (polynomial : DensePolynomial K) (shift : Nat) (row column : Fin shift) :
    upper polynomial shift row column =
      if row.val ≤ column.val then -getD polynomial.coeffs.reverse (column.val - row.val) 0 else 0 := by
  rw [upper, Arithmetic.scale_apply, plus_at]
  unfold toeplitzEntry
  rw [Nat.add_zero]
  by_cases included : row.val ≤ column.val
  · rw [if_pos included, if_pos included]
    ring0
  · rw [if_neg included, if_neg included, mul_zero]

/-- The original upper startup factor is upper triangular at its same retained coordinates. -/
theorem upper_triangular (polynomial : DensePolynomial K) (shift : Nat) :
    Triangular.IsUpper (upper polynomial shift) := by
  intro row column before
  rw [upper_at, if_neg (by omega0)]

/-- Every original startup diagonal is minus the original constant coefficient. -/
theorem upper_diagonal (polynomial : DensePolynomial K) (shift : Nat) (index : Fin shift) :
    upper polynomial shift index index = -getD polynomial.coeffs.reverse 0 0 := by
  rw [upper_at, if_pos (Nat.le_refl _), Nat.sub_self]

/-- Transport actual initial-reading coordinates to the same original finite boundary matrix.

The original polynomial equations derive the full startup factorization.
The displayed constant inverse supplies the triangular factor's diagonal
units, while the same retained shift inverse supplies its original finite
power inverse. The initial normal form is reused through the original
coordinate pullback; no boundary rank or factorization is assumed.
-/
@[expose] def ofInitial (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (step : SquareMatrix K modes)
    (stepInverse : ScaledInverse step) (stepUnit : stepInverse.scalar = 1)
    (transition : Transition values step) (room : shift + polynomial.coeffs.reverse.length ≤ horizon)
    (equations : Equations polynomial shift values)
    (constantInverse : K) (constantUnit : getD polynomial.coeffs.reverse 0 0 * constantInverse = 1)
    (normal : NormalForm (initial values shift)) : NormalForm (matrix polynomial shift values) := by
  let factor := upper polynomial shift
  let diagonalInverses := vectorOfFn fun _ : Fin shift => -constantInverse
  let factorInverse := Triangular.inverseUpper factor (upper_triangular polynomial shift) diagonalInverses (by
    intro index
    rw [upper_diagonal, vectorOfFn_apply]
    exact (show -getD polynomial.coeffs.reverse 0 0 * -constantInverse =
      getD polynomial.coeffs.reverse 0 0 * constantInverse by ring0).trans constantUnit)
  let powered := Arithmetic.power step shift
  let poweredInverse := stepInverse.power stepUnit shift
  have factorLeft : Rectangular.mul factorInverse.val.inverse factor = Multiplication.scaleIdentity 1 :=
    factorInverse.val.left_identity.trans (congrArg Multiplication.scaleIdentity factorInverse.property)
  have originalFactor : Rectangular.mul (matrix polynomial shift values) powered =
      Rectangular.mul factor (initial values shift) :=
    factorization polynomial shift values step transition room equations
  have recovered : initial values shift =
      Rectangular.mul (Rectangular.mul factorInverse.val.inverse (matrix polynomial shift values)) powered := by
    rw [Rectangular.mul_assoc, originalFactor, ← Rectangular.mul_assoc, factorLeft, Rectangular.unit_mul]
  exact NormalForm.pullback factorInverse.val.inverse (factorInverse.val.symm factorInverse.property) rfl
    powered poweredInverse rfl recovered normal

/-- The boundary coordinate transport preserves the actual initial-reading identity-block size. -/
theorem ofInitial_rank (polynomial : DensePolynomial K) (shift : Nat)
    (values : Vec (Vec K horizon) modes) (step : SquareMatrix K modes)
    (stepInverse : ScaledInverse step) (stepUnit : stepInverse.scalar = 1)
    (transition : Transition values step) (room : shift + polynomial.coeffs.reverse.length ≤ horizon)
    (equations : Equations polynomial shift values)
    (constantInverse : K) (constantUnit : getD polynomial.coeffs.reverse 0 0 * constantInverse = 1)
    (normal : NormalForm (initial values shift)) :
    (ofInitial polynomial shift values step stepInverse stepUnit transition room equations
      constantInverse constantUnit normal).rank = normal.rank := rfl

end Purelib.Polynomial.Recurrence.Boundary

end
