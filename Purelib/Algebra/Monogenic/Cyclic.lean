module

public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cyclic structural matrices and exact coefficient reconstruction

A retained power table sends one original coordinate to each coordinate unit
vector. Every matrix commuting with that generator reconstructs from its
original distinguished column. The argument uses only finite scalar sums.
-/

public section

namespace Purelib.Algebra.Monogenic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] {dimension : Nat}

set_option genInjectivity false in
/-- An original matrix whose retained powers generate the coordinate units from one retained column.

The power table is cached as structural matrix data. Its specification ties
each retained entry to the same original generator and natural exponent.
-/
structure Cyclic (generator : SquareMatrix K dimension) where
  /-- The original coordinate whose iterates generate all coordinate units. -/
  origin : Fin dimension
  /-- The same original generator's retained table of the first powers. -/
  powers : Purelib.Data.Vector (SquareMatrix K dimension) dimension
  /-- Each retained power has its actual original exponent. -/
  powers_eq : ∀ index, powers index = Arithmetic.power generator index.val
  /-- The distinguished column of each retained power is its original coordinate unit. -/
  coordinate : ∀ index row, powers index row origin = if row = index then 1 else 0

constructive_injectivity Cyclic

namespace Cyclic

variable {generator : SquareMatrix K dimension}

/-- Multiplying the distinguished column of a cached power reads the corresponding original matrix column. -/
theorem mul_power_column (cyclic : Cyclic generator) (matrix : SquareMatrix K dimension)
    (index row : Fin dimension) :
    Multiplication.mul matrix (cyclic.powers index) row cyclic.origin = matrix row index := by
  rewrite [Multiplication.mul_apply]
  calc
    _ = sumFin (fun middle => if middle = index then matrix row middle else 0) := by
      apply sumFin_congr
      intro middle
      rewrite [cyclic.coordinate index middle]
      by_cases same : middle = index
      · rewrite [if_pos same, if_pos same, mul_one]
        rfl
      · rewrite [if_neg same, if_neg same, mul_zero]
        rfl
    _ = matrix row index := sumFin_ite_eq index (fun middle => matrix row middle)

/-- The cached power entries interchange their exponent and input-column indices.

Both readings are the distinguished column of the same product of powers.
Their original natural exponents commute under addition.
-/
theorem power_symmetry (cyclic : Cyclic generator) (left right row : Fin dimension) :
    cyclic.powers left row right = cyclic.powers right row left := by
  have commutes : Multiplication.mul (cyclic.powers left) (cyclic.powers right) =
      Multiplication.mul (cyclic.powers right) (cyclic.powers left) := by
    rewrite [cyclic.powers_eq left, cyclic.powers_eq right]
    exact Arithmetic.power_commute generator left.val right.val
  exact (cyclic.mul_power_column (cyclic.powers left) right row).symm.trans
    ((matrix_eq_at commutes row cyclic.origin).trans (cyclic.mul_power_column (cyclic.powers right) left row))

/-- A matrix commuting with the original generator commutes with each same retained power. -/
theorem commute_power (cyclic : Cyclic generator) (matrix : SquareMatrix K dimension)
    (commutes : Multiplication.mul matrix generator = Multiplication.mul generator matrix)
    (index : Fin dimension) :
    Multiplication.mul matrix (cyclic.powers index) = Multiplication.mul (cyclic.powers index) matrix := by
  rewrite [cyclic.powers_eq index]
  exact Arithmetic.commute_power matrix generator commutes index.val

/-- Every commuting matrix entry is determined by the same original distinguished column and cached powers. -/
theorem reconstruct_entry (cyclic : Cyclic generator) (matrix : SquareMatrix K dimension)
    (commutes : Multiplication.mul matrix generator = Multiplication.mul generator matrix)
    (row column : Fin dimension) :
    matrix row column = sumFin (fun index => matrix index cyclic.origin * cyclic.powers index row column) := by
  calc
    matrix row column = Multiplication.mul matrix (cyclic.powers column) row cyclic.origin :=
      (cyclic.mul_power_column matrix column row).symm
    _ = Multiplication.mul (cyclic.powers column) matrix row cyclic.origin :=
      matrix_eq_at (cyclic.commute_power matrix commutes column) row cyclic.origin
    _ = sumFin (fun index => cyclic.powers column row index * matrix index cyclic.origin) :=
      Multiplication.mul_apply _ _ row cyclic.origin
    _ = _ := by
      apply sumFin_congr
      intro index
      rewrite [cyclic.power_symmetry column index row]
      exact mul_comm _ _

/-- Two matrices commuting with a cyclic generator commute with one another.

The original distinguished columns give finite polynomial coordinate
reconstructions. Finite sum exchange and the cached power commutations
compare their two actual structural products.
-/
theorem commuting_pair (cyclic : Cyclic generator) (left right : SquareMatrix K dimension)
    (leftCommutes : Multiplication.mul left generator = Multiplication.mul generator left)
    (rightCommutes : Multiplication.mul right generator = Multiplication.mul generator right) :
    Multiplication.mul left right = Multiplication.mul right left := by
  apply matrix_ext
  intro row column
  calc
    Multiplication.mul left right row column =
        sumFin (fun middle => left row middle * right middle column) :=
      Multiplication.mul_apply _ _ row column
    _ = sumFin (fun middle => sumFin (fun index =>
        right index cyclic.origin * (left row middle * cyclic.powers index middle column))) := by
      apply sumFin_congr
      intro middle
      rewrite [cyclic.reconstruct_entry right rightCommutes middle column, ← sumFin_mul_left]
      apply sumFin_congr
      intro index
      exact (mul_left_comm _ _ _)
    _ = sumFin (fun index => sumFin (fun middle =>
        right index cyclic.origin * (left row middle * cyclic.powers index middle column))) := sumFin_swap _
    _ = sumFin (fun index => right index cyclic.origin *
        Multiplication.mul left (cyclic.powers index) row column) := by
      apply sumFin_congr
      intro index
      rewrite [sumFin_mul_left, Multiplication.mul_apply]
      rfl
    _ = sumFin (fun index => right index cyclic.origin *
        Multiplication.mul (cyclic.powers index) left row column) := by
      apply sumFin_congr
      intro index
      exact congrArg (fun value => right index cyclic.origin * value)
        (matrix_eq_at (cyclic.commute_power left leftCommutes index) row column)
    _ = sumFin (fun index => sumFin (fun middle =>
        right index cyclic.origin * (cyclic.powers index row middle * left middle column))) := by
      apply sumFin_congr
      intro index
      rewrite [Multiplication.mul_apply, sumFin_mul_left]
      rfl
    _ = sumFin (fun middle => sumFin (fun index =>
        right index cyclic.origin * (cyclic.powers index row middle * left middle column))) := sumFin_swap _
    _ = sumFin (fun middle => right row middle * left middle column) := by
      apply sumFin_congr
      intro middle
      rewrite [cyclic.reconstruct_entry right rightCommutes row middle, ← sumFin_mul_right]
      apply sumFin_congr
      intro index
      exact (mul_assoc _ _ _).symm
    _ = Multiplication.mul right left row column := (Multiplication.mul_apply _ _ row column).symm

end Cyclic

end Purelib.Algebra.Monogenic

end
