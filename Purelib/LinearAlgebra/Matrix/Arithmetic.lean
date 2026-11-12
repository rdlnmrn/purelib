module

public import Purelib.Algebra.Ring.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Fin

/-!
# Scalar arithmetic and finite powers of structural matrices

Every operation materializes the original dimension-indexed matrix container.
The scalar readback laws and finite power identities use the original finite
matrix product; no function extensionality or ambient matrix ring is needed.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Arithmetic

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- The structural matrix with every retained entry zero. -/
@[expose] def zero : SquareMatrix K dimension := matrixOfFn fun _ _ => 0

/-- Add the entries at the same original row and column. -/
@[expose] def add (left right : SquareMatrix K dimension) : SquareMatrix K dimension :=
  matrixOfFn fun row column => left row column + right row column

/-- Negate every retained scalar entry. -/
@[expose] def neg (matrix : SquareMatrix K dimension) : SquareMatrix K dimension :=
  matrixOfFn fun row column => -matrix row column

/-- Multiply every retained scalar entry by the same coefficient. -/
@[expose] def scale (coefficient : K) (matrix : SquareMatrix K dimension) : SquareMatrix K dimension :=
  matrixOfFn fun row column => coefficient * matrix row column

/-- Reading the zero matrix returns the scalar zero at each original coordinate. -/
theorem zero_apply (row column : Fin dimension) : (zero : SquareMatrix K dimension) row column = 0 :=
  matrixOfFn_apply _ row column

/-- Entrywise addition reads the same two original scalar entries. -/
theorem add_apply (left right : SquareMatrix K dimension) (row column : Fin dimension) :
    add left right row column = left row column + right row column := matrixOfFn_apply _ row column

/-- Entrywise negation reads the negative of the same original scalar. -/
theorem neg_apply (matrix : SquareMatrix K dimension) (row column : Fin dimension) :
    neg matrix row column = -matrix row column := matrixOfFn_apply _ row column

/-- Scalar multiplication reads the same original scalar with its retained coefficient. -/
theorem scale_apply (coefficient : K) (matrix : SquareMatrix K dimension) (row column : Fin dimension) :
    scale coefficient matrix row column = coefficient * matrix row column := matrixOfFn_apply _ row column

/-- Addition of structural matrices is associative by their original scalar entries. -/
theorem add_assoc (first second third : SquareMatrix K dimension) :
    add (add first second) third = add first (add second third) := by
  apply matrix_ext
  intro row column
  rewrite [add_apply, add_apply, add_apply, add_apply]
  exact _root_.add_assoc _ _ _

/-- A zero left summand preserves the same structural matrix. -/
theorem zero_add (matrix : SquareMatrix K dimension) : add zero matrix = matrix := by
  apply matrix_ext
  intro row column
  rewrite [add_apply, zero_apply]
  exact _root_.zero_add _

/-- Negating and adding the same matrix gives the structural zero matrix. -/
theorem neg_add_cancel (matrix : SquareMatrix K dimension) : add (neg matrix) matrix = zero := by
  apply matrix_ext
  intro row column
  rewrite [add_apply, neg_apply, zero_apply]
  exact _root_.neg_add_cancel _

/-- The original matrix product distributes over an entrywise sum on the right. -/
theorem mul_add (factor left right : SquareMatrix K dimension) :
    Multiplication.mul factor (add left right) =
      add (Multiplication.mul factor left) (Multiplication.mul factor right) := by
  apply matrix_ext
  intro row column
  rewrite [Multiplication.mul_apply, add_apply, Multiplication.mul_apply, Multiplication.mul_apply,
    ← sumFin_add]
  apply sumFin_congr
  intro middle
  rewrite [add_apply]
  exact _root_.mul_add _ _ _

/-- The original matrix product distributes over an entrywise sum on the left. -/
theorem add_mul (left right factor : SquareMatrix K dimension) :
    Multiplication.mul (add left right) factor =
      add (Multiplication.mul left factor) (Multiplication.mul right factor) := by
  apply matrix_ext
  intro row column
  rewrite [Multiplication.mul_apply, add_apply, Multiplication.mul_apply, Multiplication.mul_apply,
    ← sumFin_add]
  apply sumFin_congr
  intro middle
  rewrite [add_apply]
  exact _root_.add_mul _ _ _

/-- A retained scalar factor passes through the left matrix input. -/
theorem scale_mul (coefficient : K) (left right : SquareMatrix K dimension) :
    Multiplication.mul (scale coefficient left) right = scale coefficient (Multiplication.mul left right) := by
  apply matrix_ext
  intro row column
  rewrite [Multiplication.mul_apply, scale_apply, Multiplication.mul_apply, ← sumFin_mul_left]
  apply sumFin_congr
  intro middle
  rewrite [scale_apply]
  exact _root_.mul_assoc _ _ _

/-- A retained scalar factor passes through the right matrix input over the commutative coefficient ring. -/
theorem mul_scale (left : SquareMatrix K dimension) (coefficient : K) (right : SquareMatrix K dimension) :
    Multiplication.mul left (scale coefficient right) = scale coefficient (Multiplication.mul left right) := by
  apply matrix_ext
  intro row column
  rewrite [Multiplication.mul_apply, scale_apply, Multiplication.mul_apply, ← sumFin_mul_left]
  apply sumFin_congr
  intro middle
  rewrite [scale_apply]
  exact (_root_.mul_left_comm _ _ _)

/-- Compute one finite natural matrix power with the original structural product. -/
@[expose] def power (matrix : SquareMatrix K dimension) : Nat → SquareMatrix K dimension
  | 0 => Multiplication.scaleIdentity 1
  | exponent + 1 => Multiplication.mul (power matrix exponent) matrix

/-- The zero power is the retained scalar identity at one. -/
theorem power_zero (matrix : SquareMatrix K dimension) : power matrix 0 = Multiplication.scaleIdentity 1 := rfl

/-- A successor power multiplies the retained preceding power by the original matrix. -/
theorem power_succ (matrix : SquareMatrix K dimension) (exponent : Nat) :
    power matrix (exponent + 1) = Multiplication.mul (power matrix exponent) matrix := rfl

/-- Splitting a finite exponent composes the two powers of the same original matrix. -/
theorem power_add (matrix : SquareMatrix K dimension) (left right : Nat) :
    power matrix (left + right) = Multiplication.mul (power matrix left) (power matrix right) := by
  induction right with
  | zero => exact (Multiplication.mul_unit _).symm
  | succ right previous =>
      change Multiplication.mul (power matrix (left + right)) matrix = _
      rewrite [previous, power_succ, Multiplication.mul_assoc]
      rfl

/-- Two finite powers of the same original matrix commute. -/
theorem power_commute (matrix : SquareMatrix K dimension) (left right : Nat) :
    Multiplication.mul (power matrix left) (power matrix right) =
      Multiplication.mul (power matrix right) (power matrix left) :=
  (power_add matrix left right).symm.trans
    ((congrArg (power matrix) (Nat.add_comm left right)).trans (power_add matrix right left))

/-- Commuting with the original generator implies commuting with every finite power. -/
theorem commute_power (matrix generator : SquareMatrix K dimension)
    (commutes : Multiplication.mul matrix generator = Multiplication.mul generator matrix) (exponent : Nat) :
    Multiplication.mul matrix (power generator exponent) = Multiplication.mul (power generator exponent) matrix := by
  induction exponent with
  | zero => exact (Multiplication.mul_unit matrix).trans (Multiplication.unit_mul matrix).symm
  | succ exponent previous =>
      rewrite [power_succ, ← Multiplication.mul_assoc, previous, Multiplication.mul_assoc,
        commutes, ← Multiplication.mul_assoc]
      rfl

/-- Transposition preserves each finite power of the same original structural matrix. -/
theorem transpose_power (matrix : SquareMatrix K dimension) (exponent : Nat) :
    Rectangular.transpose (power matrix exponent) = power (Rectangular.transpose matrix) exponent := by
  induction exponent with
  | zero =>
      apply matrix_ext
      intro row column
      rewrite [power_zero, power_zero, Rectangular.transpose_apply,
        Multiplication.scaleIdentity_apply, Multiplication.scaleIdentity_apply]
      by_cases same : row = column
      · rewrite [if_pos same, if_pos same.symm]
        rfl
      · rewrite [if_neg same, if_neg (fun reverse => same reverse.symm)]
        rfl
  | succ exponent previous =>
      change Rectangular.transpose (Rectangular.mul (power matrix exponent) matrix) = _
      rewrite [Rectangular.transpose_mul, previous, power_succ]
      exact commute_power (Rectangular.transpose matrix) (Rectangular.transpose matrix) rfl exponent

/-- Retain successive generator products, consuming each completed matrix as the next cached state. -/
@[expose] def powersFrom (generator : SquareMatrix K dimension) :
    (count : Nat) → SquareMatrix K dimension → Purelib.Data.Vector (SquareMatrix K dimension) count
  | 0, _ => .nil
  | count + 1, current => .cons current (powersFrom generator count (Multiplication.mul current generator))

/-- The retained successive-product table reads the same original finite generator exponent. -/
theorem powersFrom_apply (generator : SquareMatrix K dimension) (count exponent : Nat) (index : Fin count) :
    powersFrom generator count (power generator exponent) index = power generator (exponent + index.val) := by
  induction count generalizing exponent with
  | zero => exact Fin.elim0 index
  | succ count previous =>
      refine Fin.cases rfl ?_ index
      intro next
      change powersFrom generator count (power generator (exponent + 1)) next =
        power generator (exponent + (next.val + 1))
      have exponents : exponent + 1 + next.val = exponent + (next.val + 1) :=
        (Nat.add_assoc exponent 1 next.val).trans (congrArg (fun value => exponent + value) (Nat.add_comm 1 next.val))
      exact (previous (exponent + 1) next).trans (congrArg (power generator) exponents)

/-- Compute and retain the initial finite powers with one successive-product traversal. -/
@[expose] def powerTable (generator : SquareMatrix K dimension) (count : Nat) :
    Purelib.Data.Vector (SquareMatrix K dimension) count := powersFrom generator count (Multiplication.scaleIdentity 1)

/-- Every retained initial power has its actual original bounded exponent. -/
theorem powerTable_apply (generator : SquareMatrix K dimension) (count : Nat) (index : Fin count) :
    powerTable generator count index = power generator index.val :=
  (powersFrom_apply generator count 0 index).trans (congrArg (power generator) (Nat.zero_add index.val))

end Purelib.LinearAlgebra.Matrix.Arithmetic

end
