module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Finite-order rational rotations

Finite order is supplied by an explicit positive exponent and a checked
finite matrix-power equation.  The trace calculation below is a direct
three-coordinate Cayley--Hamilton recurrence.  It forms no collection of all
torsion rotations and uses neither complex roots nor cyclotomic polynomials.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Rational.Powers

namespace RotationOrder

/-- Fixed-coordinate matrix powers, kept separate from the proof-carrying
rotation wrapper so recurrence evaluation does not unfold certificates. -/
def matrixPow (matrix : Coordinates3.Matrix3
  Fraction.Rational) : Nat → Coordinates3.Matrix3 Fraction.Rational
  | 0 => Coordinates3.Matrix3.identity
  | exponent + 1 => Coordinates3.Matrix3.mul (matrixPow
    matrix exponent) matrix

/-- The zeroth displayed matrix power is the identity. -/
@[simp] theorem matrixPow_zero (matrix :
  Coordinates3.Matrix3 Fraction.Rational) :
    matrixPow matrix 0 = Coordinates3.Matrix3.identity := rfl

/-- A successor power appends one multiplication by the original matrix. -/
@[simp] theorem matrixPow_succ (matrix :
  Coordinates3.Matrix3 Fraction.Rational) (exponent : Nat) :
    matrixPow matrix (exponent + 1) =
      Coordinates3.Matrix3.mul (matrixPow matrix exponent) matrix := rfl

/-- Adding exponents multiplies the corresponding displayed matrix powers. -/
theorem matrixPow_add (matrix :
  Coordinates3.Matrix3 Fraction.Rational) (left : Nat) :
    ∀ right : Nat,
      matrixPow matrix (left + right) =
        Coordinates3.Matrix3.mul (matrixPow matrix left)
          (matrixPow matrix right)
  | 0 => by
    rw [Nat.add_zero, matrixPow_zero, Coordinates3.Matrix3.mul_identity]
  | right + 1 => by
      rw [Nat.add_succ, matrixPow_succ,
        matrixPow_succ,
        matrixPow_add matrix left right,
          Coordinates3.Matrix3.mul_assoc]

/-- The first power is the original displayed matrix. -/
theorem matrixPow_one (matrix :
  Coordinates3.Matrix3 Fraction.Rational) :
    matrixPow matrix 1 = matrix := by
  rw [show 1 = 0 + 1 by decide, matrixPow_succ,
    matrixPow_zero,
    Coordinates3.Matrix3.identity_mul]

/-- The second power is the matrix multiplied by itself. -/
theorem matrixPow_two (matrix :
  Coordinates3.Matrix3 Fraction.Rational) :
    matrixPow matrix 2 = Coordinates3.Matrix3.mul matrix matrix := by
  rw [show 2 = 1 + 1 by decide, matrixPow_succ,
    matrixPow_one]

/-- The third power is the displayed product of three copies of the matrix. -/
theorem matrixPow_three (matrix :
  Coordinates3.Matrix3 Fraction.Rational) :
    matrixPow matrix 3 = Coordinates3.Matrix3.mul (Coordinates3.Matrix3.mul
      matrix matrix) matrix := by
  rw [show 3 = 2 + 1 by decide, matrixPow_succ,
    matrixPow_two]

end RotationOrder

end Purelib.LinearAlgebra.Coordinates3.Rational.Powers

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.Data.Rat
namespace Purelib.LinearAlgebra.Coordinates3.Matrix3

/-- The trace of a displayed matrix difference is the difference of the traces. -/
public theorem trace_sub_rational (left
  right : Coordinates3.Matrix3 Fraction.Rational) :
    Coordinates3.Matrix3.trace (Coordinates3.Matrix3.sub left right) =
      Coordinates3.Matrix3.trace left - Coordinates3.Matrix3.trace right := by
  unfold Coordinates3.Matrix3.trace Coordinates3.Matrix3.sub
  ring1

end Purelib.LinearAlgebra.Coordinates3.Matrix3
end
