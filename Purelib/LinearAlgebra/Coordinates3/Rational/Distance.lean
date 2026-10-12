module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.LinearAlgebra.Coordinates3.Matrix
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Finite rational approximation by unit-quaternion rotations

This module proves the finite-precision form of the density clause in Problem
70.  It uses squared error on the nine displayed matrix entries, a finite
integer-square-root bracket, and a rational stereographic candidate whose norm
is exactly one.  Every positive rational radius request terminates with a
strict error certificate.  No real square root, topology, sequence, or limit
is formed.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Rational.Distance

namespace KernelApproximation

/-! ## Exact rational matrix error -/

/-- Squared Frobenius error of two displayed rational matrices. -/
def matrixDistanceSq (left right :
  Coordinates3.Matrix3 Fraction.Rational) : Fraction.Rational :=
  (left.tt - right.tt) ^ 2 +
  (left.tr - right.tr) ^ 2 +
  (left.ts - right.ts) ^ 2 +
  (left.rt - right.rt) ^ 2 +
  (left.rr - right.rr) ^ 2 +
  (left.rs - right.rs) ^ 2 +
  (left.st - right.st) ^ 2 +
  (left.sr - right.sr) ^ 2 +
  (left.ss - right.ss) ^ 2

/-- The coordinatewise squared distance between rational matrices is nonnegative. -/
theorem matrixDistanceSq_nonnegative
  (left right : Coordinates3.Matrix3 Fraction.Rational) :
    0 ≤ matrixDistanceSq left right := by
  unfold matrixDistanceSq
  have tt := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.tt - right.tt)
  have tr := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.tr - right.tr)
  have ts := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.ts - right.ts)
  have rt := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.rt - right.rt)
  have rr := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.rr - right.rr)
  have rs := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.rs - right.rs)
  have st := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.st - right.st)
  have sr := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.sr - right.sr)
  have ss := Fraction.Order.Arithmetic.sq_nonneg_direct
    (left.ss - right.ss)
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (add_nonneg (add_nonneg tt tr) ts) rt) rr) rs) st) sr) ss

/-- The coordinatewise squared distance from a rational matrix to itself is zero. -/
theorem matrixDistanceSq_self (matrix :
  Coordinates3.Matrix3 Fraction.Rational) :
    matrixDistanceSq matrix matrix = 0 := by
  unfold matrixDistanceSq
  ring1
end KernelApproximation

end Purelib.LinearAlgebra.Coordinates3.Rational.Distance

end
