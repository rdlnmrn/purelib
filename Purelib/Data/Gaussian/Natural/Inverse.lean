module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
public import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Natural
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Cast.Order

import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite antiderivatives of dense Gaussian polynomials

Connect the existing low-to-high polynomial integrator to the dense
high-to-low polynomial algebra.  The derivative identity is proved by finite
Horner induction.  The existing finite Taylor estimate then bounds local
primitive increments, without analytic limits or infinite series.
-/

namespace Purelib.Data.Gaussian.Natural.Inverse

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The canonical Gaussian cast of a natural successor is nonzero. -/
public theorem nat_succ_nonzero (degree : Nat) : ((degree + 1 : Nat) :
  Basic.Canonical) ≠ 0 := by
  intro zero
  have realZero := congrArg (fun value : Basic.Canonical => value.re) zero
  rw [Cast.natCast_re, Basic.zero_re] at realZero
  exact (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ degree)).ne' realZero

end Purelib.Data.Gaussian.Natural.Inverse

end

section
@[expose] public section

/-!
# Coefficient algebra for finite Gaussian polynomial integration

All equalities are proved from finite coefficient lists.  In particular,
coefficient equality is not obtained by testing a polynomial on an infinite
carrier.  This small layer supplies the algebraic FTC used by generated path
subdivisions; it adds no analytic or antiderivative certificate assumptions.
-/

namespace Purelib.Data.Gaussian.Natural.Inverse

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The canonical Gaussian cast of a natural successor is nonzero. -/
private theorem positiveDegree_nonzero (degree : Nat) :
    ((degree + 1 : Nat) : Basic.Canonical) ≠ 0 := by
  intro equal
  have realEqual := congrArg Basic.re equal
  simp only [Cast.natCast_re, Basic.zero_re] at realEqual
  exact (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ degree)).ne'
    realEqual

open Purelib.Algebra
open Purelib.Data.Gaussian
/-- Multiplying a Gaussian divided by a natural successor by that successor recovers the original value. -/
public theorem positiveDegree_cancel (degree : Nat) (value :
  Basic.Canonical) :
    ((degree + 1 : Nat) : Basic.Canonical) *
      (value / ((degree + 1 : Nat) : Basic.Canonical)) = value := by
  rw [_root_.mul_comm]
  exact Field.ExplicitField.div_mul_cancel value (positiveDegree_nonzero degree)

/-- Dividing a natural-successor multiple of a Gaussian by the same successor recovers the original value. -/
public theorem positiveDegree_div_cancel (degree : Nat) (value :
  Basic.Canonical) :
    (((degree + 1 : Nat) : Basic.Canonical) * value) /
      ((degree + 1 : Nat) : Basic.Canonical) = value := by
  rw [_root_.Purelib.Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    (((degree + 1 : Nat) : Basic.Canonical) * value) *
        ((degree + 1 : Nat) : Basic.Canonical)⁻¹ =
        value * (((degree + 1 : Nat) : Basic.Canonical) *
          ((degree + 1 : Nat) : Basic.Canonical)⁻¹) := by ring1
    _ = value := by
      rw [Field.ExplicitField.mul_inv_cancel _ (positiveDegree_nonzero degree), _root_.mul_one]

end Purelib.Data.Gaussian.Natural.Inverse

end

end

section
@[expose] public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

namespace Purelib.Data.Gaussian.Natural.Inverse

open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
/-- Compute the Gaussian reciprocal of the retained positive root degree. -/
def inverseDegree (degree : Positive.RootDegree) : Basic.Canonical :=
  1 / Natural.naturalGaussian degree.value

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Nat in
/-- Adding the reciprocal degree to itself the retained positive number of times gives one. -/
theorem repeatedCoefficient_inverseDegree (degree : Positive.RootDegree) :
    Natural.repeatedCoefficient (inverseDegree degree) degree.value = 1 := by
  rw [Natural.repeatedCoefficient_eq]
  unfold inverseDegree
  rw [Field.ExplicitField.div_eq_mul_inv,
    _root_.one_mul]
  exact Basic.Canonical.mul_inv_cancel _
    (Natural.naturalGaussian_ne_zero degree)
end Purelib.Data.Gaussian.Natural.Inverse

end
