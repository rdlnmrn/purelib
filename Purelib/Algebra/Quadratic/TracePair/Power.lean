module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.TracePair.Basic
public import Purelib.Algebra.Quadratic.TracePair.Norm
public import Purelib.Polynomial.Recurrence.Lucas.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Quadratic (TracePair)

section
public section

/-!
# Finite powers of the quadratic trace generator

Natural-number recursion retains both coordinates of each generator power
at the displayed trace parameter. The original second-order recurrence
identifies its trace with the finite Lucas recurrence, and its quadratic
norm is one. Subtracting the unit pair gives norm two minus that Lucas value.
-/

namespace Purelib.Algebra.Quadratic.TracePair

variable {K : Type*} [ExplicitField K]

/-- Compute finite powers of the formal quadratic generator.

Recursion starts with the unit pair and repeatedly multiplies by the generator using the supplied trace parameter. -/
@[expose] def alphaPower : Nat → K → TracePair K
  | 0, _ => one
  | exponent + 1, trace => mul trace alpha (alphaPower exponent
    trace)

/-- The zeroth generator power is the unit pair. -/
@[simp] theorem alphaPower_zero (trace : K) :
    alphaPower 0 trace = one := rfl

/-- A successor generator power multiplies the previous power by the generator. -/
@[simp] theorem alphaPower_succ (exponent : Nat) (trace : K) :
    alphaPower (exponent + 1) trace =
      mul trace alpha (alphaPower exponent trace) := rfl

/-- Two generator multiplications satisfy the quadratic trace relation.

The resulting pair is trace times one generator multiplication minus the original pair. -/
theorem alpha_square_action (trace : K) (pair : TracePair K) :
    mul trace alpha (mul trace alpha pair) =
      sub (scale trace (mul trace alpha pair)) pair := by
  apply ext <;> simp only [mul, alpha, sub, scale] <;> ring0

/-- Generator powers satisfy the second-order trace recurrence.

Each power two steps later equals trace times the successor power minus the current power. -/
theorem alphaPower_succ_succ (index : Nat) (trace : K) :
    alphaPower (index + 2) trace =
      sub (scale trace (alphaPower (index + 1) trace))
        (alphaPower index trace) := by
  rw [show index + 2 = (index + 1) + 1 by omega0,
    alphaPower_succ, alphaPower_succ, alpha_square_action]

/-- The trace of a generator power is the corresponding Lucas value.

Both finite recurrences use the same trace parameter and natural index. -/
theorem traceValue_alphaPower : ∀ index : Nat, ∀ trace : K,
    traceValue trace (alphaPower index trace) = lucas index trace
  | 0, trace => by simp only [traceValue, alphaPower, one, lucas, -eq_self, -iff_self]; ring0
  | 1, trace => by simp only [traceValue, alphaPower, one, alpha, mul, lucas, -eq_self, -iff_self]; ring0
  | index + 2, trace => by
      rw [alphaPower_succ_succ, traceValue_sub, traceValue_scale,
        traceValue_alphaPower (index + 1) trace,
        traceValue_alphaPower index trace, lucas]

/-- The formal quadratic generator has norm one. -/
theorem norm_alpha (trace : K) : norm trace alpha = 1 := by
  simp only [norm, alpha, -eq_self, -iff_self]
  ring0

/-- Every finite power of the quadratic generator has norm one.

The exponent is a natural number and the norm uses the same trace parameter as the power. -/
theorem norm_alphaPower : ∀ exponent : Nat, ∀ trace : K,
    norm trace (alphaPower exponent trace) = 1
  | 0, trace => by simp only [alphaPower, one, norm, -eq_self, -iff_self]; ring0
  | exponent + 1, trace => by
      rw [alphaPower_succ, norm_mul, norm_alpha,
        norm_alphaPower exponent trace, one_mul]

/-- The norm of a generator power minus one is two minus its Lucas value.

The exponent and trace parameter agree in the finite power, norm, and Lucas recurrence. -/
theorem norm_alphaPower_sub_one (exponent : Nat) (trace : K) :
    norm trace (sub (alphaPower exponent trace) one) =
      2 - lucas exponent trace := by
  rw [norm_sub_one, norm_alphaPower, traceValue_alphaPower]
  ring0

end Purelib.Algebra.Quadratic.TracePair

end
