module
-- Exposed integer powers retain the owned executable monoid.
public import Purelib.Algebra.Monoid.Int
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Arithmetic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite-order rational rotations

Finite order is supplied by an explicit positive exponent and a checked
finite matrix-power equation.  The trace calculation below is a direct
three-coordinate Cayley--Hamilton recurrence.  It forms no collection of all
torsion rotations and uses neither complex roots nor cyclotomic polynomials.
-/

namespace Purelib.NumberTheory.Recurrence.RationalLucas

namespace RotationOrder

/-- The finite Lucas trace recurrence for the quadratic factor
`X^2 - trace*X + 1`. -/
def traceLucas : Nat → Fraction.Rational →
  Fraction.Rational
  | 0, _trace => 2
  | 1, trace => trace
  | index + 2, trace =>
      trace * traceLucas (index + 1) trace -
        traceLucas index trace

section
open Purelib.NumberTheory
/-- The zeroth rational Lucas trace is two. -/
@[simp] theorem traceLucas_zero (trace :
  Fraction.Rational) :
    traceLucas 0 trace = 2 := rfl

/-- The first rational Lucas value is the supplied trace. -/
@[simp] theorem traceLucas_one (trace :
  Fraction.Rational) :
    traceLucas 1 trace = trace := rfl

/-- Successive rational Lucas values satisfy the quadratic trace recurrence. -/
theorem traceLucas_succ_succ (index : Nat) (trace :
  Fraction.Rational) :
    traceLucas (index + 2) trace =
      trace * traceLucas (index + 1) trace -
        traceLucas index trace :=
  rfl

/-- The second rational Lucas trace is the trace squared minus two. -/
theorem traceLucas_two (trace : Fraction.Rational) :
    traceLucas 2 trace = trace ^ 2 - 2 := by
  rw [show 2 = 0 + 2 by decide, traceLucas_succ_succ]
  simp only [traceLucas_zero]
  change trace * trace - 2 = trace ^ 2 - 2
  ring1

/-- The quadratic Lucas recurrence also satisfies the displayed third-order relation. -/
theorem traceLucas_third (index : Nat) (trace :
  Fraction.Rational) :
    traceLucas (index + 3) trace =
      (trace + 1) * traceLucas (index + 2) trace -
        (trace + 1) * traceLucas (index + 1) trace +
          traceLucas index trace := by
  rw [show index + 3 = (index + 1) + 2 by omega,
    traceLucas_succ_succ,
      traceLucas_succ_succ]
  ring1

/-! ## Direct finite denominator clearance -/

end

/-- Integer homogeneous form of `traceLucas`.  Its two cached inputs are the
numerator and denominator of one displayed canonical rational; no polynomial
root collection is formed. -/
def homogeneousTraceLucas (numerator : Int)
  (denominator : Nat) : Nat → Int
  | 0 => 2
  | 1 => numerator
  | index + 2 =>
      numerator * homogeneousTraceLucas numerator denominator (index + 1) -
        Int.pow (denominator : Int) 2 *
          homogeneousTraceLucas numerator denominator index

/-- The zeroth homogeneous integer Lucas value is two. -/
@[simp] theorem homogeneousTraceLucas_zero (numerator
  : Int)
    (denominator : Nat) :
    homogeneousTraceLucas numerator denominator 0 = 2 := rfl

/-- The first homogeneous integer Lucas value is the supplied numerator. -/
@[simp] theorem homogeneousTraceLucas_one (numerator
  : Int)
    (denominator : Nat) :
    homogeneousTraceLucas numerator denominator 1 = numerator := rfl

/-- The homogeneous recurrence scales its previous term by the numerator and its older term by the denominator squared.
-/
theorem homogeneousTraceLucas_succ_succ (numerator :
  Int)
    (denominator : Nat) (index : Nat) :
    homogeneousTraceLucas numerator denominator (index + 2) =
      numerator * homogeneousTraceLucas numerator denominator (index + 1) -
        (denominator : Int) ^ 2 *
          homogeneousTraceLucas numerator denominator index := rfl

open Purelib.NumberTheory
/-- Clearing the one canonical denominator commutes with the finite trace
recurrence. -/
theorem homogeneousTraceLucas_cast (trace :
  Fraction.Rational)
    (numerator : Int) (denominator : Nat)
    (cleared : trace * (denominator : Fraction.Rational) = (numerator : Fraction.Rational)) :
    ∀ exponent : Nat,
      (homogeneousTraceLucas numerator denominator exponent : Fraction.Rational) =
        (denominator : Fraction.Rational) ^ exponent * traceLucas exponent trace
          := open Purelib.Algebra in by
  intro exponent
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · simp only [-eq_self, -iff_self, homogeneousTraceLucas_zero,
          traceLucas_zero, pow_zero,
          one_mul, Int.cast_ofNat]
        rfl
      · rw [show 0 + 1 = 1 by decide, homogeneousTraceLucas_one,
          traceLucas_one, pow_one]
        calc
          (numerator : Fraction.Rational) = trace * (denominator : Fraction.Rational) :=
            cleared.symm
          _ = (denominator : Fraction.Rational) * trace := by ring1
      · have previous := inductionHypothesis index (by clear inductionHypothesis; omega)
        have next := inductionHypothesis (index + 1) (by clear inductionHypothesis; omega)
        rw [homogeneousTraceLucas_succ_succ,
          traceLucas_succ_succ,
          Ring.IntCast.sub, Ring.IntCast.intCast_mul,
          Ring.IntCast.intCast_mul, Ring.IntCast.intCast_pow,
          Int.cast_natCast, previous, next]
        rw [show index + 2 = (index + 1) + 1 by omega,
          pow_succ, pow_succ]
        rw [← cleared]
        ring1

/-- Modulo the displayed denominator, every positive homogeneous Lucas value
is the corresponding numerator power.  This is a finite induction on the
supplied exponent. -/
theorem denominator_dvd_homogeneousTraceLucas_sub_pow
    (numerator : Int) (denominator : Nat) :
    ∀ exponent : Nat, 0 < exponent →
      (denominator : Int) ∣
        homogeneousTraceLucas numerator denominator exponent -
          numerator ^ exponent := by
  intro exponent positive
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · clear inductionHypothesis
        exfalso
        omega
      · refine ⟨0, ?_⟩
        rw [show 0 + 1 = 1 by decide, homogeneousTraceLucas_one, pow_one]
        ring1
      · rcases inductionHypothesis (index + 1)
          (by
            clear inductionHypothesis; omega)
          (by
            clear inductionHypothesis; omega) with ⟨factor, factorEquation⟩
        have nextEquation :
            homogeneousTraceLucas numerator denominator (index + 1) =
              numerator ^ (index + 1) + (denominator : Int) * factor := by
          calc
            homogeneousTraceLucas numerator denominator (index + 1) =
                (homogeneousTraceLucas numerator denominator (index + 1) -
                    numerator ^ (index + 1)) +
                  numerator ^ (index + 1) := by ring1
            _ = (denominator : Int) * factor +
                numerator ^ (index + 1) := by rw [factorEquation]
            _ = numerator ^ (index + 1) +
                (denominator : Int) * factor := by ring1
        refine ⟨numerator * factor -
          (denominator : Int) *
            homogeneousTraceLucas numerator denominator index, ?_⟩
        rw [homogeneousTraceLucas_succ_succ, nextEquation]
        rw [show index + 2 = (index + 1) + 1 by omega, pow_succ]
        ring1

end RotationOrder

end Purelib.NumberTheory.Recurrence.RationalLucas

end
