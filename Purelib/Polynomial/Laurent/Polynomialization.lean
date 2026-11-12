module

public import Purelib.Polynomial.Laurent.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Power.Gaussian.Signed.Secant
import Purelib.Tactic.Ring

/-!
# Exact polynomializing shifts of finite Laurent expressions

The original ordered term list determines a sufficient natural shift. Each
term is constructed in the original descending dense polynomial owner and
addition combines repeated exponents by exact Gaussian arithmetic.
-/

namespace Purelib.Polynomial.Laurent.Basic.LaurentPolynomial

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Polynomial
open Purelib.Algebra.Power.Gaussian

/-- The largest displayed negative exponent magnitude in a finite term list. -/
@[expose] public def rawShiftTerms : List LaurentTerm → Nat
  | [] => 0
  | term :: remaining => Nat.max term.exponent.negativeMagnitude (rawShiftTerms remaining)

/-- Every displayed negative magnitude is bounded by the computed raw shift. -/
private theorem negativeMagnitude_le_rawShiftTerms :
    ∀ (terms : List LaurentTerm) (term : LaurentTerm), term ∈ terms →
      term.exponent.negativeMagnitude ≤ rawShiftTerms terms
  | [], _, member => by cases member
  | head :: remaining, term, member => by
      cases member with
      | head => exact Data.Nat.Order.le_max_left _ _
      | tail _ inTail =>
          exact (negativeMagnitude_le_rawShiftTerms remaining term inTail).trans
            (Data.Nat.Order.le_max_right _ _)

/-- The least shift sufficient for every displayed term before coefficient cancellation. -/
@[expose] public def rawShift (polynomial : LaurentPolynomial) : Nat :=
  rawShiftTerms polynomial.terms

/-- The retained raw shift polynomializes each original displayed exponent. -/
public theorem negativeMagnitude_le_rawShift (polynomial : LaurentPolynomial)
    (term : LaurentTerm) (member : term ∈ polynomial.terms) :
    term.exponent.negativeMagnitude ≤ polynomial.rawShift :=
  negativeMagnitude_le_rawShiftTerms polynomial.terms term member

/-- Construct a shifted finite term list by the original dense additions and monomial shifts. -/
@[expose] public def polynomializeTerms (shift : Nat) :
    List LaurentTerm → Dense.Basic.DensePolynomial Gaussian.Basic.Canonical
  | [] => 0
  | term :: remaining =>
      Dense.Basic.DensePolynomial.shift (term.exponent.shifted shift)
          (Dense.Basic.DensePolynomial.constant term.coefficient) +
        polynomializeTerms shift remaining

/-- Polynomialize the original ordered Laurent term list at a displayed natural shift.

The evaluator identity retains a sufficient-shift certificate. Zero coefficients
and repeated exponents are combined by the original dense addition procedure. -/
@[expose] public def polynomialize (polynomial : LaurentPolynomial) (shift : Nat) :
    Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
  polynomializeTerms shift polynomial.terms

/-- The original finite dense construction clears each guarded term's negative power. -/
private theorem eval_polynomializeTerms (point : Gaussian.Basic.Canonical) (shift : Nat) :
    ∀ (terms : List LaurentTerm),
      (∀ term ∈ terms, term.exponent.negativeMagnitude ≤ shift) →
      (∀ term ∈ terms, term.DefinedAt point) →
      (polynomializeTerms shift terms).eval point =
        point ^ shift * Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian
          (terms.map fun term => term.eval point)
  | [], _, _ => (Gaussian.Basic.mul_zero _).symm
  | term :: remaining, sufficient, defined => by
      have tailSufficient := fun next member => sufficient next (List.mem_cons_of_mem term member)
      have tailDefined := fun next member => defined next (List.mem_cons_of_mem term member)
      have powerIdentity := Signed.Secant.signedPower_shift point term.exponent shift
        (sufficient term List.mem_cons_self) (defined term List.mem_cons_self)
      rewrite [polynomializeTerms, Dense.Basic.DensePolynomial.eval_add,
        Dense.Basic.DensePolynomial.eval_shift, Dense.Basic.DensePolynomial.eval_constant,
        eval_polynomializeTerms point shift remaining tailSufficient tailDefined]
      change term.coefficient * point ^ term.exponent.shifted shift + _ =
        point ^ shift * (term.coefficient * Signed.Secant.signedPower point term.exponent + _)
      rewrite [← powerIdentity]
      ring1

/-- A sufficient polynomializing shift preserves the original expression on its retained domain. -/
public theorem eval_polynomialize (polynomial : LaurentPolynomial) (shift : Nat)
    (sufficient : polynomial.rawShift ≤ shift) (point : Gaussian.Basic.Canonical)
    (defined : polynomial.DefinedAt point) :
    (polynomial.polynomialize shift).eval point = point ^ shift * polynomial.eval point :=
  eval_polynomializeTerms point shift polynomial.terms
    (fun term member => (polynomial.negativeMagnitude_le_rawShift term member).trans sufficient) defined

/-- An original expression defined at zero has no displayed negative exponent. -/
public theorem rawShift_eq_zero_of_definedAt_zero (polynomial : LaurentPolynomial)
    (defined : polynomial.DefinedAt 0) : polynomial.rawShift = 0 := by
  have scan : ∀ (terms : List LaurentTerm),
      (∀ term ∈ terms, term.DefinedAt 0) → rawShiftTerms terms = 0 := by
    intro terms
    induction terms with
    | nil => intro _; rfl
    | cons term remaining inductionHypothesis =>
        intro guarded
        have magnitudeZero : term.exponent.negativeMagnitude = 0 := by
          cases exponent : term.exponent with
          | nonnegative degree => rfl
          | negative predecessor =>
              have guard := guarded term List.mem_cons_self
              change term.exponent.negativeMagnitude ≠ 0 → (0 : Gaussian.Basic.Canonical) ≠ 0 at guard
              rewrite [exponent] at guard
              exact (guard (Nat.succ_ne_zero predecessor) rfl).elim
        have tailZero := inductionHypothesis
          (fun next member => guarded next (List.mem_cons_of_mem term member))
        change Nat.max term.exponent.negativeMagnitude (rawShiftTerms remaining) = 0
        rewrite [magnitudeZero, tailZero]
        rfl
  exact scan polynomial.terms defined

end Purelib.Polynomial.Laurent.Basic.LaurentPolynomial
