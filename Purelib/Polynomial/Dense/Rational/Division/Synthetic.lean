module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Synthetic division of descending rational coefficients

The original recurrence retains the leading coefficient as the next quotient
entry and propagates its value at the displayed root. The final scalar is the
same Horner remainder, with a pointwise linear-factor evaluation certificate.
-/

open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Rational.Division.Synthetic

/-- Compute the synthetic quotient and remainder for a descending rational coefficient list.

The original leading coefficient is retained as each quotient entry.
The same root propagates the next leading value along the original tail,
and the final scalar is the retained Horner remainder. -/
@[expose] public def syntheticAux (root leading : Fraction.Rational) :
    List Fraction.Rational → List Fraction.Rational × Fraction.Rational
  | [] => ([], leading)
  | coefficient :: remaining =>
      let result := Purelib.Polynomial.Dense.Rational.Division.Synthetic.syntheticAux root (leading * root +
        coefficient) remaining
      (leading :: result.1, result.2)

/-- Split descending rational evaluation into its leading monomial and remaining coefficients.

The original tail length determines the leading power. Its unchanged
Horner evaluation supplies the remainder of this pointwise scalar
identity at the same displayed rational argument. -/
private theorem evalCoeffs_cons_power (x leading : Fraction.Rational)
    (remaining : List Fraction.Rational) :
    Dense.Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
      leading * x ^ remaining.length + Dense.Basic.DensePolynomial.evalCoeffs x remaining := by
  induction remaining generalizing leading with
  | nil =>
      simp only [Dense.Basic.DensePolynomial.evalCoeffs_cons, List.foldl_nil, List.length_nil, pow_zero,
        Dense.Basic.DensePolynomial.evalCoeffs_nil]
      ring1
  | cons coefficient remaining inductionHypothesis =>
      rw [Dense.Basic.DensePolynomial.evalCoeffs_cons]
      simp only [List.foldl_cons]
      rw [← Dense.Basic.DensePolynomial.evalCoeffs_cons x (leading * x + coefficient) remaining,
        inductionHypothesis (leading * x + coefficient),
        inductionHypothesis coefficient]
      simp only [List.length_cons, pow_succ]
      ring1

/-- Certify the original synthetic quotient length, remainder and linear-factor identity.

The retained quotient has exactly the original tail length. Its remainder
is evaluation at the supplied root, and each displayed argument evaluates
the original list as the same linear factor times quotient plus remainder. -/
public theorem syntheticAux_spec (root leading : Fraction.Rational)
    (remaining : List Fraction.Rational) :
    let result := Dense.Rational.Division.Synthetic.syntheticAux root leading remaining
    result.1.length = remaining.length ∧
      result.2 = Dense.Basic.DensePolynomial.evalCoeffs root (leading :: remaining) ∧
      ∀ x : Fraction.Rational,
        Dense.Basic.DensePolynomial.evalCoeffs x (leading :: remaining) =
          (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x result.1 + result.2 := by
  induction remaining generalizing leading with
  | nil =>
      constructor
      · rfl
      constructor
      · change leading = Dense.Basic.DensePolynomial.evalCoeffs root [leading]
        rw [Dense.Basic.DensePolynomial.evalCoeffs_cons]
        rfl
      · intro x
        change Dense.Basic.DensePolynomial.evalCoeffs x [leading] =
          (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x [] + leading
        rw [Dense.Basic.DensePolynomial.evalCoeffs_cons,
          Dense.Basic.DensePolynomial.evalCoeffs_nil, mul_zero, zero_add]
        rfl
  | cons coefficient remaining inductionHypothesis =>
      let nextLeading := leading * root + coefficient
      let recursive := Dense.Rational.Division.Synthetic.syntheticAux root nextLeading remaining
      have recursiveSpec := inductionHypothesis nextLeading
      change recursive.1.length = remaining.length ∧
        recursive.2 = Dense.Basic.DensePolynomial.evalCoeffs root (nextLeading :: remaining) ∧
        ∀ x : Fraction.Rational,
          Dense.Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) =
            (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2 at recursiveSpec
      change
        (leading :: recursive.1).length =
            (coefficient :: remaining).length ∧
          recursive.2 =
            Dense.Basic.DensePolynomial.evalCoeffs root (leading :: coefficient :: remaining) ∧
          ∀ x : Fraction.Rational,
            Dense.Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2
      constructor
      · simp only [List.length_cons]
        exact congrArg Nat.succ recursiveSpec.1
      constructor
      · rw [Dense.Basic.DensePolynomial.evalCoeffs_cons]
        simp only [List.foldl_cons]
        rw [← Dense.Basic.DensePolynomial.evalCoeffs_cons root nextLeading remaining]
        exact recursiveSpec.2.1
      · intro x
        have recursiveFactor := recursiveSpec.2.2 x
        calc
          Dense.Basic.DensePolynomial.evalCoeffs x (leading :: coefficient :: remaining) =
              leading * x ^ (remaining.length + 1) +
                coefficient * x ^ remaining.length +
                Dense.Basic.DensePolynomial.evalCoeffs x remaining := by
            rw [evalCoeffs_cons_power x leading (coefficient :: remaining),
              evalCoeffs_cons_power x coefficient remaining]
            simp only [List.length_cons]
            ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                Dense.Basic.DensePolynomial.evalCoeffs x (nextLeading :: remaining) := by
            rw [evalCoeffs_cons_power x nextLeading remaining, pow_succ]
            dsimp only [nextLeading]
            ring1
          _ = (x - root) * (leading * x ^ remaining.length) +
                ((x - root) * Dense.Basic.DensePolynomial.evalCoeffs x recursive.1 + recursive.2) := by
            rw [recursiveFactor]
          _ = (x - root) *
                (leading * x ^ remaining.length +
                  Dense.Basic.DensePolynomial.evalCoeffs x recursive.1) + recursive.2 := by
            ring1
          _ = (x - root) * Dense.Basic.DensePolynomial.evalCoeffs x (leading :: recursive.1) +
                recursive.2 := by
            rw [evalCoeffs_cons_power, recursiveSpec.1]

end Purelib.Polynomial.Dense.Rational.Division.Synthetic
