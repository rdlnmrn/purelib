module
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Enumeration.Divisors
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.List.Filter
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Integer.Homogeneous
import Purelib.Polynomial.Dense.Rational.Denominator
public import Purelib.Polynomial.Dense.Rational.RootBounds
public import Purelib.Polynomial.Dense.Rational.TrimTrailing
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

/-!
# Finite rational endpoint-divisor candidates

The original normalized, trimmed and denominator-cleared coefficients retain
their endpoint witnesses. The candidate list keeps the separately tested zero
and every ordered divisor fraction before its exact evaluation filter.
-/
namespace Purelib.Polynomial.Dense.Rational.RootCandidates

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib.Data.List Purelib.Data.Int

/-- Coarse finite search bound obtained from the actually displayed,
normalized, trailing-trimmed, denominator-cleared coefficients. -/
@[expose] public def candidateBound (p : Basic.RootCandidates.CoefficientPolynomial) : Nat :=
  Dense.Rational.RootBounds.coefficientBound
    (Dense.Rational.Denominator.clear (Dense.Rational.TrimTrailing.trimTrailing p.normalize.coeffs)).coefficients

/-- A defensive upper bound on the number of displayed fractions inspected
by `candidates` for one polynomial.  It deliberately charges for both copies
of zero in `signedComponents` as well as the separately tested zero. -/
@[expose] public def candidateSearchSize (bound : Nat) : Nat :=
  1 + 2 * bound * (bound + 1)

/-- First coefficient of a finite high-to-low integer list, or zero for the
empty defensive branch. -/
@[expose] public def leadingCoefficient : List Int → Int
  | [] => 0
  | coefficient :: _ => coefficient

/-- The actual finite integer polynomial on which endpoint divisibility is
applied.

Normalization and trailing-zero trimming produce the original rational table.
Its exact denominator-clearance result retains the integer coefficient order. -/
@[expose] public def preparedCoefficients (p : Basic.RootCandidates.CoefficientPolynomial) : List Int :=
  (Dense.Rational.Denominator.clear (Dense.Rational.TrimTrailing.trimTrailing p.normalize.coeffs)).coefficients

/-- Read the absolute constant coefficient of the normalized, trailing-trimmed, denominator-cleared integer table. -/
@[expose] public def numeratorEndpointMagnitude (p : Basic.RootCandidates.CoefficientPolynomial) : Nat :=
  (Dense.Integer.Homogeneous.constantCoefficient (preparedCoefficients p)).natAbs

/-- Read the absolute leading coefficient of the normalized, trailing-trimmed, denominator-cleared integer table. -/
@[expose] public def denominatorEndpointMagnitude (p : Basic.RootCandidates.CoefficientPolynomial) : Nat :=
  (leadingCoefficient (preparedCoefficients p)).natAbs

/-- Work charged to the separately tested zero and the finite product of
signed constant-term divisors with positive leading-term divisors. -/
@[expose] public def divisorCandidateSearchSize (p : Basic.RootCandidates.CoefficientPolynomial) : Nat :=
  1 + 2 * numeratorEndpointMagnitude p * denominatorEndpointMagnitude p

/-- Derive and exactly filter the finite rational-root candidate list using
only divisors of the two nonzero endpoint coefficients.  Zero is tested
separately because it is the one root removed by trailing-zero trimming.

The normalized and trimmed table determines the original cleared endpoints.
Their signed/positive divisor occurrences keep their order before the exact
evaluation test selects each original candidate. -/
@[expose] public def candidates (p : Basic.RootCandidates.CoefficientPolynomial) : List Fraction.Rational :=
  (0 :: Data.Rat.Enumeration.Divisors.divisorFractions (numeratorEndpointMagnitude p)
      (denominatorEndpointMagnitude p)).filter
    (fun candidate => p.eval candidate = 0)

/-- Exact filtering cannot make the finite endpoint-divisor product larger. -/
public theorem candidates_length_le (p : Basic.RootCandidates.CoefficientPolynomial) :
    (candidates p).length ≤ divisorCandidateSearchSize p := by
  calc
    (candidates p).length ≤
        (0 :: Data.Rat.Enumeration.Divisors.divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)).length := by
      exact Filter.length_filter_le _ _
    _ = 1 + (Data.Rat.Enumeration.Divisors.divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)).length := by
      simp only [List.length_cons]
      exact Nat.add_comm _ _
    _ ≤ 1 + 2 * numeratorEndpointMagnitude p *
          denominatorEndpointMagnitude p :=
      Nat.add_le_add_left
        (Data.Rat.Enumeration.Divisors.divisorFractions_length_le (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)) 1
    _ = divisorCandidateSearchSize p := rfl

/-- Every displayed rational root of a nonzero dense polynomial occurs in
the automatically derived finite candidate list.  The quantifier is over one
supplied value only; the construction itself is the finite list `candidates
p`.

A zero root retains the separately tested head. A nonzero root keeps its
normalized and trimmed coefficient witnesses, exact denominator clearance and
reduced numerator/denominator divisors through the original finite filter. -/
public theorem root_mem_candidates (p : Basic.RootCandidates.CoefficientPolynomial) (nonzero : p.isZero = false)
    (point : Fraction.Rational) (root : p.eval point = 0) :
    point ∈ candidates p := by
  by_cases pointZero : point = 0
  · subst point
    apply Filter.mem_filter.mpr
    exact ⟨List.Mem.head _, decide_eq_true root⟩
  · rcases Dense.Basic.DensePolynomial.normalized_coeffs_shape nonzero with
      ⟨remaining, normalizedShape, _degreeShape⟩
    have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero nonzero
    rcases Dense.Rational.TrimTrailing.trimTrailing_cons_of_leading_nonzero p.leadingCoeff remaining
        leadingNonzero with ⟨trimmedRemaining, trimmedShape⟩
    have normalizedRoot :
        Dense.Basic.DensePolynomial.evalCoeffs point p.normalize.coeffs = 0 := by
      change p.normalize.eval point = 0
      rewrite [Dense.Basic.DensePolynomial.eval_normalize]
      exact root
    have trimmedRoot := Dense.Rational.TrimTrailing.eval_trimTrailing_eq_zero_of_nonzero_root point
      p.normalize.coeffs pointZero normalizedRoot
    rw [normalizedShape, trimmedShape] at trimmedRoot
    have homogeneousZero := Dense.Rational.RootBounds.homogeneous_zero_of_eval_zero point
      p.leadingCoeff trimmedRemaining trimmedRoot
    rcases Dense.Rational.Denominator.clear_leading_nonzero p.leadingCoeff trimmedRemaining
        leadingNonzero with
      ⟨integerLeading, integerRemaining, clearedShape,
        integerLeadingNonzero⟩
    rw [clearedShape] at homogeneousZero
    have rationalConstantNonzero := Dense.Rational.TrimTrailing.trimTrailing_constant_nonzero
      (p.leadingCoeff :: remaining) p.leadingCoeff trimmedRemaining
      trimmedShape
    have integerConstantNonzero := Dense.Rational.Denominator.clear_constant_nonzero
      p.leadingCoeff trimmedRemaining rationalConstantNonzero
    rw [clearedShape] at integerConstantNonzero
    have divisors := Dense.Rational.RootBounds.reduced_divisors_of_homogeneous_zero
      (Fraction.Basic.representative point) integerLeading integerRemaining
      integerLeadingNonzero integerConstantNonzero homogeneousZero
    have divisorMember : point ∈
        Data.Rat.Enumeration.Divisors.divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p) := by
      apply Data.Rat.Enumeration.Divisors.mem_divisorFractions_of_representative_divisors point
      · exact pointZero
      · simpa only [numeratorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using Arithmetic.natAbs_pos_of_ne_zero integerConstantNonzero
      · simpa only [denominatorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using Arithmetic.natAbs_pos_of_ne_zero integerLeadingNonzero
      · simpa only [numeratorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using divisors.1
      · simpa only [denominatorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using divisors.2
    apply Filter.mem_filter.mpr
    exact ⟨List.Mem.tail 0 divisorMember, decide_eq_true root⟩

end Purelib.Polynomial.Dense.Rational.RootCandidates
