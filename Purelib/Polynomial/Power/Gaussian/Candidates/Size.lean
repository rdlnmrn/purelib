module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Power.Gaussian.ExactRoot.Check
import Purelib.Data.List.Cartesian
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Deduplicate
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.RootCandidates
public import Purelib.Polynomial.Power.Gaussian.Candidates

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Algebra.Power.Gaussian.ExactRoot

/-!
# Finite occurrence bounds for Gaussian power candidates

The bounds retain the actual radius list and each pair of coordinate search
sizes. Summing their products counts the original ordered candidate occurrences
before deduplication and exact promotion.
-/

namespace Purelib.Polynomial.Power.Gaussian.Candidates.Size

open Purelib Purelib.Data Purelib.Data.Rat Purelib.Polynomial
open Purelib.Data.List

/-- The finite size charged to one coordinate's endpoint-divisor
rational-root search.  It is computed from that eliminant's actual cleared
leading and constant coefficients. -/
@[expose] public def coordinateCandidateSearchSize
    (polynomial : Dense.Rational.Basic.RootCandidates.CoefficientPolynomial) : Nat :=
  Dense.Rational.RootCandidates.divisorCandidateSearchSize polynomial

/-- The coordinate-product charge at one displayed radius.

The real and imaginary polynomials at that same radius supply their retained
endpoint-divisor bounds. Their product keeps the original coordinate pairing. -/
@[expose] public def radiusCandidateSearchSize (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : Nat :=
  coordinateCandidateSearchSize
      (Power.Gaussian.Candidates.realCoordinatePolynomial input degree radius) *
    coordinateCandidateSearchSize
      (Power.Gaussian.Candidates.imaginaryCoordinatePolynomial input degree radius)

/-- A bound on the Gaussian candidates reaching deduplication and the exact
power test: the finite sum of coordinate-product charges over the actually
derived radius list.

Each retained radius contributes the product of its two original coordinate
search sizes. The sum counts every original radius occurrence separately. -/
@[expose] public def automaticCandidateSearchSize (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree) :
    Nat :=
  ((Power.Gaussian.Candidates.radiusCandidates input degree).map
    (radiusCandidateSearchSize input degree)).sum

/-- The candidates at one radius fit the product of the two coordinate search bounds. -/
public theorem candidatesAtRadius_length_le (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) :
    (Power.Gaussian.Candidates.candidatesAtRadius input degree radius).length ≤
      radiusCandidateSearchSize input degree radius := by
  rw [Power.Gaussian.Candidates.candidatesAtRadius,
    Cartesian.cartesianCandidates_length]
  exact Nat.mul_le_mul
    (Dense.Rational.RootCandidates.candidates_length_le
      (Power.Gaussian.Candidates.realCoordinatePolynomial input degree radius))
    (Dense.Rational.RootCandidates.candidates_length_le
      (Power.Gaussian.Candidates.imaginaryCoordinatePolynomial input degree radius))

/-- A finite union of radius candidates fits the sum of its coordinate-product bounds.

The original head fiber contributes its retained product bound. Scalar addition
combines that bound with the bound of the unchanged radius tail. -/
private theorem candidateRadii_length_le (input : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) : ∀ radii : List Fraction.Rational,
    (radii.flatMap (Power.Gaussian.Candidates.candidatesAtRadius input degree)).length ≤
      (radii.map (radiusCandidateSearchSize input degree)).sum
  | [] => Nat.le_refl 0
  | radius :: remaining => by
      simp only [Flatten.flatMap_cons, Append.length_append, List.map_cons,
        List.sum_cons]
      exact Nat.add_le_add
        (candidatesAtRadius_length_le input degree radius)
        (candidateRadii_length_le input degree remaining)

/-- The pre-deduplication sparse union already satisfies the summed
endpoint-divisor bound. -/
public theorem rawDerivedCandidates_length_le (input : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Candidates.rawDerivedCandidates input degree).length ≤
      automaticCandidateSearchSize input degree := by
  exact candidateRadii_length_le input degree (Power.Gaussian.Candidates.radiusCandidates input degree)

/-- Deduplicated candidates fit the summed coordinate-product search bound.

Deduplication cannot increase the size of the actual finite union over the derived radius list. -/
public theorem derivedCandidates_length_le (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Candidates.derivedCandidates input degree).length ≤
      automaticCandidateSearchSize input degree := by
  calc
    (Power.Gaussian.Candidates.derivedCandidates input degree).length ≤
        (Power.Gaussian.Candidates.rawDerivedCandidates input degree).length := by
      exact Data.List.Deduplicate.deduplicateCandidates_length_le _
    _ ≤ automaticCandidateSearchSize input degree :=
      rawDerivedCandidates_length_le input degree

/-- Exact promotion cannot exceed the finite Cartesian candidate bound. -/
public theorem automaticExactRoots_length_le
    (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Power.Gaussian.Candidates.automaticExactRoots input degree).length ≤
      automaticCandidateSearchSize input degree := by
  have promotedSublist :=
    Algebra.Power.Gaussian.ExactRoot.Check.promoteCandidates_points_sublist input degree
      (Power.Gaussian.Candidates.derivedCandidates input degree)
  have promotedLength := promotedSublist.length_le
  rewrite [Map.length_map] at promotedLength
  exact promotedLength.trans (derivedCandidates_length_le input degree)
end Purelib.Polynomial.Power.Gaussian.Candidates.Size
