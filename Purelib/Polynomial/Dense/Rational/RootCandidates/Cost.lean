module
import Purelib.Data.Nat.BitWidth
import Purelib.Computation.Arithmetic.Cost.Basic
import Purelib.Computation.Arithmetic.Cost.Rational
import Purelib.Data.Rat.Enumeration.Divisors
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Evaluation.Cost
public import Purelib.Polynomial.Dense.Rational.RootCandidates

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Work and pool counts for rational root candidates

The unfiltered pool retains its separately tested zero and original endpoint
divisor fractions. Work follows every pool entry, including failed Horner tests,
with separate core and normalization charges.
-/
namespace Purelib.Polynomial.Dense.Rational.RootCandidates.Cost

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

/-- The exact unfiltered pool used by `candidates`.

The original ordered signed-divisor fractions follow the separately tested zero.
No evaluation filtering or duplicate removal is performed by this pool builder. -/
@[expose] public def candidatePool (polynomial : Basic.CoordinatePolynomial)
  : List Fraction.Rational :=
  0 :: Enumeration.Divisors.divisorFractions
    (numeratorEndpointMagnitude
      polynomial)
    (denominatorEndpointMagnitude
      polynomial)

/-- The exact root candidates are the unfiltered pool restricted to zero evaluations. -/
public theorem candidates_eq_filter_pool (polynomial :
  Basic.CoordinatePolynomial) :
    candidates polynomial =
      (candidatePool polynomial).filter
      (fun candidate => polynomial.eval candidate = 0) := rfl

/-- The unfiltered divisor pool has at most the displayed divisor-search size. -/
public theorem candidatePool_length_le (polynomial :
  Basic.CoordinatePolynomial) :
    (candidatePool polynomial).length ≤
      divisorCandidateSearchSize
        polynomial := by
  unfold candidatePool
  rw [List.length_cons]
  unfold divisorCandidateSearchSize
  have bound :=
    Enumeration.Divisors.divisorFractions_length_le
      (numeratorEndpointMagnitude
        polynomial)
      (denominatorEndpointMagnitude
        polynomial)
  omega

/-- Each bounded divisor test is charged at the bit width of its displayed
index and endpoint.  Fraction construction is charged at the actual width of
every member of the finite pool. -/
@[expose] public def divisorEnumerationCost (polynomial :
  Basic.CoordinatePolynomial) : Computation.Arithmetic.Cost.Basic.Work :=
  let numerator :=
    numeratorEndpointMagnitude
      polynomial
  let denominator :=
    denominatorEndpointMagnitude
      polynomial
  { core :=
      numerator * (Data.Nat.BitWidth.natWidth numerator + 1) ^ 2 +
        denominator * (Data.Nat.BitWidth.natWidth denominator + 1) ^ 2 +
        (candidatePool polynomial).length *
          (Data.Nat.BitWidth.natWidth numerator + Data.Nat.BitWidth.natWidth denominator + 1) ^ 2
    normalization :=
      ((candidatePool polynomial).map
        Computation.Arithmetic.Cost.Rational.normalizationCharge).sum }

/-- Sum the exact rational Horner work over every unfiltered candidate.

The charge follows the actual finite pool, including unsuccessful candidates, with arithmetic and normalization work
retained separately. -/
@[expose] public def allHornerWork (polynomial : Basic.CoordinatePolynomial)
  : Computation.Arithmetic.Cost.Basic.Work :=
  Computation.Arithmetic.Cost.Basic.Work.sum ((candidatePool polynomial).map fun
    candidate =>
    Evaluation.Cost.polynomialHornerWork polynomial candidate)

/-- The pool occurrences fit the summed divisor-search sizes of a polynomial list.

Structural recursion follows each original polynomial occurrence. Its retained
pool bound is added to the bound of the unchanged tail, including repetitions. -/
public theorem sum_candidatePool_length_le : ∀ polynomials : List
  Basic.CoordinatePolynomial,
    (polynomials.map (fun polynomial => (candidatePool polynomial).length)).sum ≤
      (polynomials.map
        divisorCandidateSearchSize).sum
  | [] => Nat.le_refl 0
  | polynomial :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (candidatePool_length_le polynomial)
        (sum_candidatePool_length_le remaining)

end Purelib.Polynomial.Dense.Rational.RootCandidates.Cost
