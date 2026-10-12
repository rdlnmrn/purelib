module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Computation.Arithmetic.Cost.Basic
import Purelib.Computation.Arithmetic.Cost.Gaussian
public import Purelib.Computation.Arithmetic.Cost.Gaussian.Power
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.List.Deduplicate.Cost
public import Purelib.Data.List.Deduplicate.Cost
import Purelib.Data.List.Flatten.Length
import Purelib.Data.Nat.Positive
public import Purelib.Polynomial.Dense.Rational.Clearance.Cost
public import Purelib.Polynomial.Dense.Rational.Construction.Cost
import Purelib.Polynomial.Dense.Rational.RootCandidates
public import Purelib.Polynomial.Dense.Rational.RootCandidates.Cost
import Purelib.Polynomial.Dense.Rational.TrimTrailing
import Purelib.Polynomial.Power.Gaussian.Candidates
public import Purelib.Polynomial.Power.Gaussian.Candidates.Size

import Mathlib.Algebra.GroupWithZero.Nat
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Work and occurrence counts for Gaussian power candidates

The ledger follows the retained sparse search in order: one norm polynomial,
then the real and imaginary coordinate polynomials for each radius candidate.
Arithmetic charges, normalization charges and occurrence counts retain their
separate fields and the exact candidate lists used by the executable search.
-/

namespace Purelib.Polynomial.Power.Gaussian.Candidates.Cost

open Purelib Purelib.Data Purelib.Data.Rat Purelib.Polynomial
open Purelib.Polynomial.Power.Gaussian

/-! ## The actual sparse search ledger -/

/-- List the norm polynomial followed by two coordinate polynomials per radius.

The original retained radius order determines the flat-map order. Each occurrence
contributes its real polynomial first and its imaginary polynomial second. -/
@[expose] public def searchPolynomials (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    List Dense.Rational.Basic.CoordinatePolynomial :=
  Candidates.radiusPolynomial input degree ::
    (Candidates.radiusCandidates input degree).flatMap fun radius =>
      [Candidates.realCoordinatePolynomial input degree radius,
        Candidates.imaginaryCoordinatePolynomial input degree radius]

/-- The search materializes one norm polynomial and two coordinate polynomials for each retained radius candidate.

Each original radius occurrence contributes its ordered real and imaginary
pair. The norm polynomial supplies the remaining single occurrence. -/
public theorem searchPolynomials_length (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (searchPolynomials input degree).length =
      1 + 2 * (Candidates.radiusCandidates input degree).length := by
  unfold searchPolynomials
  rw [List.length_cons,
    Data.List.Flatten.Length.flatMap_pair_length
      (Candidates.realCoordinatePolynomial input degree)
      (Candidates.imaginaryCoordinatePolynomial input degree)
      (Candidates.radiusCandidates input degree)]
  ring1

/-- Count the coefficient slots in the exact list of searched norm and coordinate polynomials.

The exact searched polynomial list supplies each coefficient length. Its natural
sum counts the original tables, including repeated radius occurrences. -/
@[expose] public def searchCoefficientSlots (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Nat :=
  ((searchPolynomials input degree).map
    (fun polynomial => polynomial.coeffs.length)).sum

/-- Each radius contributes two coordinate tables with degree plus one slots.

Structural recursion follows the original ordered radius list. The head contributes
its two retained coefficient lengths, while the tail keeps its original sum. -/
private theorem coordinateSearchSlots (input : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) : ∀ radii : List Fraction.Rational,
    (((radii.flatMap fun radius =>
        [Candidates.realCoordinatePolynomial input degree radius,
          Candidates.imaginaryCoordinatePolynomial input degree radius]).map
      (fun polynomial => polynomial.coeffs.length)).sum) =
      2 * radii.length * (degree.value + 1)
  | [] => (Nat.zero_mul (degree.value + 1)).symm
  | radius :: remaining => by
      change
        (Candidates.realCoordinatePolynomial input degree radius).coeffs.length +
            ((Candidates.imaginaryCoordinatePolynomial input degree radius).coeffs.length +
              (((remaining.flatMap fun radius =>
                [Candidates.realCoordinatePolynomial input degree radius,
                  Candidates.imaginaryCoordinatePolynomial input degree radius]).map
                (fun polynomial => polynomial.coeffs.length)).sum)) =
          2 * (remaining.length + 1) * (degree.value + 1)
      rewrite [Candidates.realCoordinatePolynomial_coefficients_length,
        Candidates.imaginaryCoordinatePolynomial_coefficients_length,
        coordinateSearchSlots input degree remaining]
      ring1

/-- The searched coefficient count is the polynomial count times degree plus one.

The norm table and each retained coordinate table have the same exact length.
The original radius occurrences contribute two tables each, including repeats. -/
public theorem searchCoefficientSlots_eq (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    searchCoefficientSlots input degree =
      (1 + 2 * (Candidates.radiusCandidates input degree).length) *
        (degree.value + 1) := by
  change
    (Candidates.radiusPolynomial input degree).coeffs.length +
        ((((Candidates.radiusCandidates input degree).flatMap fun radius =>
          [Candidates.realCoordinatePolynomial input degree radius,
            Candidates.imaginaryCoordinatePolynomial input degree radius]).map
          (fun polynomial => polynomial.coeffs.length)).sum) = _
  rewrite [Candidates.radiusPolynomial_coefficients_length,
    coordinateSearchSlots input degree (Candidates.radiusCandidates input degree)]
  ring1

/-- Sum the finite denominator-clearance work for the normalized, trailing-zero-trimmed searched coefficient lists.

Each original normalized table is trimmed by the retained trailing-zero scan.
The same coefficient list supplies its core and normalization charges. -/
@[expose] public def searchedClearanceWork (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Computation.Arithmetic.Cost.Basic.Work :=
  Computation.Arithmetic.Cost.Basic.Work.sum ((searchPolynomials input degree).map fun polynomial =>
    Dense.Rational.Clearance.Cost.clearanceWork
      (Dense.Rational.TrimTrailing.trimTrailing
        polynomial.normalize.coeffs))

/-- Charge norm computation, the imaginary rotation and construction of every searched polynomial.

The returned work keeps core arithmetic and rational normalization charges separate. -/
@[expose] public def searchedConstructionWork (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree)
  : Computation.Arithmetic.Cost.Basic.Work :=
  let rotation := Computation.Arithmetic.Cost.Gaussian.Power.powerWork
    Gaussian.Constants.negativeImaginaryUnit degree.value
  Computation.Arithmetic.Cost.Gaussian.gaussianNormWork input + rotation.1 +
    Computation.Arithmetic.Cost.Gaussian.gaussianMulWork rotation.2 input +
    Computation.Arithmetic.Cost.Basic.Work.sum ((searchPolynomials input degree).map
      Dense.Rational.Construction.Cost.polynomialConstructionWork)

/-- Sum the endpoint-divisor enumeration work for the exact searched polynomial list.

Each original searched polynomial contributes its displayed endpoint-divisor
work. Both work components are accumulated over that same ordered list. -/
@[expose] public def searchedDivisorWork (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Computation.Arithmetic.Cost.Basic.Work :=
  Computation.Arithmetic.Cost.Basic.Work.sum ((searchPolynomials input degree).map
    Dense.Rational.RootCandidates.Cost.divisorEnumerationCost)

/-- Sum the exact candidate-evaluation work for the searched polynomial list.

Every retained pool entry contributes its exact finite Horner work. The sum
follows the original searched polynomial occurrences without deduplicating them. -/
@[expose] public def searchedHornerWork (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Computation.Arithmetic.Cost.Basic.Work :=
  Computation.Arithmetic.Cost.Basic.Work.sum ((searchPolynomials input degree).map
    Dense.Rational.RootCandidates.Cost.allHornerWork)

/-- Count all retained rational candidate evaluations across the searched polynomial list.

The exact unfiltered candidate pool of each searched polynomial determines its
occurrence count. The original polynomial order and repetitions are retained. -/
@[expose] public def searchedHornerTestCount (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree)
  : Nat :=
  ((searchPolynomials input degree).map
    (fun polynomial => (Dense.Rational.RootCandidates.Cost.candidatePool polynomial).length)).sum

/-- Sum the finite divisor-candidate search bounds for the searched polynomials.

Each original polynomial contributes the bound from its displayed cleared
endpoints. The sum retains the same searched occurrence list as the test count. -/
@[expose] public def searchedHornerTestBound (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree)
  : Nat :=
  ((searchPolynomials input degree).map
    Dense.Rational.RootCandidates.divisorCandidateSearchSize).sum

/-- The retained Horner test count is bounded by the sum of finite divisor-candidate search bounds.

Each searched polynomial keeps its original unfiltered candidate pool.
The corresponding occurrence bound is added over the exact searched list. -/
public theorem searchedHornerTestCount_le (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    searchedHornerTestCount input degree ≤
      searchedHornerTestBound input degree :=
  Dense.Rational.RootCandidates.Cost.sum_candidatePool_length_le (searchPolynomials input degree)

/-- Sum the exact power-test work over the deduplicated Gaussian candidate list.

The deduplicated list supplies the original candidates and final exponent.
Their actual power-test computations determine both work components. -/
@[expose] public def finalPowerWork (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Computation.Arithmetic.Cost.Basic.Work :=
  Computation.Arithmetic.Cost.Basic.Work.sum ((Candidates.derivedCandidates input degree).map fun candidate =>
    Computation.Arithmetic.Cost.Gaussian.Power.powerTestWork input candidate degree.value)

@[expose] public section

set_option genInjectivity false in
/-- Retain seven work charges and three occurrence counts for a finite root search.

Endpoint divisor enumeration, rational normalization and duplicate removal have
separate charges. Horner tests, duplicate comparisons and final power tests retain
their original occurrence counts independently of the summed work charge. -/
structure RootSearchAccount where
  /-- The core work charged to coefficient denominator clearance. -/ coefficientClearance : Nat
  /-- The core work charged to sparse polynomial construction and input norm and rotation. -/
    sparsePolynomialConstruction : Nat
  /-- The core work charged to finite endpoint-divisor enumeration. -/ endpointDivisorEnumeration : Nat
  /-- The normalization work accumulated across clearance, construction, divisor, Horner and power computations. -/
    rationalNormalization : Nat
  /-- The core work charged to exact rational Horner evaluations. -/ exactHornerTests : Nat
  /-- The work charged to Gaussian duplicate removal on the raw candidate list. -/ duplicateRemoval : Nat
  /-- The core work charged to the final exact Gaussian power tests. -/ exactPowerTests : Nat
  /-- The number of retained rational Horner candidate tests. -/ hornerTestCount : Nat
  /-- The number of equality comparisons in raw-candidate duplicate removal. -/ duplicateComparisonCount : Nat
  /-- The number of deduplicated Gaussian candidates receiving a final power test. -/ powerTestCount : Nat
deriving DecidableEq

constructive_injectivity RootSearchAccount

derive_exposed_repr RootSearchAccount

end

namespace RootSearchAccount

/-- Sum the seven work charges, excluding the separately retained operation counts. -/
@[expose] public def total (account : RootSearchAccount) : Nat :=
  account.coefficientClearance +
    account.sparsePolynomialConstruction +
    account.endpointDivisorEnumeration +
    account.rationalNormalization +
    account.exactHornerTests +
    account.duplicateRemoval +
    account.exactPowerTests

end RootSearchAccount

/-- Retain the complete work ledger for one input and positive degree.

Five phase computations are cached before their core and normalization projections
are combined. Duplicate and power counts use the original raw and deduplicated
candidate lists respectively. -/
@[expose] public def account (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  RootSearchAccount :=
  let clearance := searchedClearanceWork input degree
  let construction := searchedConstructionWork input degree
  let divisors := searchedDivisorWork input degree
  let horner := searchedHornerWork input degree
  let power := finalPowerWork input degree
  { coefficientClearance := clearance.core
    sparsePolynomialConstruction := construction.core
    endpointDivisorEnumeration := divisors.core
    rationalNormalization :=
      clearance.normalization + construction.normalization +
        divisors.normalization + horner.normalization + power.normalization
    exactHornerTests := horner.core
    duplicateRemoval :=
      Gaussian.List.Deduplicate.Cost.duplicateRemovalCost (Candidates.rawDerivedCandidates input degree)
    exactPowerTests := power.core
    hornerTestCount := searchedHornerTestCount input degree
    duplicateComparisonCount :=
      Data.List.Deduplicate.Cost.duplicateComparisonCount (Candidates.rawDerivedCandidates input degree)
    powerTestCount := (Candidates.derivedCandidates input degree).length }

/-- Read the total finite bit-work charge from the executable root-search account. -/
@[expose] public def chargedBitComplexity (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
  Nat :=
  (account input degree).total

/-- The number of final exact power tests is bounded by the automatic candidate search size. -/
public theorem powerTestCount_le (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (account input degree).powerTestCount ≤
      Candidates.Size.automaticCandidateSearchSize input degree := by
  exact Candidates.Size.derivedCandidates_length_le input degree

/-- The duplicate-comparison count is bounded by the square of the raw candidate-list length. -/
public theorem duplicateComparisonCount_le (input : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) :
    (account input degree).duplicateComparisonCount ≤
      (Candidates.rawDerivedCandidates input degree).length ^ 2 := by
  change Data.List.Deduplicate.Cost.duplicateComparisonCount (Candidates.rawDerivedCandidates input degree) ≤ _
  simpa only [pow_two] using
    Data.List.Deduplicate.Cost.duplicateComparisonCount_le_square
      (Candidates.rawDerivedCandidates input degree)

/-- The duplicate-comparison count is bounded by the square of the automatic candidate search size. -/
public theorem duplicateComparisonCount_le_candidate_square (input : Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) :
    (account input degree).duplicateComparisonCount ≤
      (Candidates.Size.automaticCandidateSearchSize input degree) ^ 2 := by
  exact (duplicateComparisonCount_le input degree).trans
    (Nat.pow_le_pow_left
      (Candidates.Size.rawDerivedCandidates_length_le input degree) 2)

/-- The final exact-root output and every charged phase share one finite
candidate bound.  This is the public bit-complexity theorem: it exposes the
computed binary work ledger, the exact test counts, and the already-proved
root-list bound together.

The original account supplies the work equality and occurrence counts. Its
retained searched polynomials, raw candidates and promoted candidates provide
their respective finite bounds without recomputing those input lists. -/
public theorem automaticExactRoots_bit_complexity
    (input : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    chargedBitComplexity input degree = (account input degree).total ∧
      (Candidates.automaticExactRoots input degree).length ≤
        Candidates.Size.automaticCandidateSearchSize input degree ∧
      (account input degree).powerTestCount ≤
        Candidates.Size.automaticCandidateSearchSize input degree ∧
      (account input degree).hornerTestCount ≤
        searchedHornerTestBound input degree ∧
      (account input degree).duplicateComparisonCount ≤
        (Candidates.Size.automaticCandidateSearchSize input degree) ^ 2 := by
  exact ⟨rfl, Candidates.Size.automaticExactRoots_length_le input degree,
    powerTestCount_le input degree, searchedHornerTestCount_le input degree,
    duplicateComparisonCount_le_candidate_square input degree⟩

end Purelib.Polynomial.Power.Gaussian.Candidates.Cost
