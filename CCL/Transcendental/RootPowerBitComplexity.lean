import mathlib.Tactic.QuotientFreeOmega
import CCL.Transcendental.RootPowers

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

namespace CCL.RootPowerBitComplexity

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial :=
  RFAP.ConstructiveRationalRootCandidates.Polynomial
abbrev RootDegree := CCL.RootPowers.RootDegree

open CCL.RootPowers
open RFAP.ConstructiveFraction

/-! ## Displayed binary widths -/

/-- One sign/zero bit plus the finite binary magnitude width. -/
def natWidth (value : Nat) : Nat := Nat.log2 value + 1

def intWidth (value : Int) : Nat := natWidth value.natAbs + 1

/-- Width of the canonical reduced numerator/positive-denominator pair. -/
def rationalWidth (value : Coordinate) : Nat :=
  intWidth (representative value).num + natWidth (representative value).den

def gaussianWidth (value : Gaussian) : Nat :=
  rationalWidth value.re + rationalWidth value.im

def polynomialWidth (polynomial : Polynomial) : Nat :=
  (polynomial.coeffs.map rationalWidth).sum

theorem natWidth_positive (value : Nat) : 0 < natWidth value := by
  unfold natWidth
  omega

theorem intWidth_positive (value : Int) : 0 < intWidth value := by
  unfold intWidth
  omega

theorem rationalWidth_positive (value : Coordinate) :
    0 < rationalWidth value := by
  unfold rationalWidth
  have numeratorPositive := intWidth_positive (representative value).num
  have denominatorPositive := natWidth_positive (representative value).den
  omega

theorem gaussianWidth_positive (value : Gaussian) :
    0 < gaussianWidth value := by
  unfold gaussianWidth
  have realPositive := rationalWidth_positive value.re
  have imaginaryPositive := rationalWidth_positive value.im
  omega

/-! ## The finite schoolbook work model -/

/-- Core signed-binary work and canonical-normalization work are kept
separate so the formerly hidden gcd phase remains visible. -/
structure Work where
  core : Nat
  normalization : Nat
deriving DecidableEq, Repr

namespace Work

def zero : Work := ⟨0, 0⟩

def add (left right : Work) : Work :=
  ⟨left.core + right.core,
    left.normalization + right.normalization⟩

instance : Zero Work := ⟨zero⟩
instance : Add Work := ⟨add⟩

@[simp] theorem zero_core : (0 : Work).core = 0 := rfl
@[simp] theorem zero_normalization : (0 : Work).normalization = 0 := rfl
@[simp] theorem add_core (left right : Work) :
    (left + right).core = left.core + right.core := rfl
@[simp] theorem add_normalization (left right : Work) :
    (left + right).normalization =
      left.normalization + right.normalization := rfl

def sum : List Work → Work
  | [] => 0
  | work :: remaining => work + sum remaining

@[simp] theorem sum_nil : sum [] = 0 := rfl
@[simp] theorem sum_cons (work : Work) (remaining : List Work) :
    sum (work :: remaining) = work + sum remaining := rfl

def total (work : Work) : Nat := work.core + work.normalization

end Work

def normalizationCharge (value : Coordinate) : Nat :=
  (rationalWidth value + 1) ^ 3

/-- One rational operation with its actual normalized result. -/
def rationalOperationWork (left right output : Coordinate) : Work :=
  { core :=
      (rationalWidth left + rationalWidth right + rationalWidth output + 1) ^ 2
    normalization := normalizationCharge output }

def rationalAddWork (left right : Coordinate) : Work :=
  rationalOperationWork left right (left + right)

def rationalSubWork (left right : Coordinate) : Work :=
  rationalOperationWork left right (left - right)

def rationalMulWork (left right : Coordinate) : Work :=
  rationalOperationWork left right (left * right)

def rationalEqualityCost (left right : Coordinate) : Nat :=
  rationalWidth left + rationalWidth right + 1

def gaussianEqualityCost (left right : Gaussian) : Nat :=
  rationalEqualityCost left.re right.re +
    rationalEqualityCost left.im right.im

/-- The six rational operations in one displayed Gaussian product. -/
def gaussianMulWork (left right : Gaussian) : Work :=
  let realLeft := rationalMulWork left.re right.re
  let realRight := rationalMulWork left.im right.im
  let imaginaryLeft := rationalMulWork left.re right.im
  let imaginaryRight := rationalMulWork left.im right.re
  realLeft + realRight + imaginaryLeft + imaginaryRight +
    rationalSubWork (left.re * right.re) (left.im * right.im) +
    rationalAddWork (left.re * right.im) (left.im * right.re)

def gaussianNormWork (value : Gaussian) : Work :=
  rationalMulWork value.re value.re +
    rationalMulWork value.im value.im +
    rationalAddWork (value.re * value.re) (value.im * value.im)

/-! ## Exact Horner and power traces -/

/-- Bit work of the actual high-to-low Horner accumulator sequence. -/
def hornerWork (point : Coordinate) :
    List Coordinate → Coordinate → Work
  | [], _ => 0
  | coefficient :: remaining, accumulator =>
      let product := accumulator * point
      let next := product + coefficient
      rationalMulWork accumulator point +
        rationalAddWork product coefficient +
        hornerWork point remaining next

def polynomialHornerWork (polynomial : Polynomial)
    (point : Coordinate) : Work :=
  hornerWork point polynomial.coeffs 0

def hornerStepCount (coefficients : List Coordinate) : Nat :=
  coefficients.length

theorem hornerStepCount_eq_length (coefficients : List Coordinate) :
    hornerStepCount coefficients = coefficients.length := rfl

/-- Repeated multiplication with the same intermediate values as `z^n`. -/
def powerWork (point : Gaussian) : Nat → Work × Gaussian
  | 0 => (0, 1)
  | exponent + 1 =>
      let previous := powerWork point exponent
      (previous.1 + gaussianMulWork previous.2 point,
        previous.2 * point)

@[simp] theorem powerWork_value (point : Gaussian) : ∀ exponent,
    (powerWork point exponent).2 = point ^ exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [powerWork, powerWork_value, pow_succ]

def powerTestWork (input candidate : Gaussian) (degree : Nat) : Work :=
  let powered := powerWork candidate degree
  { core := powered.1.core + gaussianEqualityCost powered.2 input
    normalization := powered.1.normalization }

/-! ## Clearance, pools, and finite comparison passes -/

def intMultiplicationCost (left right : Int) : Nat :=
  (intWidth left + intWidth right + intWidth (left * right) + 1) ^ 2

def natMultiplicationCost (left right : Nat) : Nat :=
  (natWidth left + natWidth right + natWidth (left * right) + 1) ^ 2

/-- Core work of the exact structural denominator-clearance recursion. -/
def clearanceCoreCost : List Coordinate → Nat
  | [] => 0
  | coefficient :: remaining =>
      let head := representative coefficient
      let tail := RFAP.ConstructiveRationalRootCandidates.clear remaining
      clearanceCoreCost remaining +
        natMultiplicationCost head.den tail.denominator +
        intMultiplicationCost head.num (tail.denominator : Int) +
        (tail.coefficients.map
          (fun value => intMultiplicationCost (head.den : Int) value)).sum

def clearanceWork (coefficients : List Coordinate) : Work :=
  { core := clearanceCoreCost coefficients
    normalization :=
      (coefficients.map (fun value => normalizationCharge value)).sum }

/-- The exact unfiltered pool used by `candidates`. -/
def candidatePool (polynomial : Polynomial) : List Coordinate :=
  0 :: RFAP.ConstructiveRationalRootCandidates.divisorFractions
    (RFAP.ConstructiveRationalRootCandidates.numeratorEndpointMagnitude
      polynomial)
    (RFAP.ConstructiveRationalRootCandidates.denominatorEndpointMagnitude
      polynomial)

theorem candidates_eq_filter_pool (polynomial : Polynomial) :
    RFAP.ConstructiveRationalRootCandidates.candidates polynomial =
      (candidatePool polynomial).filter
      (fun candidate => polynomial.eval candidate = 0) := rfl

theorem candidatePool_length_le (polynomial : Polynomial) :
    (candidatePool polynomial).length ≤
      RFAP.ConstructiveRationalRootCandidates.divisorCandidateSearchSize
        polynomial := by
  unfold candidatePool
  rw [List.length_cons]
  change
      (RFAP.ConstructiveRationalRootCandidates.divisorFractions
        (RFAP.ConstructiveRationalRootCandidates.numeratorEndpointMagnitude
          polynomial)
        (RFAP.ConstructiveRationalRootCandidates.denominatorEndpointMagnitude
          polynomial)).length + 1 ≤ _
  unfold RFAP.ConstructiveRationalRootCandidates.divisorCandidateSearchSize
  have bound :=
    RFAP.ConstructiveRationalRootCandidates.divisorFractions_length_le
      (RFAP.ConstructiveRationalRootCandidates.numeratorEndpointMagnitude
        polynomial)
      (RFAP.ConstructiveRationalRootCandidates.denominatorEndpointMagnitude
        polynomial)
  omega

/-- Each bounded divisor test is charged at the bit width of its displayed
index and endpoint.  Fraction construction is charged at the actual width of
every member of the finite pool. -/
def divisorEnumerationCost (polynomial : Polynomial) : Work :=
  let numerator :=
    RFAP.ConstructiveRationalRootCandidates.numeratorEndpointMagnitude
      polynomial
  let denominator :=
    RFAP.ConstructiveRationalRootCandidates.denominatorEndpointMagnitude
      polynomial
  { core :=
      numerator * (natWidth numerator + 1) ^ 2 +
        denominator * (natWidth denominator + 1) ^ 2 +
        (candidatePool polynomial).length *
          (natWidth numerator + natWidth denominator + 1) ^ 2
    normalization :=
      ((candidatePool polynomial).map normalizationCharge).sum }

def allHornerWork (polynomial : Polynomial) : Work :=
  Work.sum ((candidatePool polynomial).map fun candidate =>
    polynomialHornerWork polynomial candidate)

/-- A defensive dense-list construction charge.  It is quadratic in the
coefficient slots and cubic in the actual aggregate coefficient width, so it
also covers normalization of every materialized coefficient in the coarse
schoolbook model. -/
def polynomialConstructionWork (polynomial : Polynomial) : Work :=
  { core :=
      (polynomial.coeffs.length + 1) ^ 2 *
        (polynomialWidth polynomial + 1) ^ 2
    normalization :=
      polynomial.coeffs.length * (polynomialWidth polynomial + 1) ^ 3 }

def membershipComparisonCost (candidate : Gaussian) : List Gaussian → Nat
  | [] => 0
  | value :: remaining =>
      gaussianEqualityCost candidate value +
        membershipComparisonCost candidate remaining

/-- Upper charge for the list deduplicator: it charges the entire remaining
tail even when the executable membership test stops at an earlier match. -/
def duplicateRemovalCost : List Gaussian → Nat
  | [] => 0
  | candidate :: remaining =>
      membershipComparisonCost candidate remaining +
        duplicateRemovalCost remaining

def duplicateComparisonCount : List Gaussian → Nat
  | [] => 0
  | _ :: remaining => remaining.length + duplicateComparisonCount remaining

theorem duplicateComparisonCount_le_square : ∀ values : List Gaussian,
    duplicateComparisonCount values ≤ values.length * values.length
  | [] => Nat.le_refl 0
  | _ :: remaining => by
      simp only [duplicateComparisonCount, List.length_cons]
      have inductionBound := duplicateComparisonCount_le_square remaining
      calc
        remaining.length + duplicateComparisonCount remaining ≤
            remaining.length + remaining.length * remaining.length :=
          Nat.add_le_add_left inductionBound remaining.length
        _ ≤ (remaining.length + 1) * (remaining.length + 1) := by
          rw [Nat.add_mul, Nat.mul_add]
          simp only [Nat.one_mul, Nat.mul_one]
          omega

/-! ## The actual sparse search ledger -/

/-- Exactly the polynomials searched by the sparse root algorithm: one norm
polynomial, then two coordinate polynomials per surviving norm candidate. -/
def searchPolynomials (input : Gaussian) (degree : RootDegree) :
    List Polynomial :=
  radiusPolynomial input degree ::
    (radiusCandidates input degree).flatMap fun radius =>
      [realCoordinatePolynomial input degree radius,
        imaginaryCoordinatePolynomial input degree radius]

private theorem flatMap_pair_length {A B : Type}
    (left right : A → B) : ∀ values : List A,
    (values.flatMap fun value => [left value, right value]).length =
      2 * values.length
  | [] => rfl
  | value :: remaining => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, flatMap_pair_length left right remaining]
      ring1

theorem searchPolynomials_length (input : Gaussian) (degree : RootDegree) :
    (searchPolynomials input degree).length =
      1 + 2 * (radiusCandidates input degree).length := by
  unfold searchPolynomials
  rw [List.length_cons,
    flatMap_pair_length
      (realCoordinatePolynomial input degree)
      (imaginaryCoordinatePolynomial input degree)
      (radiusCandidates input degree)]
  ring1

def searchCoefficientSlots (input : Gaussian) (degree : RootDegree) : Nat :=
  ((searchPolynomials input degree).map
    (fun polynomial => polynomial.coeffs.length)).sum

private theorem coordinateSearchSlots (input : Gaussian)
    (degree : RootDegree) : ∀ radii : List Coordinate,
    (((radii.flatMap fun radius =>
        [realCoordinatePolynomial input degree radius,
          imaginaryCoordinatePolynomial input degree radius]).map
      (fun polynomial => polynomial.coeffs.length)).sum) =
      2 * radii.length * (degree.value + 1)
  | [] => by
      simp only [List.flatMap_nil, List.map_nil, List.sum_nil,
        List.length_nil, Nat.mul_zero, Nat.zero_mul]
  | radius :: remaining => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        realCoordinatePolynomial_coefficients_length,
        imaginaryCoordinatePolynomial_coefficients_length,
        coordinateSearchSlots input degree remaining, List.length_cons]
      rw [show 2 * (remaining.length + 1) =
        2 * remaining.length + 2 by ring1, Nat.add_mul]
      ring1

/-- The specialization materializes only `q+1` coefficient slots per sparse
norm/coordinate polynomial; no `2q` Sylvester matrix or fraction-free inverse
coefficient tower enters this root search. -/
theorem searchCoefficientSlots_eq (input : Gaussian) (degree : RootDegree) :
    searchCoefficientSlots input degree =
      (1 + 2 * (radiusCandidates input degree).length) *
        (degree.value + 1) := by
  unfold searchCoefficientSlots searchPolynomials
  simp only [List.map_cons, List.sum_cons,
    radiusPolynomial_coefficients_length,
    coordinateSearchSlots input degree (radiusCandidates input degree)]
  rw [Nat.add_mul]
  simp only [Nat.one_mul]

def searchedClearanceWork (input : Gaussian) (degree : RootDegree) : Work :=
  Work.sum ((searchPolynomials input degree).map fun polynomial =>
    clearanceWork
      (RFAP.ConstructiveRationalRootCandidates.trimTrailing
        polynomial.normalize.coeffs))

def searchedConstructionWork (input : Gaussian) (degree : RootDegree) : Work :=
  let rotation := powerWork
    CCL.SparseRootCoordinates.negativeImaginaryUnit degree.value
  gaussianNormWork input + rotation.1 + gaussianMulWork rotation.2 input +
    Work.sum ((searchPolynomials input degree).map polynomialConstructionWork)

def searchedDivisorWork (input : Gaussian) (degree : RootDegree) : Work :=
  Work.sum ((searchPolynomials input degree).map divisorEnumerationCost)

def searchedHornerWork (input : Gaussian) (degree : RootDegree) : Work :=
  Work.sum ((searchPolynomials input degree).map allHornerWork)

def searchedHornerTestCount (input : Gaussian) (degree : RootDegree) : Nat :=
  ((searchPolynomials input degree).map
    (fun polynomial => (candidatePool polynomial).length)).sum

def searchedHornerTestBound (input : Gaussian) (degree : RootDegree) : Nat :=
  ((searchPolynomials input degree).map
    RFAP.ConstructiveRationalRootCandidates.divisorCandidateSearchSize).sum

private theorem sum_candidatePool_length_le : ∀ polynomials : List Polynomial,
    (polynomials.map (fun polynomial => (candidatePool polynomial).length)).sum ≤
      (polynomials.map
        RFAP.ConstructiveRationalRootCandidates.divisorCandidateSearchSize).sum
  | [] => Nat.le_refl 0
  | polynomial :: remaining => by
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (candidatePool_length_le polynomial)
        (sum_candidatePool_length_le remaining)

theorem searchedHornerTestCount_le (input : Gaussian) (degree : RootDegree) :
    searchedHornerTestCount input degree ≤
      searchedHornerTestBound input degree :=
  sum_candidatePool_length_le (searchPolynomials input degree)

def finalPowerWork (input : Gaussian) (degree : RootDegree) : Work :=
  Work.sum ((derivedCandidates input degree).map fun candidate =>
    powerTestWork input candidate degree.value)

/-- The six visible phases requested by the complexity account.  Endpoint
divisor enumeration is split out as a seventh field rather than hidden in
clearance or Horner evaluation. -/
structure RootSearchAccount where
  coefficientClearance : Nat
  sparsePolynomialConstruction : Nat
  endpointDivisorEnumeration : Nat
  rationalNormalization : Nat
  exactHornerTests : Nat
  duplicateRemoval : Nat
  exactPowerTests : Nat
  hornerTestCount : Nat
  duplicateComparisonCount : Nat
  powerTestCount : Nat
deriving DecidableEq, Repr

namespace RootSearchAccount

def total (account : RootSearchAccount) : Nat :=
  account.coefficientClearance +
    account.sparsePolynomialConstruction +
    account.endpointDivisorEnumeration +
    account.rationalNormalization +
    account.exactHornerTests +
    account.duplicateRemoval +
    account.exactPowerTests

end RootSearchAccount

/-- Fully executable bit-work ledger for one displayed input and positive
degree.  All intermediate widths are computed from finite rational data. -/
def account (input : Gaussian) (degree : RootDegree) : RootSearchAccount :=
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
      duplicateRemovalCost (rawDerivedCandidates input degree)
    exactPowerTests := power.core
    hornerTestCount := searchedHornerTestCount input degree
    duplicateComparisonCount :=
      duplicateComparisonCount (rawDerivedCandidates input degree)
    powerTestCount := (derivedCandidates input degree).length }

def chargedBitComplexity (input : Gaussian) (degree : RootDegree) : Nat :=
  (account input degree).total

theorem powerTestCount_le (input : Gaussian) (degree : RootDegree) :
    (account input degree).powerTestCount ≤
      automaticCandidateSearchSize input degree := by
  exact derivedCandidates_length_le input degree

theorem duplicateComparisonCount_le (input : Gaussian)
    (degree : RootDegree) :
    (account input degree).duplicateComparisonCount ≤
      (rawDerivedCandidates input degree).length ^ 2 := by
  change duplicateComparisonCount (rawDerivedCandidates input degree) ≤ _
  simpa only [pow_two] using
    duplicateComparisonCount_le_square
      (rawDerivedCandidates input degree)

theorem duplicateComparisonCount_le_candidate_square (input : Gaussian)
    (degree : RootDegree) :
    (account input degree).duplicateComparisonCount ≤
      (automaticCandidateSearchSize input degree) ^ 2 := by
  exact (duplicateComparisonCount_le input degree).trans
    (Nat.pow_le_pow_left
      (rawDerivedCandidates_length_le input degree) 2)

/-- The final exact-root output and every charged phase share one finite
candidate bound.  This is the public bit-complexity theorem: it exposes the
computed binary work ledger, the exact test counts, and the already-proved
root-list bound together. -/
theorem automaticExactRoots_bit_complexity
    (input : Gaussian) (degree : RootDegree) :
    chargedBitComplexity input degree = (account input degree).total ∧
      (automaticExactRoots input degree).length ≤
        automaticCandidateSearchSize input degree ∧
      (account input degree).powerTestCount ≤
        automaticCandidateSearchSize input degree ∧
      (account input degree).hornerTestCount ≤
        searchedHornerTestBound input degree ∧
      (account input degree).duplicateComparisonCount ≤
        (automaticCandidateSearchSize input degree) ^ 2 := by
  exact ⟨rfl, automaticExactRoots_length_le input degree,
    powerTestCount_le input degree, searchedHornerTestCount_le input degree,
    duplicateComparisonCount_le_candidate_square input degree⟩

end CCL.RootPowerBitComplexity
