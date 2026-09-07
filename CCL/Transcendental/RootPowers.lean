import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Bridge.ProjectiveRationalEvaluation
import CCL.Transcendental.SparseRootCoordinates
import RFAP.Polynomial.Multiplicity
import mathlib.RFAP.ConstructiveRationalRootCandidates

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

namespace CCL.RootPowers

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Expression := CCL.CertifiedExpression.Expression
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev PositiveEntry := RFAP.Multiplicity.PositiveEntry

open RFAP.ConstructiveGaussian.Gaussian
open CCL.OperationalFieldLaws
open CCL.TranscendentalCoherence

/-- A positive displayed natural root degree. -/
structure RootDegree where
  value : Nat
  positive : 0 < value

/-! ## The finite multi-valued root operation -/

/-- The displayed monic polynomial whose roots are the `degree.value` root
occurrences of `input`.  Coefficients are stored from highest to lowest. -/
def rootPolynomial (input : Gaussian) (degree : RootDegree) :
    GaussianPolynomial :=
  ⟨1 :: (List.replicate (degree.value - 1) 0 ++ [-input])⟩

theorem rootPolynomial_normalized (input : Gaussian) (degree : RootDegree) :
    (rootPolynomial input degree).normalize = rootPolynomial input degree := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [rootPolynomial, RFAP.ComputablePolynomial.DensePolynomial.normalize]

theorem rootPolynomial_degree (input : Gaussian) (degree : RootDegree) :
    (rootPolynomial input degree).natDegree = degree.value := by
  change
    (rootPolynomial input degree).normalize.coeffs.length - 1 = degree.value
  rw [rootPolynomial_normalized]
  have oneLe : 1 ≤ degree.value := degree.positive
  simp only [rootPolynomial, List.length_cons, List.length_append,
    List.length_replicate, List.length_nil]
  omega

private theorem evalCoeffs_append_singleton
    (point : Gaussian) (coefficients : List Gaussian)
    (trailing : Gaussian) :
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        (coefficients ++ [trailing]) =
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point coefficients *
        point + trailing := by
  simp only [RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
    QuotientFreeList.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rootPolynomial_eval (input point : Gaussian) (degree : RootDegree) :
    (rootPolynomial input degree).eval point =
      point ^ degree.value - input := by
  have predecessor : degree.value - 1 + 1 = degree.value := by
    exact Nat.sub_add_cancel degree.positive
  change
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        (1 :: (List.replicate (degree.value - 1) 0 ++ [-input])) =
      point ^ degree.value - input
  rw [show
      1 :: (List.replicate (degree.value - 1) 0 ++ [-input]) =
        ([1] ++ List.replicate (degree.value - 1) 0) ++ [-input] by
      simp only [List.cons_append, List.nil_append]]
  rw [evalCoeffs_append_singleton,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_append_replicate_zero]
  change ((0 * point + 1) * point ^ (degree.value - 1)) * point + -input =
    point ^ degree.value - input
  rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.one_mul, ← pow_succ, predecessor]
  exact RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg _ _

/-- One squarefree factor in the finite root family.  Its multiplicity counts
how many root occurrences it contributes per isolated root, while `result`
provides either its exact linear terminal or all its shrinking CCL tracks. -/
structure RootFactor where
  entry : PositiveEntry
  result : CCL.BoxRFAPBridge.PositiveResult entry.part.polynomial

namespace RootFactor

def occurrenceCount (factor : RootFactor) : Nat :=
  factor.entry.multiplicity * factor.entry.part.polynomial.natDegree

theorem multiplicityPositive (factor : RootFactor) :
    0 < factor.entry.multiplicity :=
  factor.entry.multiplicityPositive

end RootFactor

def isolateRootFactor (entry : PositiveEntry) : RootFactor :=
  { entry := entry
    result := CCL.BoxRFAPBridge.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }

/-- The exact finite preprocessing behind the public multi-valued root
operation.  It contains no chosen roots: only a finite list of exact terminals
and degree-indexed shrinking tracks. -/
structure RootFamily (input : Gaussian) (degree : RootDegree) where
  preprocessing :
    RFAP.Factorization.PositivePreprocessing (rootPolynomial input degree)

namespace RootFamily

def entries {input : Gaussian} {degree : RootDegree}
    (family : RootFamily input degree) : List PositiveEntry :=
  family.preprocessing.decomposition.positiveMultiplicityEntries

def factors {input : Gaussian} {degree : RootDegree}
    (family : RootFamily input degree) : List RootFactor :=
  family.entries.map isolateRootFactor

def occurrenceCount {input : Gaussian} {degree : RootDegree}
    (family : RootFamily input degree) : Nat :=
  RFAP.Multiplicity.positiveDegree family.entries

/-- The finite family has exactly the requested number of root occurrences.
For a nonzero radicand these are `q` distinct sites; for zero this records one
site with multiplicity `q`. -/
theorem occurrenceCount_eq_degree
    {input : Gaussian} {degree : RootDegree}
    (family : RootFamily input degree) :
    family.occurrenceCount = degree.value := by
  calc
    family.occurrenceCount =
        (rootPolynomial input degree).normalize.natDegree :=
      family.preprocessing.decomposition.positiveMultiplicityDegree
    _ = (rootPolynomial input degree).natDegree := by
      rw [RFAP.ComputablePolynomial.DensePolynomial.natDegree_normalize]
    _ = degree.value := rootPolynomial_degree input degree

@[simp] theorem factors_length
    {input : Gaussian} {degree : RootDegree}
    (family : RootFamily input degree) :
    family.factors.length = family.entries.length := by
  simp only [factors, List.length_map]

end RootFamily

/-- Run the total finite squarefree/multiplicity preprocessing for
`T^q-input`.  The positive-degree proof rules out the zero and constant
branches by inspection of the displayed coefficient list. -/
def roots (input : Gaussian) (degree : RootDegree) :
    RootFamily input degree := by
  let polynomial := rootPolynomial input degree
  have polynomialDegree : polynomial.natDegree = degree.value :=
    rootPolynomial_degree input degree
  match outcome : RFAP.Factorization.preprocess polynomial with
  | .zero certificate =>
      have countZero :=
        RFAP.ComputablePolynomial.DensePolynomial.degreeCount_eq_zero_of_isZero
          certificate
      have degreeZero : polynomial.natDegree = 0 := by
        simp only [RFAP.ComputablePolynomial.DensePolynomial.natDegree,
          countZero, Nat.zero_sub]
      rw [polynomialDegree] at degreeZero
      exact (Nat.ne_of_gt degree.positive degreeZero).elim
  | .constant _ degreeZero =>
      rw [polynomialDegree] at degreeZero
      exact (Nat.ne_of_gt degree.positive degreeZero).elim
  | .positive preprocessing =>
      exact ⟨by simpa only [polynomial] using preprocessing⟩

/-! ## Immediate promotion of displayed exact roots -/

/-- A displayed rational member of the finite root family.  Its defining
power identity is finite and decidable. -/
structure ExactRoot (input : Gaussian) (degree : RootDegree) where
  point : Gaussian
  power_eq : point ^ degree.value = input

namespace ExactRoot

theorem polynomialRoot
    {input : Gaussian} {degree : RootDegree}
    (root : ExactRoot input degree) :
    (rootPolynomial input degree).eval root.point = 0 := by
  rw [rootPolynomial_eval, root.power_eq,
    RFAP.ConstructiveGaussian.Gaussian.sub_self]

/-- A displayed exact member is encoded as a genuinely terminating CCL (or
the distinguished exact-zero terminal), never as an endless shrinking
approximation. -/
def terminal
    {input : Gaussian} {degree : RootDegree}
    (root : ExactRoot input degree) :
    CCL.BoxRFAPBridge.Terminal (rootPolynomial input degree) :=
  CCL.BoxRFAPBridge.terminalOfExactRoot
    { point := root.point, root := root.polynomialRoot }

end ExactRoot

/-- Finite exact test and promotion for one proposed Gaussian-rational root.
This is the termination boundary: no opaque progressive input is inspected
for an undecidable equality. -/
def promoteIfExact (input : Gaussian) (degree : RootDegree)
    (candidate : Gaussian) : Option (ExactRoot input degree) :=
  if power : candidate ^ degree.value = input then
    some ⟨candidate, power⟩
  else
    none

theorem promoteIfExact_eq_some
    (input : Gaussian) (degree : RootDegree) (candidate : Gaussian)
    (power : candidate ^ degree.value = input) :
    promoteIfExact input degree candidate = some ⟨candidate, power⟩ := by
  simp only [promoteIfExact, dif_pos power]

theorem promoteIfExact_eq_none
    (input : Gaussian) (degree : RootDegree) (candidate : Gaussian)
    (power : candidate ^ degree.value ≠ input) :
    promoteIfExact input degree candidate = none := by
  simp only [promoteIfExact, dif_neg power]

/-- Check one finite batch of proposed rational roots, retaining exactly the
members whose displayed power identity succeeds. -/
def promoteCandidates (input : Gaussian) (degree : RootDegree) :
    List Gaussian → List (ExactRoot input degree)
  | [] => []
  | candidate :: remaining =>
      match promoteIfExact input degree candidate with
      | some root => root :: promoteCandidates input degree remaining
      | none => promoteCandidates input degree remaining

theorem promoteCandidates_points_sublist
    (input : Gaussian) (degree : RootDegree) :
    (candidates : List Gaussian) →
      List.Sublist
        ((promoteCandidates input degree candidates).map ExactRoot.point)
        candidates
  | [] => List.Sublist.slnil
  | candidate :: remaining => by
      rw [promoteCandidates]
      split
      · rename_i root promoted
        have pointEqual : root.point = candidate := by
          rw [promoteIfExact] at promoted
          split at promoted
          · exact congrArg ExactRoot.point (Option.some.inj promoted.symm)
          · contradiction
        rw [List.map_cons, pointEqual]
        exact List.Sublist.cons_cons candidate
          (promoteCandidates_points_sublist input degree remaining)
      · exact List.Sublist.cons candidate
          (promoteCandidates_points_sublist input degree remaining)

/-! ## Automatic sparse derivation of every rational candidate -/

abbrev CoordinatePolynomial :=
  RFAP.ConstructiveRationalRootCandidates.Polynomial

/-- The first sparse equation is `S^q-N(input)`. -/
def radiusPolynomial (input : Gaussian) (degree : RootDegree) :
    CoordinatePolynomial :=
  CCL.SparseRootCoordinates.powerPolynomial
    (normSq input) degree.value

/-- Every rational candidate for the squared norm, derived from the two
nonzero endpoint coefficients of the sparse norm equation. -/
def radiusCandidates (input : Gaussian) (degree : RootDegree) :
    List Coordinate :=
  RFAP.ConstructiveRationalRootCandidates.candidates
    (radiusPolynomial input degree)

/-- The real-coordinate Lucas equation at one displayed radius. -/
def realCoordinatePolynomial (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : CoordinatePolynomial :=
  CCL.SparseRootCoordinates.coordinatePolynomial radius input.re
    degree.value

/-- The imaginary-coordinate equation is the same recurrence after the fixed
quarter turn `-i`, which exposes the imaginary coordinate as a real one. -/
def imaginaryCoordinatePolynomial (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : CoordinatePolynomial :=
  CCL.SparseRootCoordinates.coordinatePolynomial radius
    ((CCL.SparseRootCoordinates.negativeImaginaryUnit ^
      degree.value * input).re) degree.value

theorem radiusPolynomial_coefficients_length (input : Gaussian)
    (degree : RootDegree) :
    (radiusPolynomial input degree).coeffs.length = degree.value + 1 :=
  CCL.SparseRootCoordinates.powerPolynomial_coefficients_length
    (normSq input) degree.value degree.positive

theorem realCoordinatePolynomial_coefficients_length (input : Gaussian)
    (degree : RootDegree) (radius : Coordinate) :
    (realCoordinatePolynomial input degree radius).coeffs.length =
      degree.value + 1 :=
  CCL.SparseRootCoordinates.coordinatePolynomial_coefficients_length
    radius input.re degree.value degree.positive

theorem imaginaryCoordinatePolynomial_coefficients_length (input : Gaussian)
    (degree : RootDegree) (radius : Coordinate) :
    (imaginaryCoordinatePolynomial input degree radius).coeffs.length =
      degree.value + 1 :=
  CCL.SparseRootCoordinates.coordinatePolynomial_coefficients_length
    radius
      ((CCL.SparseRootCoordinates.negativeImaginaryUnit ^
        degree.value * input).re) degree.value degree.positive

def realCoordinateCandidates (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : List Coordinate :=
  RFAP.ConstructiveRationalRootCandidates.candidates
    (realCoordinatePolynomial input degree radius)

def imaginaryCoordinateCandidates (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : List Coordinate :=
  RFAP.ConstructiveRationalRootCandidates.candidates
    (imaginaryCoordinatePolynomial input degree radius)

/-- Cartesian coordinate candidates at one already-derived rational radius. -/
def candidatesAtRadius (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : List Gaussian :=
  (realCoordinateCandidates input degree radius).flatMap fun real =>
    (imaginaryCoordinateCandidates input degree radius).map fun imaginary =>
      ({ re := real, im := imaginary } : Gaussian)

/-- Constructive duplicate removal for a finite Gaussian-rational candidate
list.  This transparent recursion also makes its size decrease immediate. -/
def deduplicateCandidates : List Gaussian → List Gaussian
  | [] => []
  | candidate :: remaining =>
      if candidate ∈ remaining then
        deduplicateCandidates remaining
      else
        candidate :: deduplicateCandidates remaining

theorem mem_deduplicateCandidates (candidate : Gaussian) :
    (values : List Gaussian) →
      candidate ∈ deduplicateCandidates values ↔ candidate ∈ values
  | [] => by simp only [deduplicateCandidates, List.not_mem_nil]
  | value :: remaining => by
      rw [deduplicateCandidates]
      split
      · rename_i duplicate
        rw [mem_deduplicateCandidates candidate remaining]
        constructor
        · exact fun member => List.mem_cons_of_mem value member
        · intro member
          rcases List.mem_cons.mp member with equal | tailMember
          · rw [equal]
            exact duplicate
          · exact tailMember
      · simp only [List.mem_cons, mem_deduplicateCandidates candidate remaining]

theorem deduplicateCandidates_length_le (values : List Gaussian) :
    (deduplicateCandidates values).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl 0
  | cons value remaining inductionHypothesis =>
      rw [deduplicateCandidates]
      split
      · exact Nat.le_succ_of_le inductionHypothesis
      · exact Nat.succ_le_succ inductionHypothesis

/-- The finite union of the coordinate products over all derived radii before
duplicate removal. -/
def rawDerivedCandidates (input : Gaussian) (degree : RootDegree) :
    List Gaussian :=
  (radiusCandidates input degree).flatMap
    (candidatesAtRadius input degree)

/-- The sparse candidate union with duplicates removed before exact power
filtering. -/
def derivedCandidates (input : Gaussian) (degree : RootDegree) :
    List Gaussian :=
  deduplicateCandidates (rawDerivedCandidates input degree)

/-- The finite size charged to one coordinate's endpoint-divisor
rational-root search.  It is computed from that eliminant's actual cleared
leading and constant coefficients. -/
def coordinateCandidateSearchSize
    (polynomial : RFAP.ConstructiveRationalRootCandidates.Polynomial) : Nat :=
  RFAP.ConstructiveRationalRootCandidates.divisorCandidateSearchSize polynomial

/-- The coordinate-product charge at one displayed radius. -/
def radiusCandidateSearchSize (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) : Nat :=
  coordinateCandidateSearchSize
      (realCoordinatePolynomial input degree radius) *
    coordinateCandidateSearchSize
      (imaginaryCoordinatePolynomial input degree radius)

/-- A bound on the Gaussian candidates reaching deduplication and the exact
power test: the finite sum of coordinate-product charges over the actually
derived radius list. -/
def automaticCandidateSearchSize (input : Gaussian) (degree : RootDegree) :
    Nat :=
  ((radiusCandidates input degree).map
    (radiusCandidateSearchSize input degree)).sum

private theorem cartesianCandidates_length
    (realCandidates imaginaryCandidates : List Coordinate) :
    (realCandidates.flatMap fun real =>
      imaginaryCandidates.map fun imaginary =>
        ({ re := real, im := imaginary } : Gaussian)).length =
      realCandidates.length * imaginaryCandidates.length := by
  induction realCandidates with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons real remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem candidatesAtRadius_length_le (input : Gaussian) (degree : RootDegree)
    (radius : Coordinate) :
    (candidatesAtRadius input degree radius).length ≤
      radiusCandidateSearchSize input degree radius := by
  rw [candidatesAtRadius,
    cartesianCandidates_length]
  exact Nat.mul_le_mul
    (RFAP.ConstructiveRationalRootCandidates.candidates_length_le
      (realCoordinatePolynomial input degree radius))
    (RFAP.ConstructiveRationalRootCandidates.candidates_length_le
      (imaginaryCoordinatePolynomial input degree radius))

private theorem candidateRadii_length_le (input : Gaussian)
    (degree : RootDegree) : ∀ radii : List Coordinate,
    (radii.flatMap (candidatesAtRadius input degree)).length ≤
      (radii.map (radiusCandidateSearchSize input degree)).sum
  | [] => Nat.le_refl 0
  | radius :: remaining => by
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.sum_cons]
      exact Nat.add_le_add
        (candidatesAtRadius_length_le input degree radius)
        (candidateRadii_length_le input degree remaining)

/-- The pre-deduplication sparse union already satisfies the summed
endpoint-divisor bound. -/
theorem rawDerivedCandidates_length_le (input : Gaussian)
    (degree : RootDegree) :
    (rawDerivedCandidates input degree).length ≤
      automaticCandidateSearchSize input degree := by
  exact candidateRadii_length_le input degree (radiusCandidates input degree)

/-- Deduplication leaves no more than the product of the two finite
coordinate divisor-search sizes. -/
theorem derivedCandidates_length_le (input : Gaussian) (degree : RootDegree) :
    (derivedCandidates input degree).length ≤
      automaticCandidateSearchSize input degree := by
  calc
    (derivedCandidates input degree).length ≤
        (rawDerivedCandidates input degree).length := by
      exact deduplicateCandidates_length_le _
    _ ≤ automaticCandidateSearchSize input degree :=
      rawDerivedCandidates_length_le input degree

/-- Every displayed exact Gaussian-rational root occurs in the automatically
derived finite list.  The proof first selects its rational squared norm and
then its two Lucas-coordinate roots; no Sylvester eliminant is constructed. -/
theorem exactRoot_mem_derivedCandidates
    {input : Gaussian} {degree : RootDegree}
    (root : ExactRoot input degree) :
    root.point ∈ derivedCandidates input degree := by
  have radiusRoot :
      (radiusPolynomial input degree).eval (normSq root.point) = 0 :=
    CCL.SparseRootCoordinates.powerPolynomial_norm_root
      degree.positive root.power_eq
  have radiusMember :
      normSq root.point ∈ radiusCandidates input degree :=
    RFAP.ConstructiveRationalRootCandidates.root_mem_candidates
      (radiusPolynomial input degree)
      (CCL.SparseRootCoordinates.powerPolynomial_nonzero
        (normSq input) degree.value degree.positive)
      (normSq root.point) radiusRoot
  have realRoot :
      (realCoordinatePolynomial input degree (normSq root.point)).eval
        root.point.re = 0 :=
    CCL.SparseRootCoordinates.coordinatePolynomial_real_root
      degree.positive root.power_eq
  have imaginaryRoot :
      (imaginaryCoordinatePolynomial input degree (normSq root.point)).eval
        root.point.im = 0 :=
    CCL.SparseRootCoordinates.coordinatePolynomial_imaginary_root
      degree.positive root.power_eq
  have realMember :=
    RFAP.ConstructiveRationalRootCandidates.root_mem_candidates
      (realCoordinatePolynomial input degree (normSq root.point))
      (CCL.SparseRootCoordinates.coordinatePolynomial_nonzero
        (normSq root.point) input.re degree.value degree.positive)
      root.point.re realRoot
  have imaginaryMember :=
    RFAP.ConstructiveRationalRootCandidates.root_mem_candidates
      (imaginaryCoordinatePolynomial input degree (normSq root.point))
      (CCL.SparseRootCoordinates.coordinatePolynomial_nonzero
        (normSq root.point)
        ((CCL.SparseRootCoordinates.negativeImaginaryUnit ^
          degree.value * input).re) degree.value degree.positive)
      root.point.im imaginaryRoot
  rw [derivedCandidates, mem_deduplicateCandidates, rawDerivedCandidates]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨normSq root.point, radiusMember, ?_⟩
  rw [candidatesAtRadius]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨root.point.re, realMember, ?_⟩
  exact QuotientFreeList.mem_map.mpr ⟨root.point.im, imaginaryMember, by
    cases root.point
    rfl⟩

/-- Automatically derive the complete finite sparse candidate family and
promote precisely the successful `q`th powers. -/
def automaticExactRoots (input : Gaussian) (degree : RootDegree) :
    List (ExactRoot input degree) :=
  promoteCandidates input degree (derivedCandidates input degree)

/-- Exact promotion cannot exceed the finite Cartesian candidate bound. -/
theorem automaticExactRoots_length_le
    (input : Gaussian) (degree : RootDegree) :
    (automaticExactRoots input degree).length ≤
      automaticCandidateSearchSize input degree := by
  have promotedSublist :=
    promoteCandidates_points_sublist input degree
      (derivedCandidates input degree)
  have promotedLength := promotedSublist.length_le
  simp only [List.length_map] at promotedLength
  exact promotedLength.trans (derivedCandidates_length_le input degree)

theorem mem_promoteCandidates_of_mem
    (input : Gaussian) (degree : RootDegree) (candidate : Gaussian)
    (power : candidate ^ degree.value = input) :
    (candidates : List Gaussian) → candidate ∈ candidates →
      candidate ∈
        (promoteCandidates input degree candidates).map ExactRoot.point
  | [], member => (List.not_mem_nil member).elim
  | head :: remaining, member => by
      rw [promoteCandidates]
      split
      · rename_i promoted promotion
        have pointEqual : promoted.point = head := by
          rw [promoteIfExact] at promotion
          split at promotion
          · exact congrArg ExactRoot.point (Option.some.inj promotion.symm)
          · contradiction
        rw [List.map_cons, List.mem_cons]
        rcases List.mem_cons.mp member with equal | tailMember
        · left
          exact equal.trans pointEqual.symm
        · right
          exact mem_promoteCandidates_of_mem input degree candidate power
            remaining tailMember
      · rcases List.mem_cons.mp member with equal | tailMember
        · subst head
          rename_i promotion
          rw [promoteIfExact, dif_pos power] at promotion
          contradiction
        · exact mem_promoteCandidates_of_mem input degree candidate power
            remaining tailMember

theorem exactRoot_mem_automaticExactRoots
    {input : Gaussian} {degree : RootDegree}
    (root : ExactRoot input degree) :
    root.point ∈
      (automaticExactRoots input degree).map ExactRoot.point := by
  unfold automaticExactRoots
  exact mem_promoteCandidates_of_mem input degree root.point root.power_eq
    (derivedCandidates input degree) (exactRoot_mem_derivedCandidates root)

/-- A degree-sharp finite list of displayed rational roots.  When this data
is available, `terminals` returns all `q` answers as exact finite CCL states.
The point list is finite data, not a set of all Gaussian rationals. -/
structure ExactRootFamily (input : Gaussian) (degree : RootDegree) where
  members : List (ExactRoot input degree)
  pointsNodup : (members.map ExactRoot.point).Nodup
  count : members.length = degree.value

namespace ExactRootFamily

/-- A finite candidate batch automatically becomes a complete exact family
when its successful, duplicate-free members already have the degree-sharp
count.  Failure merely requests another finite batch; it does not assert that
an irrational answer or an unbounded search object exists. -/
def ofCandidates? (input : Gaussian) (degree : RootDegree)
    (candidates : List Gaussian) : Option (ExactRootFamily input degree) :=
  let members := promoteCandidates input degree candidates
  if nodup : (members.map ExactRoot.point).Nodup then
    if count : members.length = degree.value then
      some ⟨members, nodup, count⟩
    else
      none
  else
    none

/-- Run the degree-sharp exact-family check on the automatically derived
finite sparse rational candidate family.  It succeeds exactly when the promoted
distinct rational roots already fill all `q` root slots. -/
def automatic? (input : Gaussian) (degree : RootDegree) :
    Option (ExactRootFamily input degree) :=
  ofCandidates? input degree (derivedCandidates input degree)

def terminals {input : Gaussian} {degree : RootDegree}
    (family : ExactRootFamily input degree) :
    List (CCL.BoxRFAPBridge.Terminal
      (rootPolynomial input degree)) :=
  family.members.map ExactRoot.terminal

theorem terminals_length {input : Gaussian} {degree : RootDegree}
    (family : ExactRootFamily input degree) :
    family.terminals.length = degree.value := by
  simp only [terminals, List.length_map, family.count]

/-- Degree-sharp maximality stated only for one additional displayed rational
candidate: if it satisfies the same finite power identity, it is already in
the checked finite family.  No carrier-wide root collection is formed. -/
theorem containsDisplayed {input : Gaussian} {degree : RootDegree}
    (family : ExactRootFamily input degree)
    (candidate : ExactRoot input degree) :
    candidate.point ∈ family.members.map ExactRoot.point := by
  by_contra absent
  let polynomial := rootPolynomial input degree
  have nonzero : polynomial.isZero = false :=
    RFAP.Linear.isZero_false_of_natDegree_pos (by
      rw [rootPolynomial_degree input degree]
      exact degree.positive)
  have nodup :
      (candidate.point :: family.members.map ExactRoot.point).Nodup :=
    List.nodup_cons.mpr ⟨absent, family.pointsNodup⟩
  have zeros : ∀ point ∈
      candidate.point :: family.members.map ExactRoot.point,
      polynomial.eval point = 0 := by
    intro point member
    rcases List.mem_cons.mp member with pointEqual | member
    · rw [pointEqual]
      exact candidate.polynomialRoot
    · rcases QuotientFreeList.mem_map.mp member with
        ⟨root, _rootMember, pointEqual⟩
      rw [← pointEqual]
      exact root.polynomialRoot
  have bound :=
    RFAP.ConstructiveFiniteRoots.nodup_zeros_length_lt_degreeCount
      polynomial nonzero
      (candidate.point :: family.members.map ExactRoot.point) nodup zeros
  have countSlots :=
    RFAP.ComputablePolynomial.DensePolynomial.natDegree_add_one_eq_degreeCount
      nonzero
  rw [List.length_cons, List.length_map, family.count] at bound
  rw [rootPolynomial_degree input degree] at countSlots
  omega

end ExactRootFamily

/-! ## Small exact-termination check -/

def squareRootDegree : RootDegree := ⟨2, by decide⟩

/-- Both complex square roots of the exact input `4` are found in one finite
candidate batch, so this example produces two terminating CCL states rather
than one arbitrarily selected branch. -/
theorem squareRootsOfFour_exact :
    (ExactRootFamily.ofCandidates? (4 : Gaussian) squareRootDegree
      [(2 : Gaussian), (-2 : Gaussian)]).isSome = true := by
  decide

def naturalGaussian (value : Nat) : Gaussian :=
  ⟨value, 0⟩

theorem naturalGaussian_ne_zero (degree : RootDegree) :
    naturalGaussian degree.value ≠ 0 := by
  intro equal
  have realEqual := congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
  change (degree.value : Coordinate) = 0 at realEqual
  have naturalZero : degree.value = 0 := by
    exact RFAP.ConstructiveFraction.natCast_injective_direct realEqual
  exact (Nat.ne_of_gt degree.positive) naturalZero

/-- Repeated finite addition of one displayed Gaussian coefficient. -/
def repeatedCoefficient (coefficient : Gaussian) : Nat → Gaussian
  | 0 => 0
  | count + 1 => coefficient + repeatedCoefficient coefficient count

theorem naturalGaussian_succ (count : Nat) :
    naturalGaussian (count + 1) = 1 + naturalGaussian count := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change ((count + 1 : Nat) : Coordinate) = 1 + (count : Coordinate)
    rw [Nat.cast_add, Nat.cast_one]
    exact RFAP.ConstructiveFraction.add_comm _ _
  · change (0 : Coordinate) = 0 + 0
    ring1

theorem repeatedCoefficient_eq (coefficient : Gaussian) :
    (count : Nat) →
      repeatedCoefficient coefficient count =
        naturalGaussian count * coefficient
  | 0 => by
      exact (RFAP.ConstructiveGaussian.Gaussian.zero_mul coefficient).symm
  | count + 1 => by
      rw [repeatedCoefficient, repeatedCoefficient_eq,
        naturalGaussian_succ]
      calc
        coefficient + naturalGaussian count * coefficient =
            1 * coefficient + naturalGaussian count * coefficient := by
          rw [RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = (1 + naturalGaussian count) * coefficient :=
          (RFAP.ConstructiveGaussian.Gaussian.right_distrib
            1 (naturalGaussian count) coefficient).symm

def inverseDegree (degree : RootDegree) : Gaussian :=
  1 / naturalGaussian degree.value

theorem repeatedCoefficient_inverseDegree (degree : RootDegree) :
    repeatedCoefficient (inverseDegree degree) degree.value = 1 := by
  rw [repeatedCoefficient_eq]
  unfold inverseDegree
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveGaussian.Gaussian.one_mul]
  exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel _
    (naturalGaussian_ne_zero degree)

/-- Finite repeated CCL addition. -/
def natSum (value : CoherentNamed) : Nat → CoherentNamed
  | 0 => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | count + 1 =>
      CCL.ProgressiveCoherence.CoherentNamed.add value
        (natSum value count)

/-- Finite repeated CCL multiplication. -/
def natPower (value : CoherentNamed) : Nat → CoherentNamed
  | 0 => CCL.ProgressiveCoherence.CoherentNamed.exact 1
  | count + 1 =>
      CCL.ProgressiveCoherence.CoherentNamed.mul value
        (natPower value count)

def scale (coefficient : Gaussian) (value : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (CCL.ProgressiveCoherence.CoherentNamed.exact coefficient)
    value

/-- Repeated addition of a scaled CCL name is operationally one multiplication
by the displayed repeated coefficient. -/
def natSum_scale (coefficient : Gaussian) (value : CoherentNamed) :
    (count : Nat) →
      NamedEquivalent
        (natSum (scale coefficient value) count).name
        (scale (repeatedCoefficient coefficient count) value).name
  | 0 =>
      CCL.OperationalEquivalence.NamedEquivalent.symm
        (by
          simpa only [natSum, scale, repeatedCoefficient,
            CCL.ProgressiveCoherence.CoherentNamed.exact,
            CCL.ProgressiveCoherence.CoherentNamed.mul] using
            coherentMul_zero_left value)
  | count + 1 => by
      let exactCoefficient :=
        CCL.ProgressiveCoherence.CoherentNamed.exact coefficient
      let previousCoefficient := repeatedCoefficient coefficient count
      let exactPrevious :=
        CCL.ProgressiveCoherence.CoherentNamed.exact
          previousCoefficient
      let combinedCoefficient := coefficient + previousCoefficient
      let exactCombined :=
        CCL.ProgressiveCoherence.CoherentNamed.exact
          combinedCoefficient
      let scaledCurrent := scale coefficient value
      let scaledPrevious := scale previousCoefficient value
      let repeatedPrevious := natSum scaledCurrent count
      have replacePrevious : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.add
            scaledCurrent.name repeatedPrevious.name)
          (CCL.ProgressiveTransducer.Named.add
            scaledCurrent.name scaledPrevious.name) :=
        coherentAdd_respects scaledCurrent scaledCurrent
          repeatedPrevious scaledPrevious
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            scaledCurrent.name)
          (natSum_scale coefficient value count)
      have collectProducts : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.add
            scaledCurrent.name scaledPrevious.name)
          (CCL.ProgressiveTransducer.Named.mul
            (CCL.ProgressiveTransducer.Named.add
              exactCoefficient.name exactPrevious.name)
            value.name) :=
        CCL.OperationalEquivalence.NamedEquivalent.symm
          (coherentAdd_mul_right exactCoefficient exactPrevious value)
      have exactCoefficientSum : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.add
            exactCoefficient.name exactPrevious.name)
          exactCombined.name := by
        simpa only [exactCoefficient, exactPrevious, exactCombined,
          combinedCoefficient,
          CCL.ProgressiveCoherence.CoherentNamed.exact] using
          CCL.ProjectiveRationalEvaluation.exactAdd_named_equivalent
            coefficient previousCoefficient
      have replaceCoefficient : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.mul
            (CCL.ProgressiveTransducer.Named.add
              exactCoefficient.name exactPrevious.name)
            value.name)
          (CCL.ProgressiveTransducer.Named.mul
            exactCombined.name value.name) :=
        coherentMul_respects
          (CCL.ProgressiveCoherence.CoherentNamed.add
            exactCoefficient exactPrevious)
          exactCombined value value exactCoefficientSum
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            value.name)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [natSum, scaledCurrent, repeatedPrevious,
          CCL.ProgressiveCoherence.CoherentNamed.add] using
          replacePrevious)
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          collectProducts
          (by
            simpa only [scale, repeatedCoefficient, combinedCoefficient,
              exactCombined,
              CCL.ProgressiveCoherence.CoherentNamed.mul,
              CCL.ProgressiveCoherence.CoherentNamed.exact] using
              replaceCoefficient))

/-- Repeated multiplication of `exp(x)` is operationally the exponential of
the corresponding finite repeated sum. -/
def automaticExp_natSum (value : CoherentNamed) :
    (count : Nat) →
      NamedEquivalent
        (natPower (CCL.TranscendentalCoherence.exp value.name)
          count).name
        (CCL.ProgressiveExpRange.named
          (natSum value count).name)
  | 0 => by
      simpa only [natPower, natSum,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        CCL.OperationalEquivalence.NamedEquivalent.symm
          automaticExp_zero
  | count + 1 => by
      let exponential :=
        CCL.TranscendentalCoherence.exp value.name
      let previousPower := natPower exponential count
      let previousSum := natSum value count
      let previousExponential :=
        CCL.TranscendentalCoherence.exp previousSum.name
      have replacePrevious : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.mul
            exponential.name previousPower.name)
          (CCL.ProgressiveTransducer.Named.mul
            exponential.name previousExponential.name) :=
        coherentMul_respects exponential exponential
          previousPower previousExponential
          (CCL.OperationalEquivalence.NamedEquivalent.refl
            exponential.name)
          (automaticExp_natSum value count)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by simpa only [natPower, exponential, previousPower,
          CCL.ProgressiveCoherence.CoherentNamed.mul] using
          replacePrevious)
        (by
          simpa only [natSum, previousSum, previousExponential,
            exponential, CCL.TranscendentalCoherence.exp,
            CCL.ProgressiveCoherence.CoherentNamed.add] using
            automaticExp_add value previousSum)

/-- One branch-selected `q`th-root CCL expression.  This is deliberately not
the public multi-valued root family `roots`. -/
def selectedRoot (input : Expression) (branch : AnchoredChart input.output)
    (degree : RootDegree) : Expression :=
  CCL.CertifiedExpression.Expression.exponential
    (CCL.CertifiedExpression.Expression.mul
      (CCL.CertifiedExpression.Expression.exact
        (inverseDegree degree))
      (CCL.CertifiedExpression.Expression.logarithm input branch))

/-- Raising the selected root to its displayed positive natural degree
reconstructs the original input operationally. -/
def selectedRoot_power_reconstructs (input : Expression)
    (branch : AnchoredChart input.output) (degree : RootDegree) :
    NamedEquivalent
      (natPower (selectedRoot input branch degree).output degree.value).name
      input.output.name := by
  let logarithm := branch.output
  let scaled := scale (inverseDegree degree) logarithm
  let rootOutput := CCL.TranscendentalCoherence.exp scaled.name
  have sumsToLogarithm : NamedEquivalent
      (natSum scaled degree.value).name logarithm.name := by
    have collect := natSum_scale (inverseDegree degree) logarithm degree.value
    have coefficientOne :
        repeatedCoefficient (inverseDegree degree) degree.value = 1 :=
      repeatedCoefficient_inverseDegree degree
    exact CCL.OperationalEquivalence.NamedEquivalent.trans collect
      (by
        rw [coefficientOne]
        exact coherentMul_one_left logarithm)
  have exponentialSums : NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (natSum scaled degree.value).name)
      (CCL.ProgressiveExpRange.named logarithm.name) :=
    automaticExp_respects (natSum scaled degree.value) logarithm sumsToLogarithm
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [selectedRoot, rootOutput, scaled, logarithm,
        scale,
        CCL.CertifiedExpression.Expression.exponential,
        CCL.CertifiedExpression.Expression.mul,
        CCL.CertifiedExpression.Expression.exact,
        CCL.CertifiedExpression.Expression.leaf,
        CCL.CertifiedExpression.Expression.logarithm] using
        automaticExp_natSum scaled degree.value)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      exponentialSums branch.exponential_inverse)

/-- Natural-numerator rational power `(p/q)` using the same displayed branch
and the explicitly repeated reciprocal-degree coefficient. -/
def naturalRationalPower (input : Expression)
    (branch : AnchoredChart input.output) (numerator : Nat)
    (denominator : RootDegree) : Expression :=
  CCL.CertifiedExpression.Expression.exponential
    (CCL.CertifiedExpression.Expression.mul
      (CCL.CertifiedExpression.Expression.exact
        (repeatedCoefficient (inverseDegree denominator) numerator))
      (CCL.CertifiedExpression.Expression.logarithm input branch))

/-- The `p/q` construction is operationally the `p`th finite power of the
branch-selected `q`th root. -/
def selectedRoot_power_to_naturalRationalPower (input : Expression)
    (branch : AnchoredChart input.output) (numerator : Nat)
    (denominator : RootDegree) :
    NamedEquivalent
      (natPower (selectedRoot input branch denominator).output numerator).name
      (naturalRationalPower input branch numerator denominator).output.name := by
  let logarithm := branch.output
  let scaled := scale (inverseDegree denominator) logarithm
  let combined :=
    scale (repeatedCoefficient (inverseDegree denominator) numerator)
      logarithm
  have sumToCombined : NamedEquivalent
      (natSum scaled numerator).name combined.name :=
    natSum_scale (inverseDegree denominator) logarithm numerator
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [selectedRoot, scaled, logarithm, scale,
        CCL.CertifiedExpression.Expression.exponential,
        CCL.CertifiedExpression.Expression.mul,
        CCL.CertifiedExpression.Expression.exact,
        CCL.CertifiedExpression.Expression.leaf,
        CCL.CertifiedExpression.Expression.logarithm] using
        automaticExp_natSum scaled numerator)
    (by
      simpa only [naturalRationalPower, combined, scaled, logarithm, scale,
        CCL.CertifiedExpression.Expression.exponential,
        CCL.CertifiedExpression.Expression.mul,
        CCL.CertifiedExpression.Expression.exact,
        CCL.CertifiedExpression.Expression.leaf,
        CCL.CertifiedExpression.Expression.logarithm,
        CCL.TranscendentalCoherence.exp] using
        automaticExp_respects (natSum scaled numerator) combined sumToCombined)

/-- A displayed rational exponent with positive denominator. -/
structure RationalExponent where
  numerator : Int
  denominator : RootDegree

def RationalExponent.coefficient (exponent : RationalExponent) : Gaussian :=
  ⟨(exponent.numerator : Coordinate) /
      (exponent.denominator.value : Coordinate), 0⟩

/-- Branch-certified rational power `exp((p/q) * log(y))` as an actual finite
CCL expression. -/
def rationalPower (input : Expression) (branch : AnchoredChart input.output)
    (exponent : RationalExponent) : Expression :=
  CCL.CertifiedExpression.Expression.exponential
    (CCL.CertifiedExpression.Expression.mul
      (CCL.CertifiedExpression.Expression.exact
        exponent.coefficient)
      (CCL.CertifiedExpression.Expression.logarithm input branch))

end CCL.RootPowers
