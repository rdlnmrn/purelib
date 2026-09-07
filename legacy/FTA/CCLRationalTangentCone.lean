import FTA.CCLSectorTangent

/-!
# Exact rational tangent cones

The fixed eight-direction compass is sufficient for one parser sector, whose
two possible gradients are orthogonal, but an arbitrary finite history can
rotate several boundary half-planes by unrelated rational homographies.  This
module solves the resulting strict homogeneous linear feasibility problem
exactly over `ℚ`.

Every nonvertical direction can be positively rescaled so that its real
coordinate is `1` or `-1`.  The remaining inequalities are strict rational
lower and upper bounds on its imaginary coordinate.  Their finite maximum and
minimum give one explicit rational midpoint.  The two vertical directions
complete the search.
-/

namespace FTA
namespace CCLRationalTangentCone

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLSectorTangent

abbrev QI := CCL.GaussianRat

/-- Rational dot product used by a homogeneous open half-plane. -/
def dot (normal direction : QI) : ℚ :=
  normal.re * direction.re + normal.im * direction.im

/-- Strict feasibility test for a finite list of rational half-plane normals. -/
def normalsPositive? (normals : List QI) (direction : QI) : Bool :=
  normals.all fun normal => decide (0 < dot normal direction)

theorem normalsPositive?_eq_true_iff
    (normals : List QI) (direction : QI) :
    normalsPositive? normals direction = true ↔
      ∀ normal ∈ normals, 0 < dot normal direction := by
  simp [normalsPositive?]

/-- Lower slope bounds for directions whose real coordinate is fixed to
`x`.  A normal with positive imaginary coordinate contributes
`-(normal.re*x)/normal.im < y`. -/
def lowerBounds (normals : List QI) (x : ℚ) : List ℚ :=
  normals.filterMap fun normal =>
    if 0 < normal.im then some (-(normal.re * x) / normal.im) else none

/-- Upper slope bounds for directions whose real coordinate is fixed to
`x`.  A normal with negative imaginary coordinate contributes
`y < -(normal.re*x)/normal.im`. -/
def upperBounds (normals : List QI) (x : ℚ) : List ℚ :=
  normals.filterMap fun normal =>
    if normal.im < 0 then some (-(normal.re * x) / normal.im) else none

/-- One rational point in the open interval described by two finite bound
lists whenever that interval is inhabited.  In inconsistent cases this is
merely a candidate and the final Boolean feasibility check rejects it. -/
def openIntervalCandidate (lowers uppers : List ℚ) : ℚ :=
  match lowers.max?, uppers.min? with
  | none, none => 0
  | some lower, none => lower + 1
  | none, some upper => upper - 1
  | some lower, some upper => (lower + upper) / 2

theorem openIntervalCandidate_between
    (lowers uppers : List ℚ) (witness : ℚ)
    (lowerWitness : ∀ lower ∈ lowers, lower < witness)
    (upperWitness : ∀ upper ∈ uppers, witness < upper) :
    (∀ lower ∈ lowers,
        lower < openIntervalCandidate lowers uppers) ∧
      (∀ upper ∈ uppers,
        openIntervalCandidate lowers uppers < upper) := by
  unfold openIntervalCandidate
  cases lowerMax : lowers.max? with
  | none =>
      have lowersEmpty : lowers = [] :=
        List.max?_eq_none_iff.mp lowerMax
      cases upperMin : uppers.min? with
      | none =>
          have uppersEmpty : uppers = [] :=
            List.min?_eq_none_iff.mp upperMin
          simp [lowersEmpty, uppersEmpty]
      | some upper =>
          have upperSpec := List.min?_eq_some_iff.mp upperMin
          constructor
          · simp [lowersEmpty]
          · intro candidate candidateMember
            have upperLe : upper ≤ candidate :=
              upperSpec.2 candidate candidateMember
            linarith
  | some lower =>
      have lowerSpec := List.max?_eq_some_iff.mp lowerMax
      cases upperMin : uppers.min? with
      | none =>
          have uppersEmpty : uppers = [] :=
            List.min?_eq_none_iff.mp upperMin
          constructor
          · intro candidate candidateMember
            have candidateLe : candidate ≤ lower :=
              lowerSpec.2 candidate candidateMember
            linarith
          · simp [uppersEmpty]
      | some upper =>
          have upperSpec := List.min?_eq_some_iff.mp upperMin
          have lowerLtWitness : lower < witness :=
            lowerWitness lower lowerSpec.1
          have witnessLtUpper : witness < upper :=
            upperWitness upper upperSpec.1
          constructor
          · intro candidate candidateMember
            have candidateLe : candidate ≤ lower :=
              lowerSpec.2 candidate candidateMember
            linarith
          · intro candidate candidateMember
            have upperLe : upper ≤ candidate :=
              upperSpec.2 candidate candidateMember
            linarith

/-- Candidate with prescribed nonzero real coordinate. -/
def normalizedCandidate (normals : List QI) (x : ℚ) : QI :=
  ⟨x, openIntervalCandidate (lowerBounds normals x)
    (upperBounds normals x)⟩

/-- If one imaginary coordinate works after fixing the real coordinate, the
computed maximum/minimum candidate works as well. -/
theorem normalizedCandidate_slopes_of_witness
    (normals : List QI) (x witness : ℚ)
    (slopes : ∀ normal ∈ normals,
      0 < normal.re * x + normal.im * witness) :
    ∀ normal ∈ normals, 0 < dot normal (normalizedCandidate normals x) := by
  have lowerWitness : ∀ lower ∈ lowerBounds normals x,
      lower < witness := by
    intro lower lowerMember
    rcases List.mem_filterMap.mp lowerMember with
      ⟨normal, normalMember, equality⟩
    split at equality
    · rename_i imagPositive
      cases equality
      apply (div_lt_iff₀ imagPositive).2
      have positive := slopes normal normalMember
      linarith
    · contradiction
  have upperWitness : ∀ upper ∈ upperBounds normals x,
      witness < upper := by
    intro upper upperMember
    rcases List.mem_filterMap.mp upperMember with
      ⟨normal, normalMember, equality⟩
    split at equality
    · rename_i imagNegative
      cases equality
      apply (lt_div_iff_of_neg imagNegative).2
      have positive := slopes normal normalMember
      linarith
    · contradiction
  have bounds := openIntervalCandidate_between
    (lowerBounds normals x) (upperBounds normals x) witness
    lowerWitness upperWitness
  intro normal normalMember
  by_cases imagPositive : 0 < normal.im
  · have lowerMember : -(normal.re * x) / normal.im ∈
        lowerBounds normals x := by
      rw [lowerBounds, List.mem_filterMap]
      exact ⟨normal, normalMember, by simp [imagPositive]⟩
    have lower := bounds.1 _ lowerMember
    change 0 < normal.re * x + normal.im *
      openIntervalCandidate (lowerBounds normals x)
        (upperBounds normals x)
    have scaled := (div_lt_iff₀ imagPositive).1 lower
    linarith
  · by_cases imagNegative : normal.im < 0
    · have upperMember : -(normal.re * x) / normal.im ∈
          upperBounds normals x := by
        rw [upperBounds, List.mem_filterMap]
        exact ⟨normal, normalMember, by simp [imagNegative]⟩
      have upper := bounds.2 _ upperMember
      change 0 < normal.re * x + normal.im *
        openIntervalCandidate (lowerBounds normals x)
          (upperBounds normals x)
      have scaled := (lt_div_iff_of_neg imagNegative).1 upper
      linarith
    · have imagZero : normal.im = 0 :=
        le_antisymm (le_of_not_gt imagPositive)
          (le_of_not_gt imagNegative)
      have positive := slopes normal normalMember
      simpa [dot, normalizedCandidate, imagZero] using positive

/-- Four candidates suffice: the two vertical directions and one exact
finite-interval candidate in each nonvertical orientation. -/
def directionCandidates (normals : List QI) : List QI :=
  [⟨0, 1⟩, ⟨0, -1⟩,
    normalizedCandidate normals 1,
    normalizedCandidate normals (-1)]

/-- Exact finite strict-cone search. -/
def strictDirection? (normals : List QI) : Option QI :=
  (directionCandidates normals).find? fun direction =>
    normalsPositive? normals direction

theorem strictDirection?_some_slopes
    {normals : List QI} {direction : QI}
    (search : strictDirection? normals = some direction) :
    ∀ normal ∈ normals, 0 < dot normal direction := by
  apply (normalsPositive?_eq_true_iff normals direction).1
  exact List.find?_some search

/-- Completeness of the four-candidate solver: every inhabited strict
rational cone yields a successful executable search. -/
theorem strictDirection?_isSome_of_exists
    (normals : List QI)
    (existsDirection : ∃ direction : QI,
      ∀ normal ∈ normals, 0 < dot normal direction) :
    (strictDirection? normals).isSome := by
  rcases existsDirection with ⟨direction, slopes⟩
  rw [strictDirection?, List.find?_isSome]
  by_cases normalsEmpty : normals = []
  · refine ⟨⟨0, 1⟩, by simp [directionCandidates], ?_⟩
    exact (normalsPositive?_eq_true_iff _ _).2 (by simp [normalsEmpty])
  by_cases realPositive : 0 < direction.re
  · let witness := direction.im / direction.re
    let candidate := normalizedCandidate normals 1
    refine ⟨candidate, by simp [candidate, directionCandidates], ?_⟩
    apply (normalsPositive?_eq_true_iff _ _).2
    apply normalizedCandidate_slopes_of_witness normals 1 witness
    intro normal normalMember
    have original := slopes normal normalMember
    have realNonzero : direction.re ≠ 0 := realPositive.ne'
    have identity :
        direction.re *
            (normal.re * 1 + normal.im * witness) =
          dot normal direction := by
      dsimp only [witness, dot]
      field_simp [realNonzero]
    have scaled :
        0 < direction.re *
          (normal.re * 1 + normal.im * witness) := by
      rw [identity]
      exact original
    nlinarith
  · by_cases realNegative : direction.re < 0
    · let witness := direction.im / (-direction.re)
      let candidate := normalizedCandidate normals (-1)
      refine ⟨candidate, by simp [candidate, directionCandidates], ?_⟩
      apply (normalsPositive?_eq_true_iff _ _).2
      apply normalizedCandidate_slopes_of_witness normals (-1) witness
      intro normal normalMember
      have original := slopes normal normalMember
      have scalePositive : 0 < -direction.re := neg_pos.mpr realNegative
      have realNonzero : direction.re ≠ 0 := realNegative.ne
      have identity :
          (-direction.re) *
              (normal.re * (-1) + normal.im * witness) =
            dot normal direction := by
        dsimp only [witness, dot]
        field_simp [realNonzero]
        ring
      have scaled :
          0 < (-direction.re) *
            (normal.re * (-1) + normal.im * witness) := by
        rw [identity]
        exact original
      nlinarith
    · have realZero : direction.re = 0 :=
        le_antisymm (le_of_not_gt realPositive)
          (le_of_not_gt realNegative)
      have imagNonzero : direction.im ≠ 0 := by
        intro imagZero
        rcases List.exists_mem_of_ne_nil normals normalsEmpty with
          ⟨normal, normalMember⟩
        have positive := slopes normal normalMember
        simp [dot, realZero, imagZero] at positive
      by_cases imagPositive : 0 < direction.im
      · refine ⟨⟨0, 1⟩, by simp [directionCandidates], ?_⟩
        apply (normalsPositive?_eq_true_iff _ _).2
        intro normal normalMember
        have positive := slopes normal normalMember
        have product : 0 < normal.im * direction.im := by
          simpa [dot, realZero] using positive
        have normalPositive : 0 < normal.im := by
          nlinarith
        simpa [dot] using normalPositive
      · have imagNegative : direction.im < 0 := by
          apply lt_of_le_of_ne (le_of_not_gt imagPositive)
          exact imagNonzero
        refine ⟨⟨0, -1⟩, by simp [directionCandidates], ?_⟩
        apply (normalsPositive?_eq_true_iff _ _).2
        intro normal normalMember
        have positive := slopes normal normalMember
        have product : 0 < normal.im * direction.im := by
          simpa [dot, realZero] using positive
        have normalNegative : normal.im < 0 := by
          rcases mul_pos_iff.mp product with bothPositive | bothNegative
          · exact (not_lt_of_ge imagNegative.le bothPositive.2).elim
          · exact bothNegative.1
        simpa [dot] using neg_pos.mpr normalNegative

/-! ## Hermitian boundary interface -/

/-- Rational gradient normals for a finite list of oriented Hermitian owner
boundaries at one rational base point. -/
def gradientNormals (forms : List HermitianForm) (z : QI) : List QI :=
  forms.map fun form => gradientVector form z

@[simp] theorem dot_gradientVector
    (form : HermitianForm) (z direction : QI) :
    dot (gradientVector form z) direction =
      directionalSlope form z direction := rfl

/-- Exact strict tangent-cone search for arbitrary rational Hermitian
boundaries. -/
def rationalTangentDirection?
    (forms : List HermitianForm) (z : QI) : Option QI :=
  strictDirection? (gradientNormals forms z)

theorem rationalTangentDirection?_some_slopes
    {forms : List HermitianForm} {z direction : QI}
    (search : rationalTangentDirection? forms z = some direction) :
    ∀ form ∈ forms, 0 < directionalSlope form z direction := by
  intro form formMember
  have gradientMember : gradientVector form z ∈ gradientNormals forms z := by
    exact List.mem_map.mpr ⟨form, formMember, rfl⟩
  simpa using strictDirection?_some_slopes search
    (gradientVector form z) gradientMember

/-- The exact rational search is complete whenever the displayed strict
tangent cone is inhabited. -/
theorem rationalTangentDirection?_isSome_of_exists
    (forms : List HermitianForm) (z : QI)
    (existsDirection : ∃ direction : QI,
      ∀ form ∈ forms, 0 < directionalSlope form z direction) :
    (rationalTangentDirection? forms z).isSome := by
  apply strictDirection?_isSome_of_exists
  rcases existsDirection with ⟨direction, slopes⟩
  refine ⟨direction, ?_⟩
  intro normal normalMember
  rcases List.mem_map.mp normalMember with
    ⟨form, formMember, rfl⟩
  simpa using slopes form formMember

/-- Proof-bearing exact rational tangent direction.  The solver's candidate
is positively shrunk to the unit-norm convention used by the owner grid. -/
def rationalTangentDirectionCertificate?
    (forms : List HermitianForm) (z : QI) :
    Option (TangentDirection forms z) :=
  match search : rationalTangentDirection? forms z with
  | none => none
  | some direction => some
      { vector := shrinkDirection direction
        normSqLeOne := normSq_shrinkDirection_le_one direction
        slopes := by
          intro form formMember
          rw [directionalSlope_shrinkDirection]
          exact mul_pos (shrinkFactor_pos direction)
            (rationalTangentDirection?_some_slopes search form formMember) }

theorem rationalTangentDirectionCertificate?_isSome_of_exists
    (forms : List HermitianForm) (z : QI)
    (existsDirection : ∃ direction : QI,
      ∀ form ∈ forms, 0 < directionalSlope form z direction) :
    (rationalTangentDirectionCertificate? forms z).isSome := by
  have found := rationalTangentDirection?_isSome_of_exists
    forms z existsDirection
  unfold rationalTangentDirectionCertificate?
  split
  · rename_i search
    rw [search] at found
    contradiction
  · rfl

end CCLRationalTangentCone
end FTA
