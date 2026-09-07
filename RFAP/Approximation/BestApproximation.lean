import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.GaussianEuclidean
import RFAP.Approximation.GaussianCoset
import RFAP.Approximation.HurwitzApproximation
import RFAP.Approximation.HurwitzGeometry

/-!
# Finite best Gaussian-rational approximations

Chevallier's lattice formulation uses two coordinate sizes: the error
`|qz-p|` and the denominator `|q|`.  This file states the same comparison
without square roots and without a completed complex carrier.  A lattice
vector is represented by its displayed Gaussian-integer pair `(p,q)`, its
first coordinate is the division-free rational error `qz-p`, and its second
coordinate is the displayed denominator `q`.

The main theorem proves directly that the two-tier best-approximation
predicate is equivalent to minimality in the corresponding closed cylinder.
All quantifiers range over supplied finite Gaussian-integer records; no
lattice completion, global enumeration, or choice principle is used.
-/

namespace RFAP.BestApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair
abbrev Fraction := RFAP.HurwitzRational.Fraction

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.HurwitzApproximation

/-- Squared first-coordinate size of the source-lattice vector represented by
`(p,q)`: the quadrance of `qz-p`. -/
def errorQuadrance (source : Gaussian) (pair : Pair) : Coordinate :=
  normSq (error source pair)

/-- Squared second-coordinate size of a displayed source-lattice vector. -/
def denominatorQuadrance (pair : Pair) : Nat :=
  normNat pair.denominator

/-- The determinant of two coefficient pairs.  Its Gaussian quadrance is the
finite coefficient substitute for the index of the sublattice they span. -/
def coefficientDeterminant (left right : Pair) : GaussianInt :=
  determinant left right

/-- The determinant quadrance of two displayed coefficient pairs. -/
def coefficientIndexQuadrance (left right : Pair) : Nat :=
  normNat (coefficientDeterminant left right)

/-- The zero numerator--denominator coefficient pair. -/
def zeroPair : Pair :=
  { numerator := 0
    denominator := 0 }

theorem pair_ext {left right : Pair}
    (numeratorEqual : left.numerator = right.numerator)
    (denominatorEqual : left.denominator = right.denominator) :
    left = right := by
  cases left
  cases right
  cases numeratorEqual
  cases denominatorEqual
  rfl

/-- A displayed integral pair represents a nonzero source-lattice vector.
The source-lattice map is injective, so this is exactly the coefficientwise
nonzero test. -/
def PairNonzero (pair : Pair) : Prop :=
  pair.numerator ≠ 0 ∨ pair.denominator ≠ 0

/-- The two displayed coordinates of the source-lattice vector represented
by `(p,q)`. -/
def sourceVector (source : Gaussian) (pair : Pair) : Gaussian × Gaussian :=
  (error source pair, toGaussian pair.denominator)

/-- The coefficient representation of a source-lattice vector is injective:
its second coordinate recovers `q`, and its first then recovers `p`. -/
theorem sourceVector_injective (source : Gaussian) :
    Function.Injective (sourceVector source) := by
  intro left right vectorEqual
  have errorEqual : error source left = error source right :=
    congrArg Prod.fst vectorEqual
  have denominatorGaussianEqual :
      toGaussian left.denominator = toGaussian right.denominator :=
    congrArg Prod.snd vectorEqual
  have denominatorEqual : left.denominator = right.denominator :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_injective
      denominatorGaussianEqual
  have numeratorGaussianEqual :
      toGaussian left.numerator = toGaussian right.numerator := by
    calc
      toGaussian left.numerator =
          source * toGaussian left.denominator - error source left := by
        unfold error
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
      _ = source * toGaussian right.denominator - error source right := by
        rw [denominatorGaussianEqual, errorEqual]
      _ = toGaussian right.numerator := by
        unfold error
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
  have numeratorEqual : left.numerator = right.numerator :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_injective
      numeratorGaussianEqual
  cases left
  cases right
  cases numeratorEqual
  cases denominatorEqual
  rfl

theorem pairNonzero_iff_ne_zeroPair (pair : Pair) :
    PairNonzero pair ↔ pair ≠ zeroPair := by
  constructor
  · intro nonzero equal
    subst pair
    rcases nonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero rfl
    · exact denominatorNonzero rfl
  · intro pairNonzero
    by_cases numeratorZero : pair.numerator = 0
    · by_cases denominatorZero : pair.denominator = 0
      · exact (pairNonzero (by
          cases pair
          cases numeratorZero
          cases denominatorZero
          rfl)).elim
      · exact Or.inr denominatorZero
    · exact Or.inl numeratorZero

@[simp] theorem sourceVector_zeroPair (source : Gaussian) :
    sourceVector source zeroPair = (0, 0) := by
  apply Prod.ext
  · change error source zeroPair = 0
    rw [error, zeroPair, toGaussian_zero,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_self]
  · rfl

/-- The coefficientwise nonzero test agrees exactly with nonzeroness of the
displayed source-lattice vector. -/
theorem pairNonzero_iff_sourceVector_ne_zero
    (source : Gaussian) (pair : Pair) :
    PairNonzero pair ↔ sourceVector source pair ≠ (0, 0) := by
  rw [pairNonzero_iff_ne_zeroPair]
  constructor
  · intro pairNonzero vectorZero
    apply pairNonzero
    apply sourceVector_injective source
    rw [sourceVector_zeroPair]
    exact vectorZero
  · intro vectorNonzero pairZero
    subst pair
    exact vectorNonzero (sourceVector_zeroPair source)

/-- The coefficient determinant is also the cross difference of the two
division-free errors. -/
theorem toGaussian_coefficientDeterminant
    (source : Gaussian) (left right : Pair) :
    toGaussian (coefficientDeterminant left right) =
      toGaussian left.denominator * error source right -
        toGaussian right.denominator * error source left := by
  unfold coefficientDeterminant determinant error
  simp only [toGaussian_sub, toGaussian_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- Chevallier's two-tier best-approximation condition, expressed with exact
quadrances.  Smaller nonzero denominators require strict improvement; at an
equal or smaller denominator the candidate may only tie the reference. -/
def IsBest (source : Gaussian) (reference : Pair) : Prop :=
  reference.denominator ≠ 0 ∧
    (∀ competitor : Pair, competitor.denominator ≠ 0 →
      denominatorQuadrance competitor < denominatorQuadrance reference →
      errorQuadrance source reference < errorQuadrance source competitor) ∧
    (∀ competitor : Pair, competitor.denominator ≠ 0 →
      denominatorQuadrance competitor ≤ denominatorQuadrance reference →
      errorQuadrance source reference ≤ errorQuadrance source competitor)

/-- The weaker lower-height condition proved unconditionally by the finite
Hurwitz--Lakein theorem. -/
def IsWeakLowerBest (source : Gaussian) (reference : Pair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ competitor : Pair, competitor.denominator ≠ 0 →
      denominatorQuadrance competitor < denominatorQuadrance reference →
      errorQuadrance source reference ≤ errorQuadrance source competitor

/-- Membership in the closed coordinate cylinder determined by `reference`.
This is the square-root-free form of the product of the two closed discs used
in the Gaussian-lattice definition. -/
def InClosedCylinder (source : Gaussian) (reference candidate : Pair) : Prop :=
  errorQuadrance source candidate ≤ errorQuadrance source reference ∧
    denominatorQuadrance candidate ≤ denominatorQuadrance reference

/-- A candidate lies on both coordinate boundaries of the reference
cylinder. -/
def OnCylinderBoundary (source : Gaussian)
    (reference candidate : Pair) : Prop :=
  errorQuadrance source candidate = errorQuadrance source reference ∧
    denominatorQuadrance candidate = denominatorQuadrance reference

/-- Minimality of the displayed vector `(qz-p,q)` in the source lattice.
The nonzero-second-coordinate clause is the `q \ne 0` side condition in the
best-approximation correspondence. -/
def IsGaussLatticeMinimal (source : Gaussian) (reference : Pair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ candidate : Pair, PairNonzero candidate →
      InClosedCylinder source reference candidate →
      OnCylinderBoundary source reference candidate

/-- A best approximation satisfies the weak comparison used by the finite
Hurwitz--Lakein theorem. -/
theorem IsBest.isWeakLowerBest {source : Gaussian} {reference : Pair}
    (best : IsBest source reference) : IsWeakLowerBest source reference := by
  refine ⟨best.1, ?_⟩
  intro competitor competitorNonzero denominatorSmaller
  exact (best.2.1 competitor competitorNonzero denominatorSmaller).le

/-- Restrict lattice minimality to candidates with nonzero denominators. -/
def IsDenominatorMinimal (source : Gaussian) (reference : Pair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ candidate : Pair, candidate.denominator ≠ 0 →
      InClosedCylinder source reference candidate →
      OnCylinderBoundary source reference candidate

theorem isBest_iff_isDenominatorMinimal
    (source : Gaussian) (reference : Pair) :
    IsBest source reference ↔ IsDenominatorMinimal source reference := by
  constructor
  · intro best
    refine ⟨best.1, ?_⟩
    intro candidate candidateNonzero inside
    rcases Nat.lt_or_eq_of_le inside.2 with denominatorSmaller |
        denominatorEqual
    · have strictlyWorse :=
        best.2.1 candidate candidateNonzero denominatorSmaller
      exact (not_lt_of_ge inside.1 strictlyWorse).elim
    · have referenceLe := best.2.2 candidate candidateNonzero
        denominatorEqual.le
      exact ⟨le_antisymm inside.1 referenceLe, denominatorEqual⟩
  · intro minimal
    refine ⟨minimal.1, ?_, ?_⟩
    · intro competitor competitorNonzero denominatorSmaller
      apply lt_of_not_ge
      intro competitorLe
      have boundary := minimal.2 competitor competitorNonzero
        ⟨competitorLe, denominatorSmaller.le⟩
      exact (Nat.ne_of_lt denominatorSmaller) boundary.2
    · intro competitor competitorNonzero denominatorNoLarger
      apply le_of_not_gt
      intro competitorStrictlyBetter
      have boundary := minimal.2 competitor competitorNonzero
        ⟨competitorStrictlyBetter.le, denominatorNoLarger⟩
      exact (ne_of_lt competitorStrictlyBetter) boundary.1

/-- At a fixed denominator, use the deterministic nearest Gaussian integer
as numerator. -/
def nearestPair (source : Gaussian) (denominator : GaussianInt) : Pair :=
  { numerator := RFAP.HurwitzNearest.nearest
      (source * toGaussian denominator)
    denominator := denominator }

@[simp] theorem nearestPair_denominator
    (source : Gaussian) (denominator : GaussianInt) :
    (nearestPair source denominator).denominator = denominator := rfl

theorem nearestPair_error (source : Gaussian) (denominator : GaussianInt) :
    error source (nearestPair source denominator) =
      RFAP.HurwitzNearest.remainder (source * toGaussian denominator) := rfl

/-- The equal-height clause forces every best approximation into the usual
nearest-integer error cylinder. -/
theorem IsBest.errorQuadrance_le_half
    {source : Gaussian} {reference : Pair} (best : IsBest source reference) :
    errorQuadrance source reference ≤ 1 / 2 := by
  calc
    errorQuadrance source reference ≤
        errorQuadrance source (nearestPair source reference.denominator) :=
      best.2.2 (nearestPair source reference.denominator) best.1 le_rfl
    _ = normSq (RFAP.HurwitzNearest.remainder
          (source * toGaussian reference.denominator)) := by
      rw [errorQuadrance, nearestPair_error]
    _ ≤ 1 / 2 := RFAP.HurwitzNearest.remainder_normSq_le_half _

private theorem one_le_errorQuadrance_of_vertical
    (source : Gaussian) {candidate : Pair}
    (numeratorNonzero : candidate.numerator ≠ 0)
    (denominatorZero : candidate.denominator = 0) :
    (1 : Coordinate) ≤ errorQuadrance source candidate := by
  have oneLeNorm : 1 ≤ normNat candidate.numerator :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_pos numeratorNonzero
  have castBound : (1 : Coordinate) ≤ (normNat candidate.numerator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct oneLeNorm
  rw [errorQuadrance, error, denominatorZero, toGaussian_zero,
    RFAP.ConstructiveGaussian.Gaussian.mul_zero]
  rw [zero_sub, normSq_neg, normSq_toGaussian]
  exact castBound

/-- The exact finite analogue of the minimal-vector/best-approximation
correspondence: a displayed pair is best precisely when its source-lattice
vector is minimal in the closed product cylinder and has nonzero second
coordinate. -/
theorem isBest_iff_isGaussLatticeMinimal
    (source : Gaussian) (reference : Pair) :
    IsBest source reference ↔ IsGaussLatticeMinimal source reference := by
  constructor
  · intro best
    have denominatorMinimal :=
      (isBest_iff_isDenominatorMinimal source reference).mp best
    refine ⟨best.1, ?_⟩
    intro candidate candidateNonzero inside
    by_cases denominatorNonzero : candidate.denominator ≠ 0
    · exact denominatorMinimal.2 candidate denominatorNonzero inside
    · have denominatorZero : candidate.denominator = 0 := by
        by_cases equal : candidate.denominator = 0
        · exact equal
        · exact (denominatorNonzero equal).elim
      have numeratorNonzero : candidate.numerator ≠ 0 := by
        rcases candidateNonzero with numeratorNonzero | impossible
        · exact numeratorNonzero
        · exact (impossible denominatorZero).elim
      have oneLeCandidate := one_le_errorQuadrance_of_vertical source
        numeratorNonzero denominatorZero
      have referenceLeHalf := best.errorQuadrance_le_half
      have impossible : (1 : Coordinate) ≤ 1 / 2 :=
        oneLeCandidate.trans (inside.1.trans referenceLeHalf)
      exact ((show ¬ ((1 : Coordinate) ≤ 1 / 2) by decide) impossible).elim
  · intro minimal
    apply (isBest_iff_isDenominatorMinimal source reference).mpr
    refine ⟨minimal.1, ?_⟩
    intro candidate candidateNonzero inside
    exact minimal.2 candidate (Or.inr candidateNonzero) inside

/-- The displayed numerator and denominator of the source itself, viewed as
an exact competitor. -/
def exactPair (source : Fraction) : Pair :=
  { numerator := source.numerator
    denominator := source.denominator }

@[simp] theorem exactPair_denominator (source : Fraction) :
    (exactPair source).denominator = source.denominator := rfl

theorem exactPair_error (source : Fraction) :
    error source.value (exactPair source) = 0 := by
  rw [error, exactPair, source.value_mul_denominator]
  exact RFAP.ConstructiveGaussian.Gaussian.sub_self _

/-- For a displayed rational source, every best approximation occurs no
later than the source's own displayed denominator height.  The exact source
pair is the finite witness excluding every larger denominator. -/
theorem IsBest.denominatorQuadrance_le_source
    {source : Fraction} {reference : Pair}
    (best : IsBest source.value reference) :
    denominatorQuadrance reference ≤ normNat source.denominator := by
  apply Nat.le_of_not_gt
  intro sourceDenominatorSmaller
  have impossible := best.2.1 (exactPair source) source.denominatorNonzero
    sourceDenominatorSmaller
  change normSq (error source.value reference) <
    normSq (error source.value (exactPair source)) at impossible
  rw [exactPair_error, normSq_zero] at impossible
  exact (not_lt_of_ge (normSq_nonneg (error source.value reference))) impossible

/-! ## Finite search bounds -/

/-- Clearing the displayed source denominator turns the rational error into
an exact Gaussian-integer record. -/
def clearedError (source : Fraction) (pair : Pair) : GaussianInt :=
  source.numerator * pair.denominator -
    pair.numerator * source.denominator

theorem toGaussian_clearedError (source : Fraction) (pair : Pair) :
    toGaussian (clearedError source pair) =
      error source.value pair * toGaussian source.denominator := by
  rw [clearedError,
    RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_sub,
    toGaussian_mul, toGaussian_mul, ← source.value_mul_denominator]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [error,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

theorem clearedError_norm_identity (source : Fraction) (pair : Pair) :
    (normNat (clearedError source pair) : Coordinate) =
      errorQuadrance source.value pair *
        (normNat source.denominator : Coordinate) := by
  rw [← normSq_toGaussian, toGaussian_clearedError, normSq_mul,
    normSq_toGaussian]
  rfl

/-- Error quadrance at most one half gives an integral cleared-error
quadrance no larger than the source denominator quadrance. -/
theorem clearedError_normNat_le_denominator
    {source : Fraction} {pair : Pair}
    (smallError : errorQuadrance source.value pair ≤ 1 / 2) :
    normNat (clearedError source pair) ≤ normNat source.denominator := by
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  have denominatorNonnegative :
      (0 : Coordinate) ≤ (normNat source.denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _)
  calc
    (normNat (clearedError source pair) : Coordinate) =
        errorQuadrance source.value pair *
          (normNat source.denominator : Coordinate) :=
      clearedError_norm_identity source pair
    _ ≤ (1 / 2 : Coordinate) *
          (normNat source.denominator : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        smallError denominatorNonnegative
    _ ≤ 1 * (normNat source.denominator : Coordinate) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Coordinate) ≤ 1 by decide) denominatorNonnegative
    _ = (normNat source.denominator : Coordinate) := by ring1

private theorem normNat_sub_le_two (left right : GaussianInt) :
    normNat (left - right) ≤ 2 * (normNat left + normNat right) := by
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  calc
    (normNat (left - right) : Coordinate) =
        normSq (toGaussian left - toGaussian right) := by
      rw [← RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_sub,
        normSq_toGaussian]
    _ ≤ 2 * (normSq (toGaussian left) + normSq (toGaussian right)) :=
      normSq_sub_le_two _ _
    _ = ((2 * (normNat left + normNat right) : Nat) : Coordinate) := by
      rw [normSq_toGaussian, normSq_toGaussian, Nat.cast_mul,
        Nat.cast_add, Nat.cast_ofNat]

/-- Cancellation of a common natural-number factor in a strict inequality,
proved directly from decidable natural order.  The more general upstream
cancellation theorem has a choice-bearing proof route, which is unnecessary
for this finite calculation. -/
theorem nat_lt_of_mul_lt_mul_left_direct {factor left right : Nat}
    (strict : factor * left < factor * right) : left < right := by
  by_cases ordered : left < right
  · exact ordered
  · have reverse : right ≤ left := Nat.le_of_not_gt ordered
    have scaledReverse : factor * right ≤ factor * left :=
      Nat.mul_le_mul_left factor reverse
    exact False.elim ((Nat.not_le_of_gt strict) scaledReverse)

theorem numerator_mul_denominator_eq (source : Fraction) (pair : Pair) :
    pair.numerator * source.denominator =
      source.numerator * pair.denominator - clearedError source pair := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [clearedError,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- A single source-computed numerator quadrance bound sufficient for every
pair with denominator no larger than the source and error at most one half. -/
def numeratorQuadranceBound (source : Fraction) : Nat :=
  2 * (normNat source.numerator * normNat source.denominator +
    normNat source.denominator)

theorem numeratorQuadrance_le_bound
    {source : Fraction} {pair : Pair}
    (denominatorBounded :
      denominatorQuadrance pair ≤ normNat source.denominator)
    (smallError : errorQuadrance source.value pair ≤ 1 / 2) :
    normNat pair.numerator ≤ numeratorQuadranceBound source := by
  have denominatorPositive := normNat_pos source.denominatorNonzero
  have clearedBound :=
    clearedError_normNat_le_denominator (source := source) (pair := pair)
      smallError
  have productBound :
      normNat (pair.numerator * source.denominator) ≤
        numeratorQuadranceBound source := by
    rw [numerator_mul_denominator_eq]
    refine (normNat_sub_le_two _ _).trans ?_
    rw [normNat_mul]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add
        (Nat.mul_le_mul_left (normNat source.numerator) denominatorBounded)
        clearedBound)
  calc
    normNat pair.numerator = normNat pair.numerator * 1 :=
      (Nat.mul_one _).symm
    _ ≤ normNat pair.numerator * normNat source.denominator :=
      Nat.mul_le_mul_left _ denominatorPositive
    _ = normNat (pair.numerator * source.denominator) :=
      (normNat_mul _ _).symm
    _ ≤ numeratorQuadranceBound source := productBound

/-- Finite rectangular over-enumeration containing every possible best pair
for this displayed rational source. -/
def candidates (source : Fraction) : List Pair :=
  (RFAP.ConstructiveGaussianHeight.GaussianInt.componentSquare
      (normNat source.denominator)).flatMap fun denominator =>
    (RFAP.ConstructiveGaussianHeight.GaussianInt.componentSquare
      (numeratorQuadranceBound source)).map fun numerator =>
        { numerator := numerator
          denominator := denominator }

private theorem length_flatMap_constant
    {Outer Inner Result : Type} (outer : List Outer) (inner : List Inner)
    (combine : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (combine left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Exact size of the finite rectangular over-enumeration. -/
@[simp] theorem candidates_length (source : Fraction) :
    (candidates source).length =
      16 * (normNat source.denominator + 1) ^ 2 *
        (numeratorQuadranceBound source + 1) ^ 2 := by
  rw [candidates, length_flatMap_constant]
  simp only [
    RFAP.ConstructiveGaussianHeight.GaussianInt.componentSquare_length]
  ring1

theorem mem_candidates_of_bounds {source : Fraction} {pair : Pair}
    (denominatorBounded :
      denominatorQuadrance pair ≤ normNat source.denominator)
    (smallError : errorQuadrance source.value pair ≤ 1 / 2) :
    pair ∈ candidates source := by
  rw [candidates]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨pair.denominator,
    RFAP.ConstructiveGaussianHeight.GaussianInt.mem_componentSquare_of_normNat_le
      denominatorBounded, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨pair.numerator,
    RFAP.ConstructiveGaussianHeight.GaussianInt.mem_componentSquare_of_normNat_le
      (numeratorQuadrance_le_bound denominatorBounded smallError), ?_⟩
  cases pair
  rfl

theorem IsBest.mem_candidates {source : Fraction} {pair : Pair}
    (best : IsBest source.value pair) : pair ∈ candidates source :=
  mem_candidates_of_bounds best.denominatorQuadrance_le_source
    best.errorQuadrance_le_half

/-! ## Executable all-best selection -/

/-- The two comparisons which one bounded candidate must satisfy relative to
the proposed best pair. -/
def RespectsCandidate (source : Fraction) (reference candidate : Pair) : Prop :=
  (candidate.denominator ≠ 0 →
      denominatorQuadrance candidate < denominatorQuadrance reference →
      errorQuadrance source.value reference <
        errorQuadrance source.value candidate) ∧
    (candidate.denominator ≠ 0 →
      denominatorQuadrance candidate ≤ denominatorQuadrance reference →
      errorQuadrance source.value reference ≤
        errorQuadrance source.value candidate)

instance respectsCandidateDecidable
    (source : Fraction) (reference candidate : Pair) :
    Decidable (RespectsCandidate source reference candidate) := by
  unfold RespectsCandidate
  infer_instance

/-- A structural finite conjunction over the displayed candidate list. -/
def EveryCandidateRespects (source : Fraction) (reference : Pair) :
    List Pair → Prop
  | [] => True
  | candidate :: remaining =>
      RespectsCandidate source reference candidate ∧
        EveryCandidateRespects source reference remaining

instance everyCandidateRespectsDecidable
    (source : Fraction) (reference : Pair) (list : List Pair) :
    Decidable (EveryCandidateRespects source reference list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons candidate remaining inductionHypothesis =>
      letI : Decidable
          (EveryCandidateRespects source reference remaining) :=
        inductionHypothesis
      change Decidable
        (RespectsCandidate source reference candidate ∧
          EveryCandidateRespects source reference remaining)
      infer_instance

theorem EveryCandidateRespects.of_mem
    {source : Fraction} {reference candidate : Pair} {list : List Pair}
    (every : EveryCandidateRespects source reference list)
    (member : candidate ∈ list) :
    RespectsCandidate source reference candidate := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change RespectsCandidate source reference head ∧
        EveryCandidateRespects source reference remaining at every
      rcases List.mem_cons.mp member with equal | tailMember
      · subst candidate
        exact every.1
      · exact inductionHypothesis every.2 tailMember

theorem everyCandidateRespects_of_forall
    {source : Fraction} {reference : Pair} {list : List Pair}
    (respects : ∀ candidate ∈ list,
      RespectsCandidate source reference candidate) :
    EveryCandidateRespects source reference list := by
  induction list with
  | nil => trivial
  | cons candidate remaining inductionHypothesis =>
      exact ⟨respects candidate List.mem_cons_self,
        inductionHypothesis (fun tail tailMember =>
          respects tail (List.mem_cons_of_mem _ tailMember))⟩

/-- Fully finite certificate checked by the all-best selector.  The first
three clauses are the proved global cutoffs; the last is a structural pass
over the explicit candidate rectangle. -/
def PassesBestTest (source : Fraction) (reference : Pair) : Prop :=
  reference.denominator ≠ 0 ∧
    denominatorQuadrance reference ≤ normNat source.denominator ∧
    errorQuadrance source.value reference ≤ 1 / 2 ∧
    EveryCandidateRespects source reference (candidates source)

instance passesBestTestDecidable (source : Fraction) (reference : Pair) :
    Decidable (PassesBestTest source reference) := by
  unfold PassesBestTest
  infer_instance

/-- The bounded executable test is extensionally exact: it accepts precisely
the best approximations quantified over all displayed Gaussian-integer
pairs. -/
theorem passesBestTest_iff_isBest (source : Fraction) (reference : Pair) :
    PassesBestTest source reference ↔ IsBest source.value reference := by
  constructor
  · intro passes
    refine ⟨passes.1, ?_, ?_⟩
    · intro competitor competitorNonzero denominatorSmaller
      apply lt_of_not_ge
      intro competitorLe
      have competitorDenominatorBounded :
          denominatorQuadrance competitor ≤ normNat source.denominator :=
        denominatorSmaller.le.trans passes.2.1
      have competitorSmallError :
          errorQuadrance source.value competitor ≤ 1 / 2 :=
        competitorLe.trans passes.2.2.1
      have member := mem_candidates_of_bounds competitorDenominatorBounded
        competitorSmallError
      have respects := EveryCandidateRespects.of_mem passes.2.2.2 member
      exact (not_lt_of_ge competitorLe
        (respects.1 competitorNonzero denominatorSmaller)).elim
    · intro competitor competitorNonzero denominatorNoLarger
      by_cases referenceLe :
          errorQuadrance source.value reference ≤
            errorQuadrance source.value competitor
      · exact referenceLe
      · have competitorLt := lt_of_not_ge referenceLe
        have competitorDenominatorBounded :
            denominatorQuadrance competitor ≤ normNat source.denominator :=
          denominatorNoLarger.trans passes.2.1
        have competitorSmallError :
            errorQuadrance source.value competitor ≤ 1 / 2 :=
          competitorLt.le.trans passes.2.2.1
        have member := mem_candidates_of_bounds competitorDenominatorBounded
          competitorSmallError
        have respects := EveryCandidateRespects.of_mem passes.2.2.2 member
        exact respects.2 competitorNonzero denominatorNoLarger
  · intro best
    refine ⟨best.1, best.denominatorQuadrance_le_source,
      best.errorQuadrance_le_half, ?_⟩
    apply everyCandidateRespects_of_forall
    intro candidate _
    exact ⟨best.2.1 candidate, best.2.2 candidate⟩

/-- Retain exactly the records carrying a successful finite best test. -/
def retainPassing (source : Fraction) : List Pair → List Pair
  | [] => []
  | candidate :: remaining =>
      if PassesBestTest source candidate then
        candidate :: retainPassing source remaining
      else
        retainPassing source remaining

theorem mem_retainPassing_iff
    (source : Fraction) (pair : Pair) (list : List Pair) :
    pair ∈ retainPassing source list ↔
      pair ∈ list ∧ PassesBestTest source pair := by
  induction list with
  | nil => simp only [retainPassing, List.not_mem_nil, false_and]
  | cons head remaining inductionHypothesis =>
      by_cases headPasses : PassesBestTest source head
      · rw [retainPassing, if_pos headPasses, List.mem_cons,
          inductionHypothesis, List.mem_cons]
        constructor
        · intro member
          rcases member with equal | tail
          · subst pair
            exact ⟨Or.inl rfl, headPasses⟩
          · exact ⟨Or.inr tail.1, tail.2⟩
        · intro member
          rcases member.1 with equal | tailMember
          · exact Or.inl equal
          · exact Or.inr ⟨tailMember, member.2⟩
      · rw [retainPassing, if_neg headPasses, inductionHypothesis,
          List.mem_cons]
        constructor
        · intro member
          exact ⟨Or.inr member.1, member.2⟩
        · intro member
          rcases member.1 with equal | tailMember
          · subst pair
            exact (headPasses member.2).elim
          · exact ⟨tailMember, member.2⟩

/-- Execute the finite search returning all and only the best approximation
pairs for a displayed rational source. -/
def allBest (source : Fraction) : List Pair :=
  retainPassing source (candidates source)

theorem retainPassing_length_le
    (source : Fraction) (list : List Pair) :
    (retainPassing source list).length ≤ list.length := by
  induction list with
  | nil => rfl
  | cons candidate remaining inductionHypothesis =>
      rw [retainPassing]
      by_cases passes : PassesBestTest source candidate
      · rw [if_pos passes, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ inductionHypothesis
      · rw [if_neg passes, List.length_cons]
        exact inductionHypothesis.trans (Nat.le_succ _)

/-- The output list is bounded by the explicit candidate count. -/
theorem allBest_length_le (source : Fraction) :
    (allBest source).length ≤
      16 * (normNat source.denominator + 1) ^ 2 *
        (numeratorQuadranceBound source + 1) ^ 2 := by
  exact (retainPassing_length_le source (candidates source)).trans_eq
    (candidates_length source)

/-- Soundness and completeness of the finite all-best algorithm. -/
theorem mem_allBest_iff_isBest (source : Fraction) (pair : Pair) :
    pair ∈ allBest source ↔ IsBest source.value pair := by
  rw [allBest, mem_retainPassing_iff]
  constructor
  · intro selected
    exact (passesBestTest_iff_isBest source pair).mp selected.2
  · intro best
    exact ⟨best.mem_candidates,
      (passesBestTest_iff_isBest source pair).mpr best⟩

/-! ## Constructive descent to a best pair -/

/-- Lexicographic comparison used for finite descent: first minimize error
quadrance, then minimize denominator quadrance among exact error ties. -/
def RankLE (source : Gaussian) (left right : Pair) : Prop :=
  errorQuadrance source left < errorQuadrance source right ∨
    (errorQuadrance source left = errorQuadrance source right ∧
      denominatorQuadrance left ≤ denominatorQuadrance right)

instance rankLEDecidable (source : Gaussian) (left right : Pair) :
    Decidable (RankLE source left right) := by
  unfold RankLE
  infer_instance

theorem rankLE_refl (source : Gaussian) (pair : Pair) :
    RankLE source pair pair :=
  Or.inr ⟨rfl, le_rfl⟩

theorem RankLE.errorQuadrance_le
    {source : Gaussian} {left right : Pair}
    (ranked : RankLE source left right) :
    errorQuadrance source left ≤ errorQuadrance source right := by
  rcases ranked with strict | tied
  · exact strict.le
  · exact tied.1.le

theorem RankLE.trans
    {source : Gaussian} {first second third : Pair}
    (firstSecond : RankLE source first second)
    (secondThird : RankLE source second third) :
    RankLE source first third := by
  rcases firstSecond with firstStrict | firstTied
  · rcases secondThird with secondStrict | secondTied
    · exact Or.inl (firstStrict.trans secondStrict)
    · rw [secondTied.1] at firstStrict
      exact Or.inl firstStrict
  · rcases secondThird with secondStrict | secondTied
    · rw [← firstTied.1] at secondStrict
      exact Or.inl secondStrict
    · exact Or.inr ⟨firstTied.1.trans secondTied.1,
        firstTied.2.trans secondTied.2⟩

theorem rankLE_total (source : Gaussian) (left right : Pair) :
    RankLE source left right ∨ RankLE source right left := by
  by_cases leftStrict :
      errorQuadrance source left < errorQuadrance source right
  · exact Or.inl (Or.inl leftStrict)
  · by_cases rightStrict :
        errorQuadrance source right < errorQuadrance source left
    · exact Or.inr (Or.inl rightStrict)
    · have errorEqual :
          errorQuadrance source left = errorQuadrance source right :=
        le_antisymm (le_of_not_gt rightStrict) (le_of_not_gt leftStrict)
      rcases Nat.le_total (denominatorQuadrance left)
          (denominatorQuadrance right) with leftLe | rightLe
      · exact Or.inl (Or.inr ⟨errorEqual, leftLe⟩)
      · exact Or.inr (Or.inr ⟨errorEqual.symm, rightLe⟩)

/-- Return a lexicographically least pair from a finite list, or `none` for
the empty list.  Ties retain the earlier displayed record. -/
def selectRankMinimum (source : Gaussian) : List Pair → Option Pair
  | [] => none
  | candidate :: remaining =>
      match selectRankMinimum source remaining with
      | none => some candidate
      | some selected =>
          if RankLE source candidate selected then some candidate
          else some selected

theorem selectRankMinimum_mem
    {source : Gaussian} {list : List Pair} {selected : Pair}
    (selection : selectRankMinimum source list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [selectRankMinimum] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectRankMinimum] at selection
      cases recursive : selectRankMinimum source remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe : RankLE source candidate recursiveSelected
          · simp only [recursive, if_pos candidateLe] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

theorem selectRankMinimum_eq_none_iff
    (source : Gaussian) (list : List Pair) :
    selectRankMinimum source list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectRankMinimum] at impossible
        cases recursive : selectRankMinimum source remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases candidateLe : RankLE source candidate selected
            · simp only [recursive, if_pos candidateLe] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe] at impossible
              cases impossible
      · intro impossible
        cases impossible

theorem selectRankMinimum_le_of_mem
    {source : Gaussian} {list : List Pair} {selected candidate : Pair}
    (selection : selectRankMinimum source list = some selected)
    (member : candidate ∈ list) :
    RankLE source selected candidate := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [selectRankMinimum] at selection
      cases recursive : selectRankMinimum source remaining with
      | none =>
          have remainingEmpty :=
            (selectRankMinimum_eq_none_iff source remaining).mp recursive
          subst remaining
          simp only [selectRankMinimum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          simp only [List.mem_singleton] at member
          subst candidate
          exact rankLE_refl source head
      | some recursiveSelected =>
          by_cases headLe : RankLE source head recursiveSelected
          · simp only [recursive, if_pos headLe] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact rankLE_refl source head
            · exact headLe.trans
                (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              rcases rankLE_total source head recursiveSelected with
                impossible | recursiveLe
              · exact (headLe impossible).elim
              · exact recursiveLe
            · exact inductionHypothesis recursive remainingMember

/-- Eligibility for the finite descent search below a supplied denominator
quadrance. -/
def HeightEligible (bound : Nat) (pair : Pair) : Prop :=
  pair.denominator ≠ 0 ∧ denominatorQuadrance pair ≤ bound

instance heightEligibleDecidable (bound : Nat) (pair : Pair) :
    Decidable (HeightEligible bound pair) := by
  unfold HeightEligible
  infer_instance

/-- The source-bounded candidate rectangle, restricted to nonzero
denominators no higher than `bound`. -/
def candidatesAtMost (source : Fraction) (bound : Nat) : List Pair :=
  (candidates source).filter fun pair => decide (HeightEligible bound pair)

theorem mem_candidatesAtMost_iff
    (source : Fraction) (bound : Nat) (pair : Pair) :
    pair ∈ candidatesAtMost source bound ↔
      pair ∈ candidates source ∧ HeightEligible bound pair := by
  simp only [candidatesAtMost, List.mem_filter, decide_eq_true_eq]

/-- Every bounded small-error pair constructively descends to a genuine best
pair with no greater denominator and no greater error. -/
theorem exists_best_below_of_small
    {source : Fraction} {candidate : Pair}
    (candidateNonzero : candidate.denominator ≠ 0)
    (denominatorBounded :
      denominatorQuadrance candidate ≤ normNat source.denominator)
    (smallError : errorQuadrance source.value candidate ≤ 1 / 2) :
    ∃ selected : Pair,
      IsBest source.value selected ∧
        denominatorQuadrance selected ≤ denominatorQuadrance candidate ∧
        errorQuadrance source.value selected ≤
          errorQuadrance source.value candidate := by
  let bound := denominatorQuadrance candidate
  let list := candidatesAtMost source bound
  have candidateMember : candidate ∈ list := by
    apply (mem_candidatesAtMost_iff source bound candidate).mpr
    exact ⟨mem_candidates_of_bounds denominatorBounded smallError,
      candidateNonzero, le_rfl⟩
  cases selection : selectRankMinimum source.value list with
  | none =>
      have listEmpty :=
        (selectRankMinimum_eq_none_iff source.value list).mp selection
      rw [listEmpty] at candidateMember
      exact (List.not_mem_nil candidateMember).elim
  | some selected =>
      have selectedMember := selectRankMinimum_mem selection
      have selectedEligible :=
        (mem_candidatesAtMost_iff source bound selected).mp selectedMember |>.2
      have selectedRanksCandidate :=
        selectRankMinimum_le_of_mem selection candidateMember
      have selectedErrorBound :
          errorQuadrance source.value selected ≤
            errorQuadrance source.value candidate :=
        selectedRanksCandidate.errorQuadrance_le
      have selectedSmall :
          errorQuadrance source.value selected ≤ 1 / 2 :=
        selectedErrorBound.trans smallError
      have selectedBest : IsBest source.value selected := by
        refine ⟨selectedEligible.1, ?_, ?_⟩
        · intro competitor competitorNonzero denominatorSmaller
          by_cases competitorSmall :
              errorQuadrance source.value competitor ≤ 1 / 2
          · have competitorDenominatorBound :
                denominatorQuadrance competitor ≤
                  normNat source.denominator :=
              denominatorSmaller.le.trans
                (selectedEligible.2.trans denominatorBounded)
            have competitorMember : competitor ∈ list := by
              apply (mem_candidatesAtMost_iff source bound competitor).mpr
              exact ⟨mem_candidates_of_bounds competitorDenominatorBound
                  competitorSmall,
                competitorNonzero,
                denominatorSmaller.le.trans selectedEligible.2⟩
            have ranked := selectRankMinimum_le_of_mem selection competitorMember
            rcases ranked with errorStrict | tied
            · exact errorStrict
            · exact ((Nat.not_le_of_gt denominatorSmaller) tied.2).elim
          · exact selectedSmall.trans_lt (lt_of_not_ge competitorSmall)
        · intro competitor competitorNonzero denominatorNoLarger
          by_cases competitorSmall :
              errorQuadrance source.value competitor ≤ 1 / 2
          · have competitorDenominatorBound :
                denominatorQuadrance competitor ≤
                  normNat source.denominator :=
              denominatorNoLarger.trans
                (selectedEligible.2.trans denominatorBounded)
            have competitorMember : competitor ∈ list := by
              apply (mem_candidatesAtMost_iff source bound competitor).mpr
              exact ⟨mem_candidates_of_bounds competitorDenominatorBound
                  competitorSmall,
                competitorNonzero,
                denominatorNoLarger.trans selectedEligible.2⟩
            have ranked :=
              selectRankMinimum_le_of_mem selection competitorMember
            exact ranked.errorQuadrance_le
          · exact (selectedSmall.trans_lt
              (lt_of_not_ge competitorSmall)).le
      exact ⟨selected, selectedBest, selectedEligible.2,
        selectedErrorBound⟩

/-! ## Consecutive minimal-vector levels -/

/-- Two best pairs are consecutive when their denominator quadrances are
strictly ordered and no best pair occurs at an intermediate quadrance.  Unit
associates and other ties at either endpoint belong to the same height level. -/
def AreConsecutiveBest (source : Gaussian) (lower upper : Pair) : Prop :=
  IsBest source lower ∧ IsBest source upper ∧
    denominatorQuadrance lower < denominatorQuadrance upper ∧
    ∀ middle : Pair, IsBest source middle →
      ¬ (denominatorQuadrance lower < denominatorQuadrance middle ∧
        denominatorQuadrance middle < denominatorQuadrance upper)

/-- The mixed open cylinder determined by a lower best error and an upper
best denominator. -/
def InOpenMixedCylinder
    (source : Gaussian) (lower upper candidate : Pair) : Prop :=
  errorQuadrance source candidate < errorQuadrance source lower ∧
    denominatorQuadrance candidate < denominatorQuadrance upper

/-- No nonzero displayed source-lattice vector lies in the mixed open
cylinder between two supplied pairs. -/
def MixedCylinderEmpty (source : Gaussian) (lower upper : Pair) : Prop :=
  ∀ candidate : Pair, PairNonzero candidate →
    ¬ InOpenMixedCylinder source lower upper candidate

/-- For displayed rational sources, the global definition by consecutive
best levels is equivalent to the local empty-open-cylinder criterion.  The
forward direction uses the executable finite descent to a best pair rather
than selecting a minimum from an infinite lattice. -/
theorem areConsecutiveBest_iff_mixedCylinderEmpty
    (source : Fraction) (lower upper : Pair) :
    AreConsecutiveBest source.value lower upper ↔
      IsBest source.value lower ∧ IsBest source.value upper ∧
        denominatorQuadrance lower < denominatorQuadrance upper ∧
        MixedCylinderEmpty source.value lower upper := by
  constructor
  · intro consecutive
    refine ⟨consecutive.1, consecutive.2.1, consecutive.2.2.1, ?_⟩
    intro candidate candidateNonzero inside
    by_cases candidateDenominatorNonzero : candidate.denominator ≠ 0
    · have candidateDenominatorBound :
          denominatorQuadrance candidate ≤ normNat source.denominator :=
        inside.2.le.trans
          consecutive.2.1.denominatorQuadrance_le_source
      have candidateSmall :
          errorQuadrance source.value candidate ≤ 1 / 2 :=
        inside.1.le.trans consecutive.1.errorQuadrance_le_half
      obtain ⟨selected, selectedBest, selectedDenominatorLe,
          selectedErrorLe⟩ :=
        exists_best_below_of_small candidateDenominatorNonzero
          candidateDenominatorBound candidateSmall
      have lowerLtSelected :
          denominatorQuadrance lower < denominatorQuadrance selected := by
        apply Nat.lt_of_not_ge
        intro selectedNoHigher
        have lowerErrorLeSelected := consecutive.1.2.2 selected
          selectedBest.1 selectedNoHigher
        exact (not_lt_of_ge
          (lowerErrorLeSelected.trans selectedErrorLe)) inside.1
      have selectedLtUpper :
          denominatorQuadrance selected < denominatorQuadrance upper :=
        selectedDenominatorLe.trans_lt inside.2
      exact consecutive.2.2.2 selected selectedBest
        ⟨lowerLtSelected, selectedLtUpper⟩
    · have denominatorZero : candidate.denominator = 0 := by
        by_cases zero : candidate.denominator = 0
        · exact zero
        · exact (candidateDenominatorNonzero zero).elim
      have numeratorNonzero : candidate.numerator ≠ 0 := by
        rcases candidateNonzero with numeratorNonzero | impossible
        · exact numeratorNonzero
        · exact (impossible denominatorZero).elim
      have oneLeCandidate := one_le_errorQuadrance_of_vertical source.value
        numeratorNonzero denominatorZero
      have impossible : (1 : Coordinate) ≤ 1 / 2 :=
        oneLeCandidate.trans
          (inside.1.le.trans consecutive.1.errorQuadrance_le_half)
      exact ((show ¬ ((1 : Coordinate) ≤ 1 / 2) by decide) impossible).elim
  · intro localData
    refine ⟨localData.1, localData.2.1, localData.2.2.1, ?_⟩
    intro middle middleBest between
    apply localData.2.2.2 middle (Or.inr middleBest.1)
    exact ⟨middleBest.2.1 lower localData.1.1 between.1, between.2⟩

/-- Best pairs at strictly different denominator levels are coefficientwise
independent.  This is the constructive part of the usual statement that two
consecutive minimal vectors span a finite-index sublattice. -/
theorem determinant_ne_zero_of_ordered_best
    {source : Gaussian} {lower upper : Pair}
    (lowerBest : IsBest source lower) (upperBest : IsBest source upper)
    (denominatorOrdered :
      denominatorQuadrance lower < denominatorQuadrance upper) :
    coefficientDeterminant lower upper ≠ 0 := by
  intro determinantZero
  have determinantIdentity :=
    toGaussian_coefficientDeterminant source lower upper
  rw [determinantZero, toGaussian_zero] at determinantIdentity
  have productIdentity :
      toGaussian lower.denominator * error source upper =
        toGaussian upper.denominator * error source lower := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · have coordinateIdentity := congrArg
        RFAP.ConstructiveGaussian.Gaussian.re determinantIdentity
      simp only [RFAP.ConstructiveGaussian.Gaussian.zero_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_re] at coordinateIdentity
      exact sub_eq_zero.mp coordinateIdentity.symm
    · have coordinateIdentity := congrArg
        RFAP.ConstructiveGaussian.Gaussian.im determinantIdentity
      simp only [RFAP.ConstructiveGaussian.Gaussian.zero_im,
        RFAP.ConstructiveGaussian.Gaussian.sub_im] at coordinateIdentity
      exact sub_eq_zero.mp coordinateIdentity.symm
  have quadranceIdentity := congrArg normSq productIdentity
  rw [normSq_mul, normSq_mul, normSq_toGaussian, normSq_toGaussian]
      at quadranceIdentity
  have upperErrorSmaller :
      errorQuadrance source upper < errorQuadrance source lower :=
    upperBest.2.1 lower lowerBest.1 denominatorOrdered
  have lowerDenominatorPositive :
      (0 : Coordinate) < (denominatorQuadrance lower : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct
      (normNat_pos lowerBest.1)
  have errorScaledStrict :
      (denominatorQuadrance lower : Coordinate) *
          errorQuadrance source upper <
        (denominatorQuadrance lower : Coordinate) *
          errorQuadrance source lower :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      lowerDenominatorPositive upperErrorSmaller
  have denominatorCastBound :
      (denominatorQuadrance lower : Coordinate) ≤
        (denominatorQuadrance upper : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct denominatorOrdered.le
  have denominatorScaledBound :
      (denominatorQuadrance lower : Coordinate) *
          errorQuadrance source lower ≤
        (denominatorQuadrance upper : Coordinate) *
          errorQuadrance source lower :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      denominatorCastBound (normSq_nonneg (error source lower))
  have productStrict := errorScaledStrict.trans_le denominatorScaledBound
  exact (ne_of_lt productStrict) quadranceIdentity

theorem AreConsecutiveBest.coefficientDeterminant_ne_zero
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper) :
    coefficientDeterminant lower upper ≠ 0 :=
  determinant_ne_zero_of_ordered_best consecutive.1 consecutive.2.1
    consecutive.2.2.1

/-- Consecutive best pairs have a positive displayed coefficient-index
quadrance. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_pos
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper) :
    0 < coefficientIndexQuadrance lower upper :=
  normNat_pos consecutive.coefficientDeterminant_ne_zero

/-- Gaussian-integer linear combination of two displayed coefficient pairs. -/
def linearCombination
    (left right : Pair) (leftCoefficient rightCoefficient : GaussianInt) : Pair :=
  { numerator :=
      leftCoefficient * left.numerator + rightCoefficient * right.numerator
    denominator :=
      leftCoefficient * left.denominator + rightCoefficient * right.denominator }

/-- Scale both displayed coefficients of a numerator--denominator pair. -/
def scalePair (coefficient : GaussianInt) (pair : Pair) : Pair :=
  { numerator := coefficient * pair.numerator
    denominator := coefficient * pair.denominator }

theorem error_scalePair
    (source : Gaussian) (coefficient : GaussianInt) (pair : Pair) :
    error source (scalePair coefficient pair) =
      toGaussian coefficient * error source pair := by
  unfold scalePair error
  simp only [toGaussian_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

theorem errorQuadrance_scalePair
    (source : Gaussian) (coefficient : GaussianInt) (pair : Pair) :
    errorQuadrance source (scalePair coefficient pair) =
      (normNat coefficient : Coordinate) * errorQuadrance source pair := by
  rw [errorQuadrance, error_scalePair, normSq_mul, normSq_toGaussian]
  rfl

theorem denominatorQuadrance_scalePair
    (coefficient : GaussianInt) (pair : Pair) :
    denominatorQuadrance (scalePair coefficient pair) =
      normNat coefficient * denominatorQuadrance pair := by
  exact normNat_mul _ _

/-- A best pair has no displayed nonunit common Gaussian-integer scale. -/
theorem IsBest.scalingCoefficient_norm_eq_one
    {source : Gaussian} {reference quotient : Pair} {coefficient : GaussianInt}
    (best : IsBest source reference)
    (quotientDenominatorNonzero : quotient.denominator ≠ 0)
    (scaled : reference = scalePair coefficient quotient) :
    normNat coefficient = 1 := by
  have coefficientNonzero : coefficient ≠ 0 := by
    intro coefficientZero
    apply best.1
    rw [scaled, coefficientZero]
    change (0 : GaussianInt) * quotient.denominator = 0
    exact RFAP.ConstructiveGaussianHeight.GaussianInt.zero_mul _
  have coefficientPositive := normNat_pos coefficientNonzero
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro coefficientGreaterThanOne
    have quotientDenominatorPositive := normNat_pos quotientDenominatorNonzero
    have denominatorSmaller :
        denominatorQuadrance quotient < denominatorQuadrance reference := by
      rw [scaled, denominatorQuadrance_scalePair]
      have scaledStrict :
          denominatorQuadrance quotient <
            normNat coefficient * denominatorQuadrance quotient := by
        change normNat quotient.denominator <
          normNat coefficient * normNat quotient.denominator
        simpa only [Nat.one_mul] using
          Nat.mul_lt_mul_of_pos_right coefficientGreaterThanOne
            quotientDenominatorPositive
      exact scaledStrict
    have bestStrict := best.2.1 quotient quotientDenominatorNonzero
      denominatorSmaller
    have quotientErrorLeReference :
        errorQuadrance source quotient ≤ errorQuadrance source reference := by
      rw [scaled, errorQuadrance_scalePair]
      have oneLeCoefficient :
          (1 : Coordinate) ≤ (normNat coefficient : Coordinate) :=
        RFAP.ConstructiveFraction.natCast_le_direct coefficientPositive
      calc
        errorQuadrance source quotient =
            (1 : Coordinate) * errorQuadrance source quotient := by ring1
        _ ≤ (normNat coefficient : Coordinate) *
              errorQuadrance source quotient :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            oneLeCoefficient (normSq_nonneg (error source quotient))
    exact (not_lt_of_ge quotientErrorLeReference) bestStrict
  · exact coefficientPositive

/-- The quotient denominator in a displayed scaling of a best pair is
automatically nonzero, so the scale itself must be a unit. -/
theorem IsBest.scalingCoefficient_norm_eq_one_of_scaled
    {source : Gaussian} {reference quotient : Pair}
    {coefficient : GaussianInt}
    (best : IsBest source reference)
    (scaled : reference = scalePair coefficient quotient) :
    normNat coefficient = 1 := by
  have quotientDenominatorNonzero : quotient.denominator ≠ 0 := by
    intro quotientDenominatorZero
    apply best.1
    rw [scaled]
    change coefficient * quotient.denominator = 0
    rw [quotientDenominatorZero,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero]
  exact best.scalingCoefficient_norm_eq_one quotientDenominatorNonzero scaled

/-! ## Explicit coefficient bases from the Gaussian Euclidean algorithm -/

/-- Divide both coefficients of a pair by their computed Gaussian gcd. -/
def gcdQuotientPair (pair : Pair) : Pair :=
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    pair.numerator pair.denominator
  { numerator := certificate.leftQuotient
    denominator := certificate.rightQuotient }

theorem gcdQuotientPair_denominator_ne_zero
    {pair : Pair} (denominatorNonzero : pair.denominator ≠ 0) :
    (gcdQuotientPair pair).denominator ≠ 0 := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    pair.numerator pair.denominator
  change certificate.rightQuotient ≠ 0
  intro quotientZero
  have factor := certificate.right_factor
  rw [quotientZero,
    RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero] at factor
  exact denominatorNonzero factor

theorem pair_eq_scalePair_euclideanGCD (pair : Pair) :
    let certificate := RFAP.GaussianEuclidean.extendedGCD
      pair.numerator pair.denominator
    pair = scalePair certificate.gcd (gcdQuotientPair pair) := by
  dsimp only
  apply pair_ext
  · exact (RFAP.GaussianEuclidean.extendedGCD
      pair.numerator pair.denominator).left_factor
  · exact (RFAP.GaussianEuclidean.extendedGCD
      pair.numerator pair.denominator).right_factor

/-- Bestness forces the computed common Gaussian divisor to be a unit. -/
theorem IsBest.euclideanGCD_norm_eq_one
    {source : Gaussian} {reference : Pair}
    (best : IsBest source reference) :
    normNat (RFAP.GaussianEuclidean.extendedGCD
      reference.numerator reference.denominator).gcd = 1 := by
  exact best.scalingCoefficient_norm_eq_one
    (gcdQuotientPair_denominator_ne_zero best.1)
    (pair_eq_scalePair_euclideanGCD reference)

/-- Complete a displayed pair to a coefficient basis using its computed
Bezout coefficients, normalized by the conjugate of its unit gcd. -/
def bezoutComplement (pair : Pair) : Pair :=
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    pair.numerator pair.denominator
  let unitScale := conj certificate.gcd
  { numerator := -(unitScale * certificate.rightCoefficient)
    denominator := unitScale * certificate.leftCoefficient }

/-- A best pair and its computed Bezout complement have determinant one. -/
theorem IsBest.coefficientDeterminant_bezoutComplement_eq_one
    {source : Gaussian} {reference : Pair}
    (best : IsBest source reference) :
    coefficientDeterminant reference (bezoutComplement reference) = 1 := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    reference.numerator reference.denominator
  have bezout := certificate.bezout
  have gcdNorm := best.euclideanGCD_norm_eq_one
  have conjugateProduct : conj certificate.gcd * certificate.gcd = 1 := by
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm,
      mul_conj, gcdNorm]
    rfl
  calc
    coefficientDeterminant reference (bezoutComplement reference) =
        conj certificate.gcd *
          (certificate.leftCoefficient * reference.numerator +
            certificate.rightCoefficient * reference.denominator) := by
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [coefficientDeterminant, determinant, bezoutComplement,
          certificate,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
        ring1
    _ = conj certificate.gcd * certificate.gcd := by rw [← bezout]
    _ = 1 := conjugateProduct

theorem IsBest.coefficientIndexQuadrance_bezoutComplement_eq_one
    {source : Gaussian} {reference : Pair}
    (best : IsBest source reference) :
    coefficientIndexQuadrance reference (bezoutComplement reference) = 1 := by
  rw [coefficientIndexQuadrance,
    best.coefficientDeterminant_bezoutComplement_eq_one]
  rfl

/-- Coefficientwise Cramer's identity.  It is the finite certificate behind
the conventional sublattice-index interpretation of the determinant. -/
theorem linearCombination_cramer
    (left right candidate : Pair) :
    linearCombination left right
        (coefficientDeterminant candidate right)
        (coefficientDeterminant left candidate) =
      scalePair (coefficientDeterminant left right) candidate := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [linearCombination, scalePair, coefficientDeterminant,
      determinant,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem linearCombination_scaleCoefficients
    (left right : Pair) (scale leftCoefficient rightCoefficient : GaussianInt) :
    linearCombination left right
        (scale * leftCoefficient) (scale * rightCoefficient) =
      scalePair scale
        (linearCombination left right leftCoefficient rightCoefficient) := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [linearCombination, scalePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- Substitute a displayed linear combination for the right-hand pair and
collect its two coefficients. -/
theorem linearCombination_nested_right
    (left complement : Pair)
    (innerLeft innerRight outerLeft outerRight : GaussianInt) :
    linearCombination left
        (linearCombination left complement innerLeft innerRight)
        outerLeft outerRight =
      linearCombination left complement
        (outerLeft + outerRight * innerLeft)
        (outerRight * innerRight) := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [linearCombination,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem scalePair_scalePair
    (left right : GaussianInt) (pair : Pair) :
    scalePair left (scalePair right pair) =
      scalePair (left * right) pair := by
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [scalePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- Multiplying the Cramer coefficients by the conjugate determinant gives an
explicit integral combination equal to the determinant quadrance times the
ambient pair. -/
theorem linearCombination_cramer_norm
    (left right candidate : Pair) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (conj determinantValue * coefficientDeterminant candidate right)
        (conj determinantValue * coefficientDeterminant left candidate) =
      scalePair (ofNat (coefficientIndexQuadrance left right)) candidate := by
  dsimp only
  rw [linearCombination_scaleCoefficients, linearCombination_cramer,
    scalePair_scalePair]
  have conjugateProduct :
      conj (coefficientDeterminant left right) *
          coefficientDeterminant left right =
        ofNat (coefficientIndexQuadrance left right) := by
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm, mul_conj]
    rfl
  rw [conjugateProduct]

/-- If the determinant quadrance is one, the displayed pairs form a genuine
coefficient basis: these are explicit coordinates for every ambient pair. -/
theorem linearCombination_cramer_of_index_one
    (left right candidate : Pair)
    (indexOne : coefficientIndexQuadrance left right = 1) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (conj determinantValue * coefficientDeterminant candidate right)
        (conj determinantValue * coefficientDeterminant left candidate) =
      candidate := by
  dsimp only
  rw [linearCombination_cramer_norm, indexOne]
  apply pair_ext <;>
    apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [scalePair, ofNat,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- First integral coordinate of `candidate` in the explicit basis completed
from the best pair `reference`. -/
def bezoutBasisFirstCoefficient (reference candidate : Pair) : GaussianInt :=
  coefficientDeterminant candidate (bezoutComplement reference)

/-- The computed Bezout complement gives explicit integral coordinates for
every ambient coefficient pair. -/
theorem IsBest.linearCombination_bezoutBasis
    {source : Gaussian} {reference : Pair}
    (best : IsBest source reference) (candidate : Pair) :
    linearCombination reference (bezoutComplement reference)
        (bezoutBasisFirstCoefficient reference candidate)
        (coefficientDeterminant reference candidate) = candidate := by
  have expansion := linearCombination_cramer_of_index_one
    reference (bezoutComplement reference) candidate
      best.coefficientIndexQuadrance_bezoutComplement_eq_one
  dsimp only at expansion
  rw [best.coefficientDeterminant_bezoutComplement_eq_one] at expansion
  rw [show conj (1 : GaussianInt) = 1 by rfl] at expansion
  simpa only [bezoutBasisFirstCoefficient,
    RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul] using expansion

/-- Membership in the ordinary Gaussian-integer span of two displayed
coefficient pairs. -/
def InCoefficientSpan (left right candidate : Pair) : Prop :=
  ∃ leftCoefficient rightCoefficient : GaussianInt,
    candidate = linearCombination left right
      leftCoefficient rightCoefficient

/-- Membership in the centered coefficient coset, written without fractional
Gaussian coefficients.  Multiplication by the determinant clears the common
denominator, and both cleared coefficients lie in the nondivisible residue
class modulo that quadrance-two determinant. -/
def InCenteredCoefficientCoset (left right candidate : Pair) : Prop :=
  let determinantValue := coefficientDeterminant left right
  ∃ leftCoefficient rightCoefficient : GaussianInt,
    ¬ RFAP.GaussianCoset.Divides determinantValue leftCoefficient ∧
    ¬ RFAP.GaussianCoset.Divides determinantValue rightCoefficient ∧
    scalePair determinantValue candidate =
      linearCombination left right leftCoefficient rightCoefficient

/-- In the index-two case the coefficient of `lower` in the explicit Bezout
basis expansion of `upper` lies in the nondivisible residue class.  Otherwise
`upper` would have a nonunit common Gaussian factor. -/
theorem IsBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two
    {source : Gaussian} {lower upper : Pair}
    (lowerBest : IsBest source lower) (upperBest : IsBest source upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    ¬ RFAP.GaussianCoset.Divides (coefficientDeterminant lower upper)
      (bezoutBasisFirstCoefficient lower upper) := by
  intro divisible
  rcases divisible with ⟨quotient, coefficientIdentity⟩
  let determinantValue := coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  have basisExpansion := lowerBest.linearCombination_bezoutBasis upper
  have scaled :
      upper = scalePair determinantValue
        (linearCombination lower complement quotient 1) := by
    calc
      upper = linearCombination lower complement
          (bezoutBasisFirstCoefficient lower upper) determinantValue :=
        basisExpansion.symm
      _ = linearCombination lower complement
          (determinantValue * quotient) (determinantValue * 1) := by
        rw [coefficientIdentity]
        apply pair_ext <;>
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [linearCombination,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im] <;>
          ring1
      _ = scalePair determinantValue
          (linearCombination lower complement quotient 1) :=
        linearCombination_scaleCoefficients lower complement
          determinantValue quotient 1
  have determinantUnit :=
    upperBest.scalingCoefficient_norm_eq_one_of_scaled scaled
  change coefficientIndexQuadrance lower upper = 1 at determinantUnit
  rw [indexTwo] at determinantUnit
  exact (show (2 : Nat) ≠ 1 by decide) determinantUnit

/-- Every ambient coefficient pair lies either in the ordinary span of two
index-two best pairs or in their centered coset.  The proof uses the explicit
Bezout basis of `lower`; no quotient lattice is formed. -/
theorem IsBest.inCoefficientSpan_or_inCenteredCoefficientCoset_of_index_two
    {source : Gaussian} {lower upper : Pair}
    (lowerBest : IsBest source lower) (upperBest : IsBest source upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (candidate : Pair) :
    InCoefficientSpan lower upper candidate ∨
      InCenteredCoefficientCoset lower upper candidate := by
  let determinantValue := coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  let upperCoefficient := bezoutBasisFirstCoefficient lower upper
  let candidateCoefficient := bezoutBasisFirstCoefficient lower candidate
  let candidateComplementCoefficient :=
    coefficientDeterminant lower candidate
  have determinantNorm : normNat determinantValue = 2 := by
    simpa only [determinantValue, coefficientIndexQuadrance] using indexTwo
  have upperCoefficientNotDivisible :
      ¬ RFAP.GaussianCoset.Divides determinantValue upperCoefficient := by
    simpa only [determinantValue, upperCoefficient] using
      lowerBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two
        upperBest indexTwo
  have upperExpansion := lowerBest.linearCombination_bezoutBasis upper
  have candidateExpansion := lowerBest.linearCombination_bezoutBasis candidate
  have upperExpansion' :
      linearCombination lower complement upperCoefficient determinantValue =
        upper := by
    simpa only [complement, upperCoefficient, determinantValue] using
      upperExpansion
  have candidateExpansion' :
      linearCombination lower complement candidateCoefficient
          candidateComplementCoefficient = candidate := by
    simpa only [complement, candidateCoefficient,
      candidateComplementCoefficient] using candidateExpansion
  rcases RFAP.GaussianCoset.coordinateEven_or_coordinateOdd
      candidateComplementCoefficient with complementEven | complementOdd
  · have complementCoefficientDivisible :
        RFAP.GaussianCoset.Divides determinantValue
          candidateComplementCoefficient :=
      (RFAP.GaussianCoset.divides_iff_coordinateEven_of_norm_two
        determinantNorm).mpr complementEven
    left
    rcases complementCoefficientDivisible with
      ⟨quotient, complementCoefficientIdentity⟩
    refine ⟨candidateCoefficient - upperCoefficient * quotient,
      quotient, ?_⟩
    calc
      candidate = linearCombination lower complement candidateCoefficient
          candidateComplementCoefficient := candidateExpansion'.symm
      _ = linearCombination lower complement
          ((candidateCoefficient - upperCoefficient * quotient) +
            quotient * upperCoefficient)
          (quotient * determinantValue) := by
        rw [complementCoefficientIdentity]
        apply pair_ext <;>
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [linearCombination,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      _ = linearCombination lower
          (linearCombination lower complement upperCoefficient
            determinantValue)
          (candidateCoefficient - upperCoefficient * quotient)
          quotient :=
        (linearCombination_nested_right lower complement upperCoefficient
          determinantValue
          (candidateCoefficient - upperCoefficient * quotient) quotient).symm
      _ = linearCombination lower upper
          (candidateCoefficient - upperCoefficient * quotient) quotient := by
        rw [upperExpansion']
  · have complementCoefficientNotDivisible :
        ¬ RFAP.GaussianCoset.Divides determinantValue
          candidateComplementCoefficient :=
      (RFAP.GaussianCoset.not_divides_iff_coordinateOdd_of_norm_two
        determinantNorm).mpr complementOdd
    right
    change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ RFAP.GaussianCoset.Divides determinantValue leftCoefficient ∧
      ¬ RFAP.GaussianCoset.Divides determinantValue rightCoefficient ∧
      scalePair determinantValue candidate =
        linearCombination lower upper leftCoefficient rightCoefficient
    refine ⟨determinantValue * candidateCoefficient -
        upperCoefficient * candidateComplementCoefficient,
      candidateComplementCoefficient, ?_,
      complementCoefficientNotDivisible, ?_⟩
    · intro leftDivisible
      have productNotDivisible :=
        RFAP.GaussianCoset.not_divides_mul_of_norm_two
          determinantNorm upperCoefficientNotDivisible
            complementCoefficientNotDivisible
      apply productNotDivisible
      rcases leftDivisible with ⟨quotient, leftIdentity⟩
      refine ⟨candidateCoefficient - quotient, ?_⟩
      have recoverProduct :
          upperCoefficient * candidateComplementCoefficient =
            determinantValue * candidateCoefficient -
              (determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      have factorDifference :
          determinantValue * candidateCoefficient -
              determinantValue * quotient =
            determinantValue * (candidateCoefficient - quotient) := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      calc
        upperCoefficient * candidateComplementCoefficient =
            determinantValue * candidateCoefficient -
              (determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) :=
          recoverProduct
        _ = determinantValue * candidateCoefficient -
              determinantValue * quotient := by rw [leftIdentity]
        _ = determinantValue * (candidateCoefficient - quotient) :=
          factorDifference
    · calc
        scalePair determinantValue candidate =
            scalePair determinantValue
              (linearCombination lower complement candidateCoefficient
                candidateComplementCoefficient) :=
          congrArg (scalePair determinantValue) candidateExpansion'.symm
        _ = linearCombination lower complement
            (determinantValue * candidateCoefficient)
            (determinantValue * candidateComplementCoefficient) :=
          (linearCombination_scaleCoefficients lower complement
            determinantValue candidateCoefficient
              candidateComplementCoefficient).symm
        _ = linearCombination lower complement
            ((determinantValue * candidateCoefficient -
                upperCoefficient * candidateComplementCoefficient) +
              candidateComplementCoefficient * upperCoefficient)
            (candidateComplementCoefficient * determinantValue) := by
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = linearCombination lower
            (linearCombination lower complement upperCoefficient
              determinantValue)
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient :=
          (linearCombination_nested_right lower complement upperCoefficient
            determinantValue
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient).symm
        _ = linearCombination lower upper
            (determinantValue * candidateCoefficient -
              upperCoefficient * candidateComplementCoefficient)
            candidateComplementCoefficient := by rw [upperExpansion']

/-- Conversely, any two cleared coefficients in the nondivisible class give
an ambient pair in the centered coset.  The witness is computed in the Bezout
basis of `lower`. -/
theorem IsBest.exists_centeredCoefficientPair_of_index_two
    {source : Gaussian} {lower upper : Pair}
    (lowerBest : IsBest source lower) (upperBest : IsBest source upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient : GaussianInt)
    (leftNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower upper) leftCoefficient)
    (rightNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower upper) rightCoefficient) :
    ∃ candidate : Pair,
      scalePair (coefficientDeterminant lower upper) candidate =
        linearCombination lower upper leftCoefficient rightCoefficient := by
  let determinantValue := coefficientDeterminant lower upper
  let complement := bezoutComplement lower
  let upperCoefficient := bezoutBasisFirstCoefficient lower upper
  have determinantNorm : normNat determinantValue = 2 := by
    simpa only [determinantValue, coefficientIndexQuadrance] using indexTwo
  have upperCoefficientNotDivisible :
      ¬ RFAP.GaussianCoset.Divides determinantValue upperCoefficient := by
    simpa only [determinantValue, upperCoefficient] using
      lowerBest.bezoutBasisFirstCoefficient_not_divisible_of_index_two
        upperBest indexTwo
  have productNotDivisible :
      ¬ RFAP.GaussianCoset.Divides determinantValue
        (upperCoefficient * rightCoefficient) :=
    RFAP.GaussianCoset.not_divides_mul_of_norm_two
      determinantNorm upperCoefficientNotDivisible rightNotDivisible
  have coefficientSumDivisible :=
    RFAP.GaussianCoset.divides_add_of_not_divides_of_norm_two
      determinantNorm leftNotDivisible productNotDivisible
  rcases coefficientSumDivisible with ⟨quotient, coefficientIdentity⟩
  let candidate := linearCombination lower complement quotient rightCoefficient
  refine ⟨candidate, ?_⟩
  have upperExpansion := lowerBest.linearCombination_bezoutBasis upper
  have upperExpansion' :
      linearCombination lower complement upperCoefficient determinantValue =
        upper := by
    simpa only [complement, upperCoefficient, determinantValue] using
      upperExpansion
  change scalePair determinantValue candidate =
    linearCombination lower upper leftCoefficient rightCoefficient
  calc
    scalePair determinantValue candidate =
        linearCombination lower complement
          (determinantValue * quotient)
          (determinantValue * rightCoefficient) :=
      (linearCombination_scaleCoefficients lower complement
        determinantValue quotient rightCoefficient).symm
    _ = linearCombination lower complement
        (leftCoefficient + rightCoefficient * upperCoefficient)
        (rightCoefficient * determinantValue) := by
      rw [← coefficientIdentity]
      apply pair_ext <;>
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [linearCombination,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
        ring1
    _ = linearCombination lower
        (linearCombination lower complement upperCoefficient
          determinantValue)
        leftCoefficient rightCoefficient :=
      (linearCombination_nested_right lower complement upperCoefficient
        determinantValue leftCoefficient rightCoefficient).symm
    _ = linearCombination lower upper leftCoefficient rightCoefficient := by
      rw [upperExpansion']

/-- In the determinant-quadrance-two case, the same displayed coefficients
express twice every ambient pair in the span.  This is the finite annihilation
certificate behind the centered index-two alternative. -/
theorem linearCombination_cramer_of_index_two
    (left right candidate : Pair)
    (indexTwo : coefficientIndexQuadrance left right = 2) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (conj determinantValue * coefficientDeterminant candidate right)
        (conj determinantValue * coefficientDeterminant left candidate) =
      scalePair (ofNat 2) candidate := by
  dsimp only
  rw [linearCombination_cramer_norm, indexTwo]

/-- Put an arbitrary second pair into a nearest-remainder normal form relative
to the explicit Bezout basis completed from a best first pair.  The returned
coefficient has at most half the determinant quadrance. -/
theorem IsBest.exists_reducedCoefficientBasis
    {source : Gaussian} {lower upper : Pair}
    (best : IsBest source lower)
    (determinantNonzero : coefficientDeterminant lower upper ≠ 0) :
    ∃ coefficient : GaussianInt, ∃ complement : Pair,
      upper = linearCombination lower complement coefficient
        (coefficientDeterminant lower upper) ∧
      2 * normNat coefficient ≤ coefficientIndexQuadrance lower upper ∧
      (4 ≤ coefficientIndexQuadrance lower upper →
        2 * (normNat coefficient + 1) ≤
            coefficientIndexQuadrance lower upper ∨
          ∃ factor : GaussianInt,
            normNat factor = 2 ∧
              coefficientDeterminant lower upper = coefficient * factor) := by
  let basisComplement := bezoutComplement lower
  let firstCoefficient := bezoutBasisFirstCoefficient lower upper
  let determinantValue := coefficientDeterminant lower upper
  let quotientFraction : RFAP.HurwitzRational.Fraction :=
    { numerator := firstCoefficient
      denominator := determinantValue
      denominatorNonzero := determinantNonzero }
  let quotient := RFAP.HurwitzRational.digit quotientFraction
  let coefficient := RFAP.HurwitzRational.remainder quotientFraction
  let adjustedComplement :=
    linearCombination lower basisComplement quotient 1
  refine ⟨coefficient, adjustedComplement, ?_, ?_, ?_⟩
  · have basisExpansion := best.linearCombination_bezoutBasis upper
    have division :=
      RFAP.HurwitzRational.digit_mul_denominator_add_remainder quotientFraction
    dsimp only [quotientFraction, firstCoefficient, determinantValue,
      quotient, coefficient] at division
    have firstIdentity :
        firstCoefficient = coefficient + determinantValue * quotient := by
      calc
        firstCoefficient = quotient * determinantValue + coefficient :=
          division.symm
        _ = coefficient + determinantValue * quotient := by
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
    calc
      upper = linearCombination lower basisComplement firstCoefficient
          determinantValue := basisExpansion.symm
      _ = linearCombination lower adjustedComplement coefficient
          determinantValue := by
        rw [firstIdentity]
        apply pair_ext <;>
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [linearCombination, adjustedComplement,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im] <;>
          ring1
  · simpa only [coefficient, quotientFraction, coefficientIndexQuadrance,
      determinantValue] using
      RFAP.HurwitzRational.twice_remainder_norm_le_denominator quotientFraction
  · intro indexAtLeastFour
    simpa only [coefficient, quotientFraction, coefficientIndexQuadrance,
      determinantValue] using
      RFAP.GaussianEuclidean.remainder_clearance_or_diagonal_factor
        quotientFraction indexAtLeastFour

theorem error_linearCombination
    (source : Gaussian) (left right : Pair)
    (leftCoefficient rightCoefficient : GaussianInt) :
    error source
        (linearCombination left right leftCoefficient rightCoefficient) =
      toGaussian leftCoefficient * error source left +
        toGaussian rightCoefficient * error source right := by
  unfold linearCombination error
  simp only [toGaussian_add, toGaussian_mul]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

/-- A unit-coefficient normal form with determinant quadrance at least four
exhibits its complement inside the mixed cylinder.  This is the exact finite
calculation used to exclude the quadrance-four and quadrance-five index
cases. -/
theorem AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
    {source : Gaussian} {lower upper complement : Pair}
    {coefficient : GaussianInt}
    (consecutive : AreConsecutiveBest source lower upper)
    (normalForm :
      upper = linearCombination lower complement coefficient
        (coefficientDeterminant lower upper))
    (clearance :
      2 * (normNat coefficient + 1) ≤
        coefficientIndexQuadrance lower upper) :
    PairNonzero complement ∧
      InOpenMixedCylinder source lower upper complement := by
  let determinantValue := coefficientDeterminant lower upper
  let indexValue := coefficientIndexQuadrance lower upper
  have upperErrorSmaller :
      errorQuadrance source upper < errorQuadrance source lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have denominatorOrdered :
      denominatorQuadrance lower < denominatorQuadrance upper :=
    consecutive.2.2.1
  have coefficientNonzero : coefficient ≠ 0 := by
    intro coefficientZero
    have scaled :
        upper = scalePair determinantValue
          (linearCombination lower complement 0 1) := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientZero]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = scalePair determinantValue
            (linearCombination lower complement 0 1) :=
          linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    change coefficientIndexQuadrance lower upper = 1 at determinantUnit
    rw [coefficientZero] at clearance
    change 2 * (normNat (0 : GaussianInt) + 1) ≤
      coefficientIndexQuadrance lower upper at clearance
    have zeroNorm : normNat (0 : GaussianInt) = 0 := rfl
    rw [zeroNorm] at clearance
    rw [determinantUnit] at clearance
    exact ((show ¬2 * (0 + 1) ≤ 1 by decide) clearance).elim
  have denominatorIdentity :=
    congrArg (fun pair : Pair => pair.denominator) normalForm
  simp only [linearCombination] at denominatorIdentity
  have complementNonzero : PairNonzero complement := by
    apply (pairNonzero_iff_ne_zeroPair complement).mpr
    intro complementZero
    have scaled : upper = scalePair coefficient lower := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = scalePair coefficient lower := by
          rw [complementZero]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination, scalePair, zeroPair,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
    have coefficientUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    have denominatorEqual := congrArg denominatorQuadrance scaled
    rw [denominatorQuadrance_scalePair, coefficientUnit, Nat.one_mul]
        at denominatorEqual
    exact (Nat.ne_of_lt denominatorOrdered) denominatorEqual.symm
  have errorIdentity := congrArg (error source) normalForm
  rw [error_linearCombination] at errorIdentity
  have scaledErrorIdentity :
      toGaussian determinantValue * error source complement =
        error source upper - toGaussian coefficient * error source lower := by
    calc
      toGaussian determinantValue * error source complement =
          (toGaussian coefficient * error source lower +
              toGaussian determinantValue * error source complement) -
            toGaussian coefficient * error source lower := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
          ring1
      _ = error source upper -
          toGaussian coefficient * error source lower :=
        congrArg
          (fun value => value -
            toGaussian coefficient * error source lower)
          errorIdentity.symm
  have errorDifferenceBound :
      normSq
          (error source upper - toGaussian coefficient * error source lower) ≤
        2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) := by
    calc
      normSq
          (error source upper - toGaussian coefficient * error source lower) ≤
          2 * (normSq (error source upper) +
            normSq (toGaussian coefficient * error source lower)) :=
        normSq_sub_le_two _ _
      _ = 2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) := by
        rw [normSq_mul, normSq_toGaussian]
        unfold errorQuadrance
        ring1
  have scaledErrorBound :
      (indexValue : Coordinate) * errorQuadrance source complement ≤
        2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) := by
    calc
      (indexValue : Coordinate) * errorQuadrance source complement =
          normSq (toGaussian determinantValue) *
            normSq (error source complement) := by
        rw [normSq_toGaussian]
        rfl
      _ = normSq (toGaussian determinantValue * error source complement) :=
        (normSq_mul _ _).symm
      _ = normSq
          (error source upper - toGaussian coefficient * error source lower) :=
        congrArg normSq scaledErrorIdentity
      _ ≤ 2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) := errorDifferenceBound
  have errorInteriorStrict :
      2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) <
        2 * ((normNat coefficient : Coordinate) + 1) *
          errorQuadrance source lower := by
    have sumStrict :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        upperErrorSmaller
          ((normNat coefficient : Coordinate) *
            errorQuadrance source lower)
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (show (0 : Coordinate) < 2 by decide) sumStrict
    calc
      2 * (errorQuadrance source upper +
          (normNat coefficient : Coordinate) *
            errorQuadrance source lower) <
          2 * (errorQuadrance source lower +
            (normNat coefficient : Coordinate) *
              errorQuadrance source lower) := scaled
      _ = 2 * ((normNat coefficient : Coordinate) + 1) *
          errorQuadrance source lower := by ring1
  have clearanceErrorLeIndexError :
      2 * ((normNat coefficient : Coordinate) + 1) *
          errorQuadrance source lower ≤
        (indexValue : Coordinate) * errorQuadrance source lower := by
    have castClearance :
        ((2 * (normNat coefficient + 1) : Nat) : Coordinate) ≤
          (indexValue : Coordinate) :=
      RFAP.ConstructiveFraction.natCast_le_direct clearance
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        castClearance (normSq_nonneg (error source lower))
    calc
      2 * ((normNat coefficient : Coordinate) + 1) *
          errorQuadrance source lower =
          ((2 * (normNat coefficient + 1) : Nat) : Coordinate) *
            errorQuadrance source lower := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      _ ≤ (indexValue : Coordinate) * errorQuadrance source lower := scaled
  have errorScaledStrict :
      (indexValue : Coordinate) * errorQuadrance source complement <
        (indexValue : Coordinate) * errorQuadrance source lower :=
    scaledErrorBound.trans_lt
      (errorInteriorStrict.trans_le clearanceErrorLeIndexError)
  have indexPositive : (0 : Coordinate) < (indexValue : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      ((Nat.mul_pos (by decide) (Nat.zero_lt_succ (normNat coefficient))).trans_le
        clearance)
  have complementErrorSmaller :
      errorQuadrance source complement < errorQuadrance source lower := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := (indexValue : Coordinate))
    · simpa only [_root_.mul_comm] using errorScaledStrict
    · exact indexPositive
  have scaledDenominatorIdentity :
      determinantValue * complement.denominator =
        upper.denominator - coefficient * lower.denominator := by
    calc
      determinantValue * complement.denominator =
          (coefficient * lower.denominator +
              determinantValue * complement.denominator) -
            coefficient * lower.denominator := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      _ = upper.denominator - coefficient * lower.denominator :=
        congrArg (fun value => value - coefficient * lower.denominator)
          denominatorIdentity.symm
  have denominatorDifferenceBound :
      normNat (upper.denominator - coefficient * lower.denominator) ≤
        2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) := by
    calc
      normNat (upper.denominator - coefficient * lower.denominator) ≤
          2 * (normNat upper.denominator +
            normNat (coefficient * lower.denominator)) :=
        normNat_sub_le_two _ _
      _ = 2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) := by
        rw [normNat_mul]
        rfl
  have scaledDenominatorBound :
      indexValue * denominatorQuadrance complement ≤
        2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) := by
    calc
      indexValue * denominatorQuadrance complement =
          normNat (determinantValue * complement.denominator) := by
        rw [normNat_mul]
        rfl
      _ = normNat (upper.denominator - coefficient * lower.denominator) :=
        congrArg normNat scaledDenominatorIdentity
      _ ≤ 2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) :=
        denominatorDifferenceBound
  have coefficientNormPositive : 0 < normNat coefficient :=
    normNat_pos coefficientNonzero
  have coefficientDenominatorStrict :
      normNat coefficient * denominatorQuadrance lower <
        normNat coefficient * denominatorQuadrance upper :=
    Nat.mul_lt_mul_of_pos_left denominatorOrdered coefficientNormPositive
  have denominatorInteriorStrict :
      2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) <
        2 * (normNat coefficient + 1) *
          denominatorQuadrance upper := by
    calc
      2 * (denominatorQuadrance upper +
          normNat coefficient * denominatorQuadrance lower) <
          2 * (denominatorQuadrance upper +
            normNat coefficient * denominatorQuadrance upper) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.add_lt_add_left coefficientDenominatorStrict _)
          (by decide)
      _ = 2 * (normNat coefficient + 1) *
          denominatorQuadrance upper := by
        ring1
  have clearanceDenominatorLeIndexDenominator :
      2 * (normNat coefficient + 1) * denominatorQuadrance upper ≤
        indexValue * denominatorQuadrance upper :=
    Nat.mul_le_mul_right (denominatorQuadrance upper) clearance
  have denominatorScaledStrict :
      indexValue * denominatorQuadrance complement <
        indexValue * denominatorQuadrance upper :=
    scaledDenominatorBound.trans_lt
      (denominatorInteriorStrict.trans_le
        clearanceDenominatorLeIndexDenominator)
  exact ⟨complementNonzero,
    complementErrorSmaller,
    nat_lt_of_mul_lt_mul_left_direct denominatorScaledStrict⟩

theorem AreConsecutiveBest.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm
    {source : Gaussian} {lower upper complement : Pair}
    {coefficient : GaussianInt}
    (consecutive : AreConsecutiveBest source lower upper)
    (normalForm :
      upper = linearCombination lower complement coefficient
        (coefficientDeterminant lower upper))
    (coefficientUnit : normNat coefficient = 1)
    (indexAtLeastFour : 4 ≤ coefficientIndexQuadrance lower upper) :
    PairNonzero complement ∧
      InOpenMixedCylinder source lower upper complement := by
  apply consecutive.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
    normalForm
  rw [coefficientUnit]
  exact indexAtLeastFour

/-- Every quadrance-two residue modulo a quadrance-five Gaussian integer has
a quadrance-one representative.  The proof is the complete finite table of
eight possible moduli and four possible residues. -/
theorem exists_unit_shift_of_norm_five_and_two
    {modulus residue : GaussianInt}
    (modulusNorm : normNat modulus = 5)
    (residueNorm : normNat residue = 2) :
    ∃ unit shift : GaussianInt,
      normNat unit = 1 ∧ residue = unit + modulus * shift := by
  have modulusCases :=
    RFAP.HurwitzGeometry.normFive_cases_of_normNat_eq_five modulusNorm
  have residueCases :=
    RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two residueNorm
  rcases modulusCases with modulusCase | modulusCase | modulusCase |
      modulusCase | modulusCase | modulusCase | modulusCase | modulusCase <;>
    rcases residueCases with residueCase | residueCase | residueCase |
      residueCase <;>
    subst modulus <;> subst residue
  all_goals first
    | exact ⟨1, 1, by decide, by decide⟩
    | exact ⟨1, -1, by decide, by decide⟩
    | exact ⟨1, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨1, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨-1, 1, by decide, by decide⟩
    | exact ⟨-1, -1, by decide, by decide⟩
    | exact ⟨-1, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨-1, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, 1, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, -1, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨⟨0, 1⟩, ⟨0, -1⟩, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, 1, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, -1, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, ⟨0, 1⟩, by decide, by decide⟩
    | exact ⟨⟨0, -1⟩, ⟨0, -1⟩, by decide, by decide⟩

/-- The determinant quadrance of consecutive best pairs cannot be four. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_ne_four
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    coefficientIndexQuadrance lower upper ≠ 4 := by
  intro indexFour
  let determinantValue := coefficientDeterminant lower upper
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, coefficientBound, _⟩ :=
    consecutive.1.exists_reducedCoefficientBasis determinantNonzero
  have coefficientSmall : normNat coefficient < 4 := by
    apply nat_lt_of_mul_lt_mul_left_direct
    exact coefficientBound.trans_lt (indexFour.trans_lt (by decide))
  rcases RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_of_lt_four
      coefficient coefficientSmall with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientEqZero :=
      RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero coefficientZero
    have scaled :
        upper = scalePair determinantValue
          (linearCombination lower complement 0 1) := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientEqZero]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = scalePair determinantValue
            (linearCombination lower complement 0 1) :=
          linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    have determinantNorm : normNat determinantValue = 4 := indexFour
    rw [determinantUnit] at determinantNorm
    exact (by decide : (1 : Nat) ≠ 4) determinantNorm
  · have witness :=
      consecutive.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm
        normalForm coefficientUnit indexFour.ge
    have cylinderEmpty :=
      (areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · have coefficientIsDiagonal :=
      RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two coefficientDiagonal
    have determinantNorm : normNat determinantValue = 4 := indexFour
    obtain ⟨factor, _, determinantFactor⟩ :=
      RFAP.HurwitzGeometry.exists_diagonal_right_factor_of_four_and_diagonal
        determinantNorm coefficientIsDiagonal
    have scaled :
        upper = scalePair coefficient
          (linearCombination lower complement 1 factor) := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (coefficient * 1) (coefficient * factor) := by
          rw [determinantFactor]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = scalePair coefficient
            (linearCombination lower complement 1 factor) :=
          linearCombination_scaleCoefficients lower complement
            coefficient 1 factor
    have coefficientMustBeUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    rw [coefficientDiagonal] at coefficientMustBeUnit
    exact (by decide : (2 : Nat) ≠ 1) coefficientMustBeUnit

/-- The determinant quadrance of consecutive best pairs cannot be five. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_ne_five
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    coefficientIndexQuadrance lower upper ≠ 5 := by
  intro indexFive
  let determinantValue := coefficientDeterminant lower upper
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, coefficientBound, _⟩ :=
    consecutive.1.exists_reducedCoefficientBasis determinantNonzero
  have coefficientSmall : normNat coefficient < 4 := by
    apply nat_lt_of_mul_lt_mul_left_direct
    exact coefficientBound.trans_lt (indexFive.trans_lt (by decide))
  rcases RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_of_lt_four
      coefficient coefficientSmall with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientEqZero :=
      RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero coefficientZero
    have scaled :
        upper = scalePair determinantValue
          (linearCombination lower complement 0 1) := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (determinantValue * 0) (determinantValue * 1) := by
          rw [coefficientEqZero]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = scalePair determinantValue
            (linearCombination lower complement 0 1) :=
          linearCombination_scaleCoefficients lower complement
            determinantValue 0 1
    have determinantUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    have determinantNorm : normNat determinantValue = 5 := indexFive
    rw [determinantUnit] at determinantNorm
    exact (by decide : (1 : Nat) ≠ 5) determinantNorm
  · have witness :=
      consecutive.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm
        normalForm coefficientUnit
          (indexFive.symm ▸ (show 4 ≤ 5 by decide))
    have cylinderEmpty :=
      (areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · have determinantNorm : normNat determinantValue = 5 := indexFive
    obtain ⟨unit, shift, unitNorm, coefficientShift⟩ :=
      exists_unit_shift_of_norm_five_and_two determinantNorm
        coefficientDiagonal
    let adjustedComplement :=
      linearCombination lower complement shift 1
    have adjustedNormalForm :
        upper = linearCombination lower adjustedComplement unit
          determinantValue := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (unit + determinantValue * shift) determinantValue := by
          rw [coefficientShift]
        _ = linearCombination lower adjustedComplement unit
            determinantValue := by
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination, adjustedComplement,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
    have witness :=
      consecutive.complement_nonzero_and_in_mixedCylinder_of_unit_normalForm
        adjustedNormalForm unitNorm
          (indexFive.symm ▸ (show 4 ≤ 5 by decide))
    have cylinderEmpty :=
      (areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty adjustedComplement witness.1 witness.2

/-- Consecutive best pairs have determinant quadrance at most two.  The proof
uses only the computed Bezout basis, one nearest Gaussian remainder, the
half-open-square boundary calculation, and the empty mixed cylinder. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_le_two
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    coefficientIndexQuadrance lower upper ≤ 2 := by
  let determinantValue := coefficientDeterminant lower upper
  let indexValue := coefficientIndexQuadrance lower upper
  have indexPositive := consecutive.coefficientIndexQuadrance_pos
  apply Nat.le_of_not_gt
  intro indexGreaterThanTwo
  have indexAtLeastFour : 4 ≤ indexValue := by
    apply Nat.le_of_not_gt
    intro indexBelowFour
    have cases :=
      RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_of_lt_four
        determinantValue indexBelowFour
    change normNat determinantValue = 0 ∨
      normNat determinantValue = 1 ∨ normNat determinantValue = 2 at cases
    change 0 < normNat determinantValue at indexPositive
    change 2 < normNat determinantValue at indexGreaterThanTwo
    rcases cases with zero | one | two
    · rw [zero] at indexPositive
      exact (Nat.not_lt_zero 0 indexPositive).elim
    · rw [one] at indexGreaterThanTwo
      exact ((show ¬2 < 1 by decide) indexGreaterThanTwo).elim
    · rw [two] at indexGreaterThanTwo
      exact (Nat.lt_irrefl 2 indexGreaterThanTwo).elim
  have determinantNonzero := consecutive.coefficientDeterminant_ne_zero
  obtain ⟨coefficient, complement, normalForm, _, boundaryAlternative⟩ :=
    consecutive.1.exists_reducedCoefficientBasis determinantNonzero
  rcases boundaryAlternative indexAtLeastFour with clearance | factorCase
  · have witness :=
      consecutive.complement_nonzero_and_in_mixedCylinder_of_normalForm_clearance
        normalForm clearance
    have cylinderEmpty :=
      (areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
        consecutive |>.2.2.2
    exact cylinderEmpty complement witness.1 witness.2
  · obtain ⟨factor, factorNorm, determinantFactor⟩ := factorCase
    have determinantFactorValue : determinantValue = coefficient * factor :=
      determinantFactor
    have scaled :
        upper = scalePair coefficient
          (linearCombination lower complement 1 factor) := by
      calc
        upper = linearCombination lower complement coefficient
            determinantValue := normalForm
        _ = linearCombination lower complement
            (coefficient * 1) (coefficient * factor) := by
          rw [determinantFactorValue]
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = scalePair coefficient
            (linearCombination lower complement 1 factor) :=
          linearCombination_scaleCoefficients lower complement
            coefficient 1 factor
    have coefficientUnit :=
      consecutive.2.1.scalingCoefficient_norm_eq_one_of_scaled scaled
    have indexEqTwo : indexValue = 2 := by
      calc
        indexValue = normNat determinantValue := rfl
        _ = normNat (coefficient * factor) := by rw [determinantFactorValue]
        _ = normNat coefficient * normNat factor := normNat_mul _ _
        _ = 2 := by rw [coefficientUnit, factorNorm]
    change coefficientIndexQuadrance lower upper = 2 at indexEqTwo
    rw [indexEqTwo] at indexGreaterThanTwo
    exact (Nat.lt_irrefl 2 indexGreaterThanTwo).elim

/-- Exact sharp index dichotomy for consecutive best pairs. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    coefficientIndexQuadrance lower upper = 1 ∨
      coefficientIndexQuadrance lower upper = 2 := by
  have positive := consecutive.coefficientIndexQuadrance_pos
  have upperBound := consecutive.coefficientIndexQuadrance_le_two
  let index := coefficientIndexQuadrance lower upper
  change 0 < index at positive
  change index ≤ 2 at upperBound
  change index = 1 ∨ index = 2
  by_cases indexOne : index = 1
  · exact Or.inl indexOne
  · have twoLe : 2 ≤ index :=
      Nat.lt_of_le_of_ne positive (Ne.symm indexOne)
    exact Or.inr (Nat.le_antisymm upperBound twoLe)

/-- Exact coefficient-lattice classification for consecutive best pairs.  In
the index-one case every ambient pair has integral coordinates in the two
pairs.  In the index-two case every ambient pair has either integral
coordinates or the displayed centered-coset certificate. -/
theorem AreConsecutiveBest.coefficientSpan_or_centeredCoset
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (candidate : Pair) :
    InCoefficientSpan lower upper candidate ∨
      InCenteredCoefficientCoset lower upper candidate := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
    indexOne | indexTwo
  · left
    let determinantValue := coefficientDeterminant lower upper
    refine ⟨conj determinantValue * coefficientDeterminant candidate upper,
      conj determinantValue * coefficientDeterminant lower candidate, ?_⟩
    have expansion :=
      linearCombination_cramer_of_index_one lower upper candidate indexOne
    dsimp only at expansion
    exact expansion.symm
  · exact
      consecutive.1.inCoefficientSpan_or_inCenteredCoefficientCoset_of_index_two
        consecutive.2.1 indexTwo candidate

/-- The reverse half of the centered description: in the index-two case any
two nondivisible cleared coefficients determine an ambient displayed pair. -/
theorem AreConsecutiveBest.exists_centeredCoefficientPair
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient : GaussianInt)
    (leftNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower upper) leftCoefficient)
    (rightNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower upper) rightCoefficient) :
    ∃ candidate : Pair,
      scalePair (coefficientDeterminant lower upper) candidate =
        linearCombination lower upper leftCoefficient rightCoefficient :=
  consecutive.1.exists_centeredCoefficientPair_of_index_two
    consecutive.2.1 indexTwo leftCoefficient rightCoefficient
      leftNotDivisible rightNotDivisible

theorem coefficientDeterminant_linearCombination_right
    (left right : Pair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant
        (linearCombination left right leftCoefficient rightCoefficient) right =
      leftCoefficient * coefficientDeterminant left right := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [coefficientDeterminant, determinant, linearCombination,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem coefficientDeterminant_left_linearCombination
    (left right : Pair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant left
        (linearCombination left right leftCoefficient rightCoefficient) =
      rightCoefficient * coefficientDeterminant left right := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [coefficientDeterminant, determinant, linearCombination,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem coefficientDeterminant_right_linearCombination
    (left right : Pair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant right
        (linearCombination left right leftCoefficient rightCoefficient) =
      -(leftCoefficient * coefficientDeterminant left right) := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [coefficientDeterminant, determinant, linearCombination,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

theorem coefficientDeterminant_scalePair_right
    (left pair : Pair) (scale : GaussianInt) :
    coefficientDeterminant left (scalePair scale pair) =
      scale * coefficientDeterminant left pair := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [coefficientDeterminant, determinant, scalePair,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- Coefficients in a linear combination of two determinant-independent
pairs are unique. -/
theorem linearCombination_coefficients_eq_of_determinant_ne_zero
    (left right : Pair)
    (determinantNonzero : coefficientDeterminant left right ≠ 0)
    {firstLeft firstRight secondLeft secondRight : GaussianInt}
    (identity :
      linearCombination left right firstLeft firstRight =
        linearCombination left right secondLeft secondRight) :
    firstLeft = secondLeft ∧ firstRight = secondRight := by
  constructor
  · have coefficientIdentity :=
      congrArg (fun pair => coefficientDeterminant pair right) identity
    rw [coefficientDeterminant_linearCombination_right,
      coefficientDeterminant_linearCombination_right] at coefficientIdentity
    exact RFAP.GaussianCoset.mul_right_cancel_of_nonzero
      determinantNonzero coefficientIdentity
  · have coefficientIdentity :=
      congrArg (coefficientDeterminant left) identity
    rw [coefficientDeterminant_left_linearCombination,
      coefficientDeterminant_left_linearCombination] at coefficientIdentity
    exact RFAP.GaussianCoset.mul_right_cancel_of_nonzero
      determinantNonzero coefficientIdentity

/-- Algebraic part of the “no repeated index two” transition.  If two
successive determinant pairs both have quadrance two, the third pair cannot
lie in the centered coset of the first two.  It therefore has an ordinary
coefficient expansion, and its coefficient on the first pair is a Gaussian
unit. -/
theorem AreConsecutiveBest.integralTransition_of_two_index_two
    {source : Fraction} {lower middle upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower middle)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient : GaussianInt,
      normNat lowerCoefficient = 1 ∧
        upper = linearCombination lower middle
          lowerCoefficient middleCoefficient := by
  rcases consecutive.coefficientSpan_or_centeredCoset upper with
    integral | centered
  · rcases integral with
      ⟨lowerCoefficient, middleCoefficient, upperIdentity⟩
    refine ⟨lowerCoefficient, middleCoefficient, ?_, upperIdentity⟩
    have determinantIdentity :=
      congrArg (coefficientDeterminant middle) upperIdentity
    rw [coefficientDeterminant_right_linearCombination] at determinantIdentity
    have normIdentity := congrArg normNat determinantIdentity
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
      normNat_mul] at normIdentity
    change coefficientIndexQuadrance middle upper =
      normNat lowerCoefficient *
        coefficientIndexQuadrance lower middle at normIdentity
    rw [leftIndexTwo, rightIndexTwo] at normIdentity
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by decide)
    calc
      normNat lowerCoefficient * 2 = 2 := normIdentity.symm
      _ = 1 * 2 := rfl
  · change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower middle) leftCoefficient ∧
      ¬ RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower middle) rightCoefficient ∧
      scalePair (coefficientDeterminant lower middle) upper =
        linearCombination lower middle leftCoefficient rightCoefficient
      at centered
    rcases centered with
      ⟨leftCoefficient, rightCoefficient, leftNotDivisible, _,
        scaledIdentity⟩
    have determinantIdentity :=
      congrArg (coefficientDeterminant middle) scaledIdentity
    rw [coefficientDeterminant_scalePair_right,
      coefficientDeterminant_right_linearCombination] at determinantIdentity
    have normIdentity := congrArg normNat determinantIdentity
    rw [normNat_mul,
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
      normNat_mul] at normIdentity
    have leftDeterminantNorm :
        normNat (coefficientDeterminant lower middle) = 2 := by
      simpa only [coefficientIndexQuadrance] using leftIndexTwo
    have rightDeterminantNorm :
        normNat (coefficientDeterminant middle upper) = 2 := by
      simpa only [coefficientIndexQuadrance] using rightIndexTwo
    have leftCoefficientNorm : normNat leftCoefficient = 2 := by
      have normIdentity' := normIdentity
      rw [leftDeterminantNorm, rightDeterminantNorm] at normIdentity'
      have numericIdentity : 4 = 2 * normNat leftCoefficient := by
        calc
          4 = 2 * 2 := by decide
          _ = normNat leftCoefficient * 2 := normIdentity'
          _ = 2 * normNat leftCoefficient := Nat.mul_comm _ _
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by decide)
      calc
        normNat leftCoefficient * 2 = 2 * normNat leftCoefficient :=
          Nat.mul_comm _ _
        _ = 4 := numericIdentity.symm
        _ = 2 * 2 := rfl
    exact False.elim
      (leftNotDivisible
        (RFAP.GaussianCoset.divides_of_norm_two
          leftDeterminantNorm leftCoefficientNorm))

/-- For two consecutive index-two transitions, the ordinary transition
coefficient on the middle pair is itself divisible by the first determinant.
Equivalently, the algebraic transition has Chevallier's displayed shape
`unit * lower + determinant * step * middle`.  This is the finite coefficient
part of the repeated-index analysis; it does not invoke the later geometric
argument excluding the transition altogether. -/
theorem AreConsecutiveBest.integralTransition_with_divisible_middleCoefficient
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient : GaussianInt,
      normNat lowerCoefficient = 1 ∧
      RFAP.GaussianCoset.Divides
        (coefficientDeterminant lower middle) middleCoefficient ∧
      upper = linearCombination lower middle
        lowerCoefficient middleCoefficient := by
  obtain ⟨lowerCoefficient, middleCoefficient, lowerCoefficientNorm,
      upperIdentity⟩ :=
    first.integralTransition_of_two_index_two leftIndexTwo rightIndexTwo
  let leftDeterminant := coefficientDeterminant lower middle
  let rightDeterminant := coefficientDeterminant middle upper
  have leftDeterminantNorm : normNat leftDeterminant = 2 := by
    simpa only [leftDeterminant, coefficientIndexQuadrance] using leftIndexTwo
  have rightDeterminantNorm : normNat rightDeterminant = 2 := by
    simpa only [rightDeterminant, coefficientIndexQuadrance] using rightIndexTwo
  have oneNonzero : (1 : GaussianInt) ≠ 0 := by decide
  have oneNorm : normNat (1 : GaussianInt) = 1 := rfl
  have oneNotDivisible :
      ¬ RFAP.GaussianCoset.Divides rightDeterminant 1 :=
    RFAP.GaussianCoset.not_divides_of_norm_lt oneNonzero
      (by rw [oneNorm, rightDeterminantNorm]; decide)
  obtain ⟨halfSum, halfSumIdentity⟩ :=
    second.exists_centeredCoefficientPair rightIndexTwo 1 1
      oneNotDivisible oneNotDivisible
  have determinantTransition :=
    congrArg (coefficientDeterminant middle) upperIdentity
  rw [coefficientDeterminant_right_linearCombination] at determinantTransition
  have determinantTransition' :
      rightDeterminant = -(lowerCoefficient * leftDeterminant) := by
    simpa only [leftDeterminant, rightDeterminant] using determinantTransition
  rcases first.coefficientSpan_or_centeredCoset halfSum with
    integralHalfSum | centeredHalfSum
  · rcases integralHalfSum with
      ⟨lowerHalfCoefficient, middleHalfCoefficient, halfSumExpansion⟩
    have halfSumDeterminant :=
      congrArg (coefficientDeterminant middle) halfSumIdentity
    rw [coefficientDeterminant_scalePair_right,
      coefficientDeterminant_left_linearCombination] at halfSumDeterminant
    have halfSpanDeterminant :=
      congrArg (coefficientDeterminant middle) halfSumExpansion
    rw [coefficientDeterminant_right_linearCombination] at halfSpanDeterminant
    rw [halfSpanDeterminant] at halfSumDeterminant
    have normIdentity := congrArg normNat halfSumDeterminant
    rw [normNat_mul,
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
      normNat_mul, RFAP.ConstructiveGaussianHeight.GaussianInt.one_mul]
        at normIdentity
    have normIdentity' := normIdentity
    rw [leftDeterminantNorm, rightDeterminantNorm] at normIdentity'
    have impossible : False := by
      have coefficientNormNonnegative :
          0 ≤ normNat lowerHalfCoefficient := Nat.zero_le _
      omega
    exact False.elim impossible
  · change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ RFAP.GaussianCoset.Divides leftDeterminant leftCoefficient ∧
      ¬ RFAP.GaussianCoset.Divides leftDeterminant rightCoefficient ∧
      scalePair leftDeterminant halfSum =
        linearCombination lower middle leftCoefficient rightCoefficient
      at centeredHalfSum
    rcases centeredHalfSum with
      ⟨centeredLeft, centeredRight, _, centeredRightNotDivisible,
        centeredIdentity⟩
    have negatedScale :
        -lowerCoefficient * leftDeterminant = rightDeterminant := by
      calc
        -lowerCoefficient * leftDeterminant =
            -(lowerCoefficient * leftDeterminant) := by
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
        _ = rightDeterminant := determinantTransition'.symm
    have centeredScaled :
        scalePair rightDeterminant halfSum =
          linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) := by
      calc
        scalePair rightDeterminant halfSum =
            scalePair (-lowerCoefficient * leftDeterminant) halfSum := by
          rw [negatedScale]
        _ = scalePair (-lowerCoefficient)
            (scalePair leftDeterminant halfSum) :=
          (scalePair_scalePair (-lowerCoefficient) leftDeterminant halfSum).symm
        _ = scalePair (-lowerCoefficient)
            (linearCombination lower middle centeredLeft centeredRight) :=
          congrArg (scalePair (-lowerCoefficient)) centeredIdentity
        _ = linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) :=
          (linearCombination_scaleCoefficients lower middle
            (-lowerCoefficient) centeredLeft centeredRight).symm
    have halfSumFromTransition :
        scalePair rightDeterminant halfSum =
          linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) := by
      calc
        scalePair rightDeterminant halfSum =
            linearCombination middle upper 1 1 := halfSumIdentity
        _ = linearCombination middle
            (linearCombination lower middle lowerCoefficient
              middleCoefficient) 1 1 := by rw [← upperIdentity]
        _ = linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) := by
          apply pair_ext <;>
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [linearCombination,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
            ring1
    have combinationsEqual :
        linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) =
          linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) :=
      centeredScaled.symm.trans halfSumFromTransition
    have leftDeterminantNonzero : leftDeterminant ≠ 0 := by
      intro determinantZero
      rw [determinantZero] at leftDeterminantNorm
      contradiction
    have coefficientIdentities :=
      linearCombination_coefficients_eq_of_determinant_ne_zero
        lower middle leftDeterminantNonzero combinationsEqual
    have negatedCoefficientNorm :
        normNat (-lowerCoefficient) = 1 := by
      rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
        lowerCoefficientNorm]
    have negatedCoefficientNonzero : -lowerCoefficient ≠ 0 := by
      intro coefficientZero
      have zeroNorm := congrArg normNat coefficientZero
      rw [negatedCoefficientNorm] at zeroNorm
      contradiction
    have negatedCoefficientNotDivisible :
        ¬ RFAP.GaussianCoset.Divides leftDeterminant
          (-lowerCoefficient) :=
      RFAP.GaussianCoset.not_divides_of_norm_lt
        negatedCoefficientNonzero
        (by rw [negatedCoefficientNorm, leftDeterminantNorm]; decide)
    have sumNotDivisible :
        ¬ RFAP.GaussianCoset.Divides leftDeterminant
          (1 + middleCoefficient) := by
      rw [← coefficientIdentities.2]
      exact RFAP.GaussianCoset.not_divides_mul_of_norm_two
        leftDeterminantNorm negatedCoefficientNotDivisible
          centeredRightNotDivisible
    have negativeOneNonzero : (-1 : GaussianInt) ≠ 0 := by decide
    have negativeOneNorm : normNat (-1 : GaussianInt) = 1 := by decide
    have negativeOneNotDivisible :
        ¬ RFAP.GaussianCoset.Divides leftDeterminant (-1) :=
      RFAP.GaussianCoset.not_divides_of_norm_lt negativeOneNonzero
        (by rw [negativeOneNorm, leftDeterminantNorm]; decide)
    have middleCoefficientDivisibleSum :=
      RFAP.GaussianCoset.divides_add_of_not_divides_of_norm_two
        leftDeterminantNorm sumNotDivisible negativeOneNotDivisible
    rcases middleCoefficientDivisibleSum with
      ⟨middleQuotient, middleSumIdentity⟩
    have middleCoefficientDivisible :
        RFAP.GaussianCoset.Divides leftDeterminant middleCoefficient := by
      refine ⟨middleQuotient, ?_⟩
      calc
        middleCoefficient = (1 + middleCoefficient) + (-1) := by
          apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
            simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im] <;>
            ring1
        _ = leftDeterminant * middleQuotient := middleSumIdentity
    exact ⟨lowerCoefficient, middleCoefficient, lowerCoefficientNorm,
      middleCoefficientDivisible, upperIdentity⟩

/-- Fully witnessed repeated-index normal form.  Two hypothetical successive
index-two transitions produce a Gaussian unit on the first pair and a
nonzero displayed Gaussian step multiplying the first determinant on the
middle pair.  The nonzeroness follows from the strict increase through the
two denominator levels. -/
theorem AreConsecutiveBest.repeatedIndexTwo_normalForm
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      normNat lowerUnit = 1 ∧ step ≠ 0 ∧
      upper = linearCombination lower middle lowerUnit
        (coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, middleCoefficient, lowerUnitNorm,
      middleCoefficientDivisible, upperIdentity⟩ :=
    first.integralTransition_with_divisible_middleCoefficient second
      leftIndexTwo rightIndexTwo
  rcases middleCoefficientDivisible with ⟨step, middleCoefficientIdentity⟩
  have witnessedIdentity :
      upper = linearCombination lower middle lowerUnit
        (coefficientDeterminant lower middle * step) := by
    rw [← middleCoefficientIdentity]
    exact upperIdentity
  have stepNonzero : step ≠ 0 := by
    intro stepZero
    have upperDenominatorIdentity :
        upper.denominator = lowerUnit * lower.denominator := by
      rw [witnessedIdentity, stepZero]
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [linearCombination,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
        ring1
    have denominatorQuadranceIdentity :=
      congrArg normNat upperDenominatorIdentity
    rw [normNat_mul, lowerUnitNorm, Nat.one_mul]
      at denominatorQuadranceIdentity
    have lowerBelowUpper :
        denominatorQuadrance lower < denominatorQuadrance upper :=
      first.2.2.1.trans second.2.2.1
    change denominatorQuadrance upper = denominatorQuadrance lower
      at denominatorQuadranceIdentity
    omega
  exact ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, witnessedIdentity⟩

/-- A nontrivial coefficient combination of consecutive best pairs is a
nonzero source-lattice vector. -/
theorem AreConsecutiveBest.linearCombination_pairNonzero
    {source : Gaussian} {left right : Pair}
    (consecutive : AreConsecutiveBest source left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    PairNonzero
      (linearCombination left right leftCoefficient rightCoefficient) := by
  apply (pairNonzero_iff_ne_zeroPair _).mpr
  intro combinationZero
  rcases coefficientNonzero with leftNonzero | rightNonzero
  · have determinantZero :
        coefficientDeterminant
            (linearCombination left right leftCoefficient rightCoefficient)
              right = 0 := by
      rw [combinationZero]
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [coefficientDeterminant, determinant, zeroPair,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im] <;>
        ring1
    have productZero :
        leftCoefficient * coefficientDeterminant left right = 0 := by
      rw [← coefficientDeterminant_linearCombination_right]
      exact determinantZero
    have normProductZero := congrArg normNat productZero
    rw [normNat_mul] at normProductZero
    have leftPositive := normNat_pos leftNonzero
    have determinantPositive := consecutive.coefficientIndexQuadrance_pos
    change normNat leftCoefficient * coefficientIndexQuadrance left right = 0
      at normProductZero
    exact (Nat.ne_of_gt
      (Nat.mul_pos leftPositive determinantPositive)) normProductZero
  · have determinantZero :
        coefficientDeterminant left
            (linearCombination left right leftCoefficient rightCoefficient) =
          0 := by
      rw [combinationZero]
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [coefficientDeterminant, determinant, zeroPair,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im] <;>
        ring1
    have productZero :
        rightCoefficient * coefficientDeterminant left right = 0 := by
      rw [← coefficientDeterminant_left_linearCombination]
      exact determinantZero
    have normProductZero := congrArg normNat productZero
    rw [normNat_mul] at normProductZero
    have rightPositive := normNat_pos rightNonzero
    have determinantPositive := consecutive.coefficientIndexQuadrance_pos
    change normNat rightCoefficient * coefficientIndexQuadrance left right = 0
      at normProductZero
    exact (Nat.ne_of_gt
      (Nat.mul_pos rightPositive determinantPositive)) normProductZero

/-- Every Gaussian unit determines a displayed member of the centered coset
of an index-two consecutive pair.  Its empty mixed cylinder forces this
explicitly constructed half-difference to lie outside that cylinder. -/
theorem AreConsecutiveBest.exists_centeredUnitCandidate_outsideCylinder
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    ∃ candidate : Pair,
      PairNonzero candidate ∧
      scalePair (coefficientDeterminant lower upper) candidate =
        linearCombination lower upper (-unit) 1 ∧
      ¬ InOpenMixedCylinder source.value lower upper candidate := by
  let determinantValue := coefficientDeterminant lower upper
  have determinantNorm : normNat determinantValue = 2 := by
    simpa only [determinantValue, coefficientIndexQuadrance] using indexTwo
  have unitNonzero : unit ≠ 0 := by
    intro unitZero
    have zeroNorm := congrArg normNat unitZero
    rw [unitNorm] at zeroNorm
    contradiction
  have negatedUnitNonzero : -unit ≠ 0 := by
    intro negatedZero
    have zeroNorm := congrArg normNat negatedZero
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
      unitNorm] at zeroNorm
    contradiction
  have negatedUnitNotDivisible :
      ¬ RFAP.GaussianCoset.Divides determinantValue (-unit) :=
    RFAP.GaussianCoset.not_divides_of_norm_lt negatedUnitNonzero
      (by
        rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_neg,
          unitNorm, determinantNorm]
        decide)
  have oneNonzero : (1 : GaussianInt) ≠ 0 := by decide
  have oneNotDivisible :
      ¬ RFAP.GaussianCoset.Divides determinantValue 1 :=
    RFAP.GaussianCoset.not_divides_of_norm_lt oneNonzero
      (by rw [determinantNorm]; decide)
  obtain ⟨candidate, centeredIdentity⟩ :=
    consecutive.exists_centeredCoefficientPair indexTwo (-unit) 1
      negatedUnitNotDivisible oneNotDivisible
  have combinationNonzero :
      PairNonzero (linearCombination lower upper (-unit) 1) :=
    consecutive.linearCombination_pairNonzero (-unit) 1
      (Or.inl negatedUnitNonzero)
  have candidateNonzero : PairNonzero candidate := by
    apply (pairNonzero_iff_ne_zeroPair candidate).mpr
    intro candidateZero
    have combinationZero :
        linearCombination lower upper (-unit) 1 = zeroPair := by
      rw [← centeredIdentity, candidateZero]
      apply pair_ext <;>
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [scalePair, zeroPair,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.zero_im] <;>
        ring1
    exact (pairNonzero_iff_ne_zeroPair _).mp combinationNonzero combinationZero
  have cylinderEmpty :=
    (areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
      consecutive |>.2.2.2
  exact ⟨candidate, candidateNonzero, centeredIdentity,
    cylinderEmpty candidate candidateNonzero⟩

/-- The same centered half-difference also lies outside the next mixed
cylinder whenever another consecutive level follows.  These four finite
candidates are the starting point of the geometric obstruction to two
successive index-two transitions. -/
theorem AreConsecutiveBest.exists_centeredUnitCandidate_outside_nextCylinder
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    ∃ candidate : Pair,
      PairNonzero candidate ∧
      scalePair (coefficientDeterminant lower middle) candidate =
        linearCombination lower middle (-unit) 1 ∧
      ¬ InOpenMixedCylinder source.value middle upper candidate := by
  obtain ⟨candidate, candidateNonzero, centeredIdentity, _⟩ :=
    first.exists_centeredUnitCandidate_outsideCylinder leftIndexTwo
      unit unitNorm
  have nextCylinderEmpty :=
    (areConsecutiveBest_iff_mixedCylinderEmpty source middle upper).mp second
      |>.2.2.2
  exact ⟨candidate, candidateNonzero, centeredIdentity,
    nextCylinderEmpty candidate candidateNonzero⟩

/-- The centered candidate tested against its own index-two cylinder gives
the exact finite constraint on the two normalized coordinates used in the
index-two geometry: at least one of its two scaled coordinate quadrances must
reach the corresponding boundary. -/
theorem AreConsecutiveBest.centeredUnit_selfObstruction
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    (2 : Coordinate) * errorQuadrance source.value lower ≤
        errorQuadrance source.value
          (linearCombination lower upper (-unit) 1) ∨
      2 * denominatorQuadrance upper ≤
        denominatorQuadrance
          (linearCombination lower upper (-unit) 1) := by
  obtain ⟨candidate, _, centeredIdentity, outside⟩ :=
    consecutive.exists_centeredUnitCandidate_outsideCylinder indexTwo
      unit unitNorm
  have determinantNorm :
      normNat (coefficientDeterminant lower upper) = 2 := by
    simpa only [coefficientIndexQuadrance] using indexTwo
  have errorIdentity :=
    congrArg (errorQuadrance source.value) centeredIdentity
  rw [errorQuadrance_scalePair, determinantNorm] at errorIdentity
  have denominatorIdentity :=
    congrArg denominatorQuadrance centeredIdentity
  rw [denominatorQuadrance_scalePair, determinantNorm] at denominatorIdentity
  by_cases errorInside :
      errorQuadrance source.value candidate <
        errorQuadrance source.value lower
  · have denominatorNotInside :
        ¬ denominatorQuadrance candidate < denominatorQuadrance upper := by
      intro denominatorInside
      exact outside ⟨errorInside, denominatorInside⟩
    right
    calc
      2 * denominatorQuadrance upper ≤
          2 * denominatorQuadrance candidate :=
        Nat.mul_le_mul_left 2 (Nat.le_of_not_gt denominatorNotInside)
      _ = denominatorQuadrance
          (linearCombination lower upper (-unit) 1) := denominatorIdentity
  · have errorOutside :
        errorQuadrance source.value lower ≤
          errorQuadrance source.value candidate :=
      le_of_not_gt errorInside
    left
    calc
      (2 : Coordinate) * errorQuadrance source.value lower ≤
          (2 : Coordinate) * errorQuadrance source.value candidate :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          errorOutside (by decide)
      _ = errorQuadrance source.value
          (linearCombination lower upper (-unit) 1) := errorIdentity

/-- Coordinate identity for the centered unit combination's error. -/
theorem error_linearCombination_negUnit_one
    (source : Gaussian) (lower upper : Pair) (unit : GaussianInt) :
    error source (linearCombination lower upper (-unit) 1) =
      error source upper - toGaussian unit * error source lower := by
  rw [error_linearCombination]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [toGaussian_neg, toGaussian_one,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

/-- Coordinate identity for the centered unit combination's denominator. -/
theorem toGaussian_denominator_linearCombination_negUnit_one
    (lower upper : Pair) (unit : GaussianInt) :
    toGaussian (linearCombination lower upper (-unit) 1).denominator =
      toGaussian upper.denominator -
        toGaussian unit * toGaussian lower.denominator := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [linearCombination, toGaussian_add, toGaussian_mul,
      toGaussian_neg, toGaussian_one,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
    ring1

/-- The self-cylinder obstruction in its geometric coordinate form.  This is
the form consumed by the finite repeated-index case table. -/
theorem AreConsecutiveBest.centeredUnit_selfCoordinateObstruction
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    (2 : Coordinate) * normSq (error source.value lower) ≤
        normSq (error source.value upper -
          toGaussian unit * error source.value lower) ∨
      (2 : Coordinate) * normSq (toGaussian upper.denominator) ≤
        normSq (toGaussian upper.denominator -
          toGaussian unit * toGaussian lower.denominator) := by
  rcases consecutive.centeredUnit_selfObstruction indexTwo unit unitNorm with
    errorExterior | denominatorExterior
  · left
    rw [← error_linearCombination_negUnit_one]
    exact errorExterior
  · right
    have castExterior :=
      RFAP.ConstructiveFraction.natCast_le_direct denominatorExterior
    calc
      (2 : Coordinate) * normSq (toGaussian upper.denominator) =
          ((2 * denominatorQuadrance upper : Nat) : Coordinate) := by
        rw [normSq_toGaussian]
        change (2 : Coordinate) *
            (denominatorQuadrance upper : Coordinate) =
          ((2 * denominatorQuadrance upper : Nat) : Coordinate)
        rw [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤
          (denominatorQuadrance
            (linearCombination lower upper (-unit) 1) : Coordinate) :=
        castExterior
      _ = normSq
          (toGaussian
            (linearCombination lower upper (-unit) 1).denominator) :=
        (normSq_toGaussian _).symm
      _ = normSq (toGaussian upper.denominator -
          toGaussian unit * toGaussian lower.denominator) := by
        rw [toGaussian_denominator_linearCombination_negUnit_one]

/-- Two opposite unit translates cannot both reach twice the larger
quadrance when the moving vector is strictly shorter.  This is the
parallelogram calculation used in the finite four-unit argument. -/
theorem not_both_opposite_exterior
    {large small firstDifference secondDifference : Coordinate}
    (ordered : small < large)
    (firstExterior : 2 * large ≤ firstDifference)
    (secondExterior : 2 * large ≤ secondDifference)
    (parallelogram :
      firstDifference + secondDifference = 2 * (large + small)) : False := by
  have summed : 2 * large + 2 * large ≤
      firstDifference + secondDifference :=
    add_le_add firstExterior secondExterior
  rw [parallelogram] at summed
  have twiceOrderedReverse : 2 * large ≤ 2 * small := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct summed (2 * large)
    convert shifted using 1 <;> ring1
  have orderedReverse : large ≤ small := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := 2)
    · simpa only [RFAP.ConstructiveFraction.mul_comm] using
        twiceOrderedReverse
    · decide
  exact (not_lt_of_ge orderedReverse) ordered

/-- Two adjacent unit translates cannot both reach twice the larger
quadrance once the larger quadrance is at least four times the smaller one.
The two associated projections are orthogonal, so their squared sum is the
product of the two quadrances. -/
theorem not_both_adjacent_exterior_of_four_mul_small_le
    {large small firstProjection secondProjection : Coordinate}
    (largeNonnegative : 0 ≤ large) (smallNonnegative : 0 ≤ small)
    (ordered : small < large) (fourSmallLe : 4 * small ≤ large)
    (projectionSquares :
      firstProjection ^ 2 + secondProjection ^ 2 = large * small)
    (firstExterior :
      2 * large ≤ large + small - 2 * firstProjection)
    (secondExterior :
      2 * large ≤ large + small - 2 * secondProjection) : False := by
  let gap := large - small
  have gapPositive : 0 < gap := by
    dsimp only [gap]
    exact RFAP.ConstructiveFraction.sub_pos_direct ordered
  have firstProjectionBound : gap ≤ -2 * firstProjection := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct firstExterior (large + small)
    change 2 * large - (large + small) ≤
      (large + small - 2 * firstProjection) - (large + small) at shifted
    convert shifted using 1
    · dsimp only [gap]
      ring1
    · ring1
  have secondProjectionBound : gap ≤ -2 * secondProjection := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct secondExterior (large + small)
    change 2 * large - (large + small) ≤
      (large + small - 2 * secondProjection) - (large + small) at shifted
    convert shifted using 1
    · dsimp only [gap]
      ring1
    · ring1
  have firstSquare : gap ^ 2 ≤ (-2 * firstProjection) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.le_of_lt_direct gapPositive)
      firstProjectionBound 2
  have secondSquare : gap ^ 2 ≤ (-2 * secondProjection) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.le_of_lt_direct gapPositive)
      secondProjectionBound 2
  have twiceGapBound : 2 * gap ^ 2 ≤ 4 * (large * small) := by
    calc
      2 * gap ^ 2 = gap ^ 2 + gap ^ 2 := by ring1
      _ ≤ (-2 * firstProjection) ^ 2 +
          (-2 * secondProjection) ^ 2 :=
        add_le_add firstSquare secondSquare
      _ = 4 * (firstProjection ^ 2 + secondProjection ^ 2) := by ring1
      _ = 4 * (large * small) := by rw [projectionSquares]
  have gapSquareLe : gap ^ 2 ≤ 2 * large * small := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := 2)
    · calc
        gap ^ 2 * 2 = 2 * gap ^ 2 := by ring1
        _ ≤ 4 * (large * small) := twiceGapBound
        _ = (2 * large * small) * 2 := by ring1
    · decide
  have largeMinusFourSmallNonnegative : 0 ≤ large - 4 * small :=
    RFAP.ConstructiveFraction.sub_nonneg_direct fourSmallLe
  have leadingNonnegative : 0 ≤ large * (large - 4 * small) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct largeNonnegative
      largeMinusFourSmallNonnegative
  have strictPolynomial : 0 < large * (large - 4 * small) + small ^ 2 := by
    by_cases smallZero : small = 0
    · rw [smallZero] at ordered ⊢
      have largePositive : 0 < large := ordered
      calc
        0 < large * large :=
          RFAP.ConstructiveFraction.mul_pos_direct largePositive largePositive
        _ = large * (large - 4 * 0) + 0 ^ 2 := by ring1
    · have smallPositive : 0 < small :=
        lt_of_le_of_ne smallNonnegative (Ne.symm smallZero)
      have smallSquarePositive : 0 < small ^ 2 := by
        simpa only [pow_two] using
          RFAP.ConstructiveFraction.mul_pos_direct smallPositive smallPositive
      exact lt_of_lt_of_le smallSquarePositive
        (le_add_of_nonneg_left leadingNonnegative)
  have strictGap : 2 * large * small < gap ^ 2 := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      0 < large * (large - 4 * small) + small ^ 2 := strictPolynomial
      _ = gap ^ 2 - 2 * large * small := by
        dsimp only [gap]
        ring1
  exact (not_lt_of_ge gapSquareLe strictGap).elim

/-- Four centered-unit cylinder obstructions force a quantitative separation
between the two error levels.  The proof is a finite sixteen-case argument:
two error exteriors are impossible by the preceding opposite/adjacent
calculations, while any three denominator exteriors contain an opposite
pair and are impossible by the parallelogram identity. -/
theorem four_unit_obstructions_force_error_lt_four_mul
    (largeError smallError lowerDenominator upperDenominator : Gaussian)
    (errorOrdered : normSq smallError < normSq largeError)
    (denominatorOrdered :
      normSq lowerDenominator < normSq upperDenominator)
    (positiveOneObstruction :
      2 * normSq largeError ≤
          normSq (smallError - toGaussian (1 : GaussianInt) * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (1 : GaussianInt) * lowerDenominator))
    (negativeOneObstruction :
      2 * normSq largeError ≤
          normSq (smallError - toGaussian (-1 : GaussianInt) * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (-1 : GaussianInt) * lowerDenominator))
    (positiveImaginaryObstruction :
      2 * normSq largeError ≤
          normSq (smallError -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * lowerDenominator))
    (negativeImaginaryObstruction :
      2 * normSq largeError ≤
          normSq (smallError -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * largeError) ∨
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) *
              lowerDenominator)) :
    normSq largeError < 4 * normSq smallError := by
  apply lt_of_not_ge
  intro fourSmallLe
  let large := normSq largeError
  let small := normSq smallError
  let firstProjection : Coordinate :=
    smallError.re * largeError.re + smallError.im * largeError.im
  let secondProjection : Coordinate :=
    -smallError.re * largeError.im + smallError.im * largeError.re
  have largeNonnegative : 0 ≤ large := normSq_nonneg largeError
  have smallNonnegative : 0 ≤ small := normSq_nonneg smallError
  have projectionSquares :
      firstProjection ^ 2 + secondProjection ^ 2 = large * small := by
    dsimp only [firstProjection, secondProjection, large, small, normSq]
    ring1
  have positiveOneExpansion :
      normSq (smallError - toGaussian (1 : GaussianInt) * largeError) =
        large + small - 2 * firstProjection := by
    dsimp only [large, small, firstProjection, normSq, toGaussian]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
      Int.cast_one, Int.cast_zero]
    ring1
  have negativeOneExpansion :
      normSq (smallError - toGaussian (-1 : GaussianInt) * largeError) =
        large + small - 2 * (-firstProjection) := by
    dsimp only [large, small, firstProjection, normSq, toGaussian]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
      Int.cast_neg, Int.cast_one, Int.cast_zero]
    ring1
  have positiveImaginaryExpansion :
      normSq (smallError -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError) =
        large + small - 2 * secondProjection := by
    dsimp only [large, small, secondProjection, normSq, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      Int.cast_zero, Int.cast_one]
    ring1
  have negativeImaginaryExpansion :
      normSq (smallError -
          toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * largeError) =
        large + small - 2 * (-secondProjection) := by
    dsimp only [large, small, secondProjection, normSq, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      Int.cast_neg, Int.cast_zero, Int.cast_one]
    ring1
  have errorOneNegativeOneImpossible
      (positiveExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (1 : GaussianInt) * largeError))
      (negativeExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (-1 : GaussianInt) * largeError)) :
      False := by
    apply not_both_opposite_exterior errorOrdered positiveExterior
      negativeExterior
    rw [positiveOneExpansion, negativeOneExpansion]
    dsimp only [large, small]
    ring1
  have errorImaginaryOppositesImpossible
      (positiveExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError))
      (negativeExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * largeError)) :
      False := by
    apply not_both_opposite_exterior errorOrdered positiveExterior
      negativeExterior
    rw [positiveImaginaryExpansion, negativeImaginaryExpansion]
    dsimp only [large, small]
    ring1
  have errorOneImaginaryImpossible
      (oneExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (1 : GaussianInt) * largeError))
      (imaginaryExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError)) :
      False := by
    rw [positiveOneExpansion] at oneExterior
    rw [positiveImaginaryExpansion] at imaginaryExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      projectionSquares oneExterior imaginaryExterior
  have errorImaginaryNegativeOneImpossible
      (imaginaryExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError))
      (negativeOneExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (-1 : GaussianInt) * largeError)) :
      False := by
    rw [positiveImaginaryExpansion] at imaginaryExterior
    rw [negativeOneExpansion] at negativeOneExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          secondProjection ^ 2 + (-firstProjection) ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      imaginaryExterior negativeOneExterior
  have errorNegativeOneNegativeImaginaryImpossible
      (negativeOneExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (-1 : GaussianInt) * largeError))
      (negativeImaginaryExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * largeError)) :
      False := by
    rw [negativeOneExpansion] at negativeOneExterior
    rw [negativeImaginaryExpansion] at negativeImaginaryExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          (-firstProjection) ^ 2 + (-secondProjection) ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      negativeOneExterior negativeImaginaryExterior
  have errorNegativeImaginaryOneImpossible
      (negativeImaginaryExterior :
        2 * normSq largeError ≤
          normSq (smallError -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * largeError))
      (oneExterior :
        2 * normSq largeError ≤
          normSq (smallError - toGaussian (1 : GaussianInt) * largeError)) :
      False := by
    rw [negativeImaginaryExpansion] at negativeImaginaryExterior
    rw [positiveOneExpansion] at oneExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          (-secondProjection) ^ 2 + firstProjection ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      negativeImaginaryExterior oneExterior
  have denominatorOneNegativeOneImpossible
      (positiveExterior :
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (1 : GaussianInt) * lowerDenominator))
      (negativeExterior :
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (-1 : GaussianInt) * lowerDenominator)) : False := by
    apply not_both_opposite_exterior denominatorOrdered positiveExterior
      negativeExterior
    dsimp only [normSq, toGaussian]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
      Int.cast_neg, Int.cast_one, Int.cast_zero]
    ring1
  have denominatorImaginaryOppositesImpossible
      (positiveExterior :
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian RFAP.HurwitzGeometry.imaginaryUnit * lowerDenominator))
      (negativeExterior :
        2 * normSq upperDenominator ≤
          normSq (upperDenominator -
            toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) *
              lowerDenominator)) : False := by
    apply not_both_opposite_exterior denominatorOrdered positiveExterior
      negativeExterior
    dsimp only [normSq, toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      Int.cast_neg, Int.cast_one, Int.cast_zero]
    ring1
  rcases positiveOneObstruction with errorOne | denominatorOne <;>
    rcases negativeOneObstruction with errorNegativeOne |
      denominatorNegativeOne <;>
    rcases positiveImaginaryObstruction with errorImaginary |
      denominatorImaginary <;>
    rcases negativeImaginaryObstruction with errorNegativeImaginary |
      denominatorNegativeImaginary
  all_goals first
    | exact errorOneNegativeOneImpossible errorOne errorNegativeOne
    | exact errorImaginaryOppositesImpossible errorImaginary
        errorNegativeImaginary
    | exact errorOneImaginaryImpossible errorOne errorImaginary
    | exact errorImaginaryNegativeOneImpossible errorImaginary errorNegativeOne
    | exact errorNegativeOneNegativeImaginaryImpossible errorNegativeOne
        errorNegativeImaginary
    | exact errorNegativeImaginaryOneImpossible errorNegativeImaginary errorOne
    | exact denominatorOneNegativeOneImpossible denominatorOne
        denominatorNegativeOne
    | exact denominatorImaginaryOppositesImpossible denominatorImaginary
        denominatorNegativeImaginary

/-- Square-root-free reverse-triangle estimate at the numerical threshold
needed below.  If one summand has quadrance at least ten times the comparison
quadrance while the other has quadrance below four times it, their sum cannot
have smaller quadrance than the comparison value.  `dotBound` is the
two-coordinate Cauchy certificate. -/
theorem large_summand_sum_not_lt_comparison
    {multipliedNorm baseNorm comparisonNorm dotValue sumNorm : Coordinate}
    (comparisonPositive : 0 < comparisonNorm)
    (baseNonnegative : 0 ≤ baseNorm)
    (tenComparisonLe : 10 * comparisonNorm ≤ multipliedNorm)
    (baseLtFourComparison : baseNorm < 4 * comparisonNorm)
    (dotBound : dotValue ^ 2 ≤ multipliedNorm * baseNorm)
    (sumExpansion :
      sumNorm = multipliedNorm + baseNorm + 2 * dotValue) :
    ¬ sumNorm < comparisonNorm := by
  intro sumSmaller
  let gap := multipliedNorm + baseNorm - comparisonNorm
  have nineComparisonPositive : 0 < 9 * comparisonNorm :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) comparisonPositive
  have nineComparisonLeGap : 9 * comparisonNorm ≤ gap := by
    have added := add_le_add tenComparisonLe baseNonnegative
    calc
      9 * comparisonNorm =
          (10 * comparisonNorm + 0) - comparisonNorm := by ring1
      _ ≤ (multipliedNorm + baseNorm) - comparisonNorm :=
        RFAP.ConstructiveFraction.sub_le_sub_right_direct added comparisonNorm
      _ = gap := by rfl
  have gapPositive : 0 < gap :=
    lt_of_lt_of_le nineComparisonPositive nineComparisonLeGap
  have gapLtNegTwiceDot : gap < -2 * dotValue := by
    rw [sumExpansion] at sumSmaller
    have shifted := RFAP.ConstructiveFraction.sub_lt_sub_right_direct
      sumSmaller (2 * dotValue)
    have shiftedAgain := RFAP.ConstructiveFraction.sub_lt_sub_right_direct
      shifted comparisonNorm
    calc
      gap =
          (multipliedNorm + baseNorm + 2 * dotValue - 2 * dotValue) -
            comparisonNorm := by
        dsimp only [gap]
        ring1
      _ < (comparisonNorm - 2 * dotValue) - comparisonNorm :=
        shiftedAgain
      _ = -2 * dotValue := by ring1
  have negTwiceDotPositive : 0 < -2 * dotValue :=
    gapPositive.trans gapLtNegTwiceDot
  have gapSquareLt : gap ^ 2 < (-2 * dotValue) ^ 2 := by
    have first : gap * gap < gap * (-2 * dotValue) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct gapPositive
        gapLtNegTwiceDot
    have second : gap * (-2 * dotValue) <
        (-2 * dotValue) * (-2 * dotValue) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        gapLtNegTwiceDot negTwiceDotPositive
    simpa only [pow_two] using first.trans second
  have gapSquareLtFourProduct :
      gap ^ 2 < 4 * (multipliedNorm * baseNorm) := by
    calc
      gap ^ 2 < (-2 * dotValue) ^ 2 := gapSquareLt
      _ = 4 * dotValue ^ 2 := by ring1
      _ ≤ 4 * (multipliedNorm * baseNorm) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotBound (by decide)
  have comparisonNonnegative : 0 ≤ comparisonNorm :=
    RFAP.ConstructiveFraction.le_of_lt_direct comparisonPositive
  have multipliedNonnegative : 0 ≤ multipliedNorm :=
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (show (0 : Coordinate) ≤ 10 by decide) comparisonNonnegative).trans
      tenComparisonLe
  have firstLeftNonnegative :
      0 ≤ multipliedNorm - 10 * comparisonNorm :=
    RFAP.ConstructiveFraction.sub_nonneg_direct tenComparisonLe
  have twiceBaseLtEightComparison :
      2 * baseNorm < 8 * comparisonNorm := by
    calc
      2 * baseNorm < 2 * (4 * comparisonNorm) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide) baseLtFourComparison
      _ = 8 * comparisonNorm := by ring1
  have firstRightPositive :
      0 < multipliedNorm + 8 * comparisonNorm - 2 * baseNorm := by
    have baselineStrict :
        10 * comparisonNorm <
          10 * comparisonNorm + 8 * comparisonNorm - 2 * baseNorm := by
      have subtracted := RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        twiceBaseLtEightComparison
        (10 * comparisonNorm + 8 * comparisonNorm)
      convert subtracted using 1
      · ring1
    have baselineLe :
        10 * comparisonNorm + 8 * comparisonNorm - 2 * baseNorm ≤
          multipliedNorm + 8 * comparisonNorm - 2 * baseNorm := by
      have sumLe := add_le_add_left tenComparisonLe (8 * comparisonNorm)
      have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct sumLe (2 * baseNorm)
      exact shifted
    exact (RFAP.ConstructiveFraction.mul_pos_direct
      (show (0 : Coordinate) < 10 by decide) comparisonPositive).trans
        (lt_of_lt_of_le baselineStrict baselineLe)
  have firstProductNonnegative :
      0 ≤ (multipliedNorm - 10 * comparisonNorm) *
        (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct firstLeftNonnegative
      (RFAP.ConstructiveFraction.le_of_lt_direct firstRightPositive)
  have secondLeftPositive : 0 < 4 * comparisonNorm - baseNorm :=
    RFAP.ConstructiveFraction.sub_pos_direct baseLtFourComparison
  have secondRightPositive : 0 < 18 * comparisonNorm - baseNorm :=
    RFAP.ConstructiveFraction.sub_pos_direct (baseLtFourComparison.trans
      (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        (show (4 : Coordinate) < 18 by decide) comparisonPositive))
  have secondProductNonnegative :
      0 ≤ (4 * comparisonNorm - baseNorm) *
        (18 * comparisonNorm - baseNorm) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.le_of_lt_direct secondLeftPositive)
      (RFAP.ConstructiveFraction.le_of_lt_direct secondRightPositive)
  have nineSquarePositive : 0 < 9 * comparisonNorm ^ 2 := by
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.pow_pos_direct comparisonPositive 2)
  have polynomialPositive :
      0 <
        (multipliedNorm - 10 * comparisonNorm) *
            (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
          (4 * comparisonNorm - baseNorm) *
            (18 * comparisonNorm - baseNorm) +
          9 * comparisonNorm ^ 2 := by
    apply lt_of_lt_of_le nineSquarePositive
    calc
      9 * comparisonNorm ^ 2 ≤
          (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 :=
        le_add_of_nonneg_left secondProductNonnegative
      _ ≤
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            ((4 * comparisonNorm - baseNorm) *
                (18 * comparisonNorm - baseNorm) +
              9 * comparisonNorm ^ 2) :=
        le_add_of_nonneg_left firstProductNonnegative
      _ =
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 := by ring1
  have fourProductLtGapSquare :
      4 * (multipliedNorm * baseNorm) < gap ^ 2 := by
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    calc
      0 <
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 := polynomialPositive
      _ = gap ^ 2 - 4 * (multipliedNorm * baseNorm) := by
        dsimp only [gap]
        ring1
  exact (not_lt_of_ge
    (RFAP.ConstructiveFraction.le_of_lt_direct fourProductLtGapSquare)
    gapSquareLtFourProduct).elim

/-- An index-two consecutive pair has a uniform rational error-ratio gap:
the lower error quadrance is strictly less than four times the upper error
quadrance.  This deliberately weaker square-root-free form of Chevallier's
chamber bound is already strong enough to bound the coefficient in a
hypothetical repeated-index transition. -/
theorem AreConsecutiveBest.errorQuadrance_lower_lt_four_mul_upper_of_index_two
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    errorQuadrance source.value lower <
      4 * errorQuadrance source.value upper := by
  have errorOrdered :
      errorQuadrance source.value upper <
        errorQuadrance source.value lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have denominatorOrdered :
      normSq (toGaussian lower.denominator) <
        normSq (toGaussian upper.denominator) := by
    rw [normSq_toGaussian, normSq_toGaussian]
    exact RFAP.ConstructiveFraction.natCast_lt_direct consecutive.2.2.1
  have translatedObstruction
      (unit : GaussianInt) (unitNorm : normNat unit = 1) :
      (2 : Coordinate) * errorQuadrance source.value lower ≤
          normSq (error source.value upper -
            toGaussian unit * error source.value lower) ∨
        (2 : Coordinate) * normSq (toGaussian upper.denominator) ≤
          normSq (toGaussian upper.denominator -
            toGaussian unit * toGaussian lower.denominator) := by
    rcases consecutive.centeredUnit_selfObstruction indexTwo unit unitNorm with
      errorExterior | denominatorExterior
    · left
      have combinationError :
          error source.value
              (linearCombination lower upper (-unit) 1) =
            error source.value upper -
              toGaussian unit * error source.value lower := by
        rw [error_linearCombination]
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [toGaussian_neg, toGaussian_one,
            RFAP.ConstructiveGaussian.Gaussian.neg_re,
            RFAP.ConstructiveGaussian.Gaussian.neg_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      simpa only [errorQuadrance, combinationError] using errorExterior
    · right
      have castExterior :=
        RFAP.ConstructiveFraction.natCast_le_direct denominatorExterior
      have denominatorIdentity :
          toGaussian
              (linearCombination lower upper (-unit) 1).denominator =
            toGaussian upper.denominator -
              toGaussian unit * toGaussian lower.denominator := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [linearCombination, toGaussian_add, toGaussian_mul,
            toGaussian_neg, toGaussian_one,
            RFAP.ConstructiveGaussian.Gaussian.neg_re,
            RFAP.ConstructiveGaussian.Gaussian.neg_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
      calc
        (2 : Coordinate) * normSq (toGaussian upper.denominator) =
            ((2 * denominatorQuadrance upper : Nat) : Coordinate) := by
          rw [normSq_toGaussian]
          change (2 : Coordinate) *
              (denominatorQuadrance upper : Coordinate) =
            ((2 * denominatorQuadrance upper : Nat) : Coordinate)
          rw [Nat.cast_mul, Nat.cast_ofNat]
        _ ≤
            (denominatorQuadrance
              (linearCombination lower upper (-unit) 1) : Coordinate) :=
          castExterior
        _ = normSq
            (toGaussian
              (linearCombination lower upper (-unit) 1).denominator) :=
          (normSq_toGaussian _).symm
        _ = normSq (toGaussian upper.denominator -
            toGaussian unit * toGaussian lower.denominator) := by
          rw [denominatorIdentity]
  have positiveOneObstruction := translatedObstruction 1 rfl
  have negativeOneObstruction := translatedObstruction (-1) (by decide)
  have positiveImaginaryObstruction :=
    translatedObstruction RFAP.HurwitzGeometry.imaginaryUnit (by decide)
  have negativeImaginaryObstruction :=
    translatedObstruction (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide)
  exact four_unit_obstructions_force_error_lt_four_mul
    (error source.value lower) (error source.value upper)
    (toGaussian lower.denominator) (toGaussian upper.denominator)
    errorOrdered denominatorOrdered positiveOneObstruction
      negativeOneObstruction positiveImaginaryObstruction
      negativeImaginaryObstruction

/-- Constructive finite counterpart of the coefficient bound in Chevallier's
repeated-index lemma.  In the fully witnessed normal form, the nonzero
Gaussian step has quadrance at most four.  The proof combines the four-unit
error-ratio bound with one exact two-coordinate Cauchy calculation. -/
theorem AreConsecutiveBest.repeatedIndexTwo_boundedNormalForm
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      normNat lowerUnit = 1 ∧ step ≠ 0 ∧ normNat step ≤ 4 ∧
      upper = linearCombination lower middle lowerUnit
        (coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepNonzero,
      transitionIdentity⟩ :=
    first.repeatedIndexTwo_normalForm second leftIndexTwo rightIndexTwo
  have stepBound : normNat step ≤ 4 := by
    apply Nat.le_of_not_gt
    intro stepGreaterThanFour
    have stepAtLeastFive : 5 ≤ normNat step := by omega
    let determinantValue := coefficientDeterminant lower middle
    let baseValue :=
      toGaussian lowerUnit * error source.value lower
    let multipliedValue :=
      toGaussian (determinantValue * step) * error source.value middle
    let dotValue : Coordinate :=
      multipliedValue.re * baseValue.re +
        multipliedValue.im * baseValue.im
    have determinantNorm : normNat determinantValue = 2 := by
      simpa only [determinantValue, coefficientIndexQuadrance] using leftIndexTwo
    have comparisonPositive :
        0 < errorQuadrance source.value middle := by
      have upperSmaller :
          errorQuadrance source.value upper <
            errorQuadrance source.value middle :=
        second.2.1.2.1 middle second.1.1 second.2.2.1
      exact (normSq_nonneg (error source.value upper)).trans_lt upperSmaller
    have comparisonNonnegative :
        0 ≤ errorQuadrance source.value middle :=
      RFAP.ConstructiveFraction.le_of_lt_direct comparisonPositive
    have baseNormIdentity :
        normSq baseValue = errorQuadrance source.value lower := by
      dsimp only [baseValue, errorQuadrance]
      rw [normSq_mul, normSq_toGaussian, lowerUnitNorm]
      ring1
    have multipliedNormIdentity :
        normSq multipliedValue =
          (2 * normNat step : Nat) *
            errorQuadrance source.value middle := by
      dsimp only [multipliedValue, determinantValue, errorQuadrance]
      rw [normSq_mul, normSq_toGaussian, normNat_mul, determinantNorm]
    have tenLeMultiplierNormNat :
        10 ≤ 2 * normNat step := by omega
    have tenComparisonLe :
        (10 : Coordinate) * errorQuadrance source.value middle ≤
          normSq multipliedValue := by
      have castBound :=
        RFAP.ConstructiveFraction.natCast_le_direct tenLeMultiplierNormNat
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          castBound comparisonNonnegative
      rw [multipliedNormIdentity]
      exact scaled
    have baseLtFourComparison :
        normSq baseValue <
          4 * errorQuadrance source.value middle := by
      rw [baseNormIdentity]
      exact first.errorQuadrance_lower_lt_four_mul_upper_of_index_two
        leftIndexTwo
    have dotBound :
        dotValue ^ 2 ≤ normSq multipliedValue * normSq baseValue := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤
            (multipliedValue.re * baseValue.im -
              multipliedValue.im * baseValue.re) ^ 2 :=
          RFAP.ConstructiveFraction.sq_nonneg_direct _
        _ = normSq multipliedValue * normSq baseValue -
            dotValue ^ 2 := by
          dsimp only [dotValue, normSq]
          ring1
    have errorTransition :
        error source.value upper = baseValue + multipliedValue := by
      rw [transitionIdentity, error_linearCombination]
    have sumExpansion :
        errorQuadrance source.value upper =
          normSq multipliedValue + normSq baseValue + 2 * dotValue := by
      rw [errorQuadrance, errorTransition]
      dsimp only [dotValue, normSq]
      simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im]
      ring1
    have upperSmaller :
        errorQuadrance source.value upper <
          errorQuadrance source.value middle :=
      second.2.1.2.1 middle second.1.1 second.2.2.1
    exact large_summand_sum_not_lt_comparison comparisonPositive
      (normSq_nonneg baseValue) tenComparisonLe baseLtFourComparison
      dotBound sumExpansion upperSmaller
  exact ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, stepBound,
    transitionIdentity⟩

/-- A nonzero Gaussian integer of quadrance at most four has quadrance
exactly one, two, or four.  The proof is the finite coordinate classification
below six, with zero and five removed by the displayed hypotheses. -/
theorem normNat_eq_one_or_two_or_four_of_nonzero_of_le_four
    (step : GaussianInt) (stepNonzero : step ≠ 0)
    (stepBound : normNat step ≤ 4) :
    normNat step = 1 ∨ normNat step = 2 ∨ normNat step = 4 := by
  have stepSmall : normNat step < 6 := by omega
  rcases
      RFAP.HurwitzGeometry.normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
        step stepSmall with
    stepZero | stepOne | stepTwo | stepFour | stepFive
  · have actualZero :=
      RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero stepZero
    exact False.elim (stepNonzero actualZero)
  · exact Or.inl stepOne
  · exact Or.inr (Or.inl stepTwo)
  · exact Or.inr (Or.inr stepFour)
  · omega

/-- The bounded nonzero step has exactly one of the three Gaussian
quadrances `1`, `2`, or `4`.  Thus the remaining no-repeated-index argument
has only twelve displayed step values before unit symmetries are used. -/
theorem AreConsecutiveBest.repeatedIndexTwo_finiteNormalForm
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      normNat lowerUnit = 1 ∧
      (normNat step = 1 ∨ normNat step = 2 ∨ normNat step = 4) ∧
      upper = linearCombination lower middle lowerUnit
        (coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, stepBound,
      transitionIdentity⟩ :=
    first.repeatedIndexTwo_boundedNormalForm second leftIndexTwo rightIndexTwo
  have stepCases :=
    normNat_eq_one_or_two_or_four_of_nonzero_of_le_four step stepNonzero
      stepBound
  exact ⟨lowerUnit, step, lowerUnitNorm, stepCases, transitionIdentity⟩

/-- The only boundary pattern left by the diagonal centered-unit case cannot
occur over the displayed rationals.  Its four inequalities pin the real and
imaginary coordinates to opposite halves of `quadrance - 1`; substituting
back into the quadrance identity would give a rational square root of three.

This lemma records that final arithmetic obstruction independently of the
finite cylinder case table which produces the four hypotheses. -/
theorem centered_diagonal_boundary_impossible
    (realPart imaginaryPart : Coordinate) :
    let quadrance := realPart ^ 2 + imaginaryPart ^ 2
    2 ≤ 1 + quadrance - 2 * realPart →
    2 * quadrance ≤ 1 + quadrance + 2 * realPart →
    2 * quadrance ≤ 1 + quadrance - 2 * imaginaryPart →
    2 ≤ 1 + quadrance + 2 * imaginaryPart →
    False := by
  dsimp only
  let quadrance := realPart ^ 2 + imaginaryPart ^ 2
  intro positiveOneSelf negativeOneNext positiveImaginaryNext
    negativeImaginarySelf
  have realUpper : 2 * realPart ≤ quadrance - 1 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * realPart) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct positiveOneSelf
      _ = (quadrance - 1) - 2 * realPart := by ring1
  have realLower : quadrance - 1 ≤ 2 * realPart := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * realPart) - 2 * quadrance :=
        RFAP.ConstructiveFraction.sub_nonneg_direct negativeOneNext
      _ = 2 * realPart - (quadrance - 1) := by ring1
  have realIdentity : 2 * realPart = quadrance - 1 :=
    le_antisymm realUpper realLower
  have imaginaryUpper : 2 * imaginaryPart ≤ 1 - quadrance := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * imaginaryPart) - 2 * quadrance :=
        RFAP.ConstructiveFraction.sub_nonneg_direct positiveImaginaryNext
      _ = (1 - quadrance) - 2 * imaginaryPart := by ring1
  have imaginaryLower : 1 - quadrance ≤ 2 * imaginaryPart := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * imaginaryPart) - 2 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct negativeImaginarySelf
      _ = 2 * imaginaryPart - (1 - quadrance) := by ring1
  have imaginaryIdentity : 2 * imaginaryPart = 1 - quadrance :=
    le_antisymm imaginaryUpper imaginaryLower
  have scaledQuadrance :
      2 * (2 * quadrance) = 2 * (quadrance - 1) ^ 2 := by
    calc
      2 * (2 * quadrance) =
          (2 * realPart) ^ 2 + (2 * imaginaryPart) ^ 2 := by
        dsimp only [quadrance]
        ring1
      _ = (quadrance - 1) ^ 2 + (1 - quadrance) ^ 2 := by
        rw [realIdentity, imaginaryIdentity]
      _ = 2 * (quadrance - 1) ^ 2 := by ring1
  have quadranceIdentity :
      2 * quadrance = (quadrance - 1) ^ 2 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (2 : Coordinate) ≠ 0 by decide)
    simpa only [RFAP.ConstructiveFraction.mul_comm] using scaledQuadrance
  have forbiddenSquare : (quadrance - 2) ^ 2 = (3 : Coordinate) := by
    calc
      (quadrance - 2) ^ 2 =
          (quadrance - 1) ^ 2 - 2 * quadrance + 3 := by ring1
      _ = 3 := by rw [← quadranceIdentity]; ring1
  exact RFAP.ConstructiveFraction.square_ne_three
    (quadrance - 2) forbiddenSquare

/-- Homogeneous form of `centered_diagonal_boundary_impossible`.  Two
opposite self-cylinder error exteriors and the two interleaved next-cylinder
error exteriors force the same forbidden rational boundary, without first
naming a complex quotient. -/
theorem centered_diagonal_error_pattern_impossible
    (largeError smallError : Gaussian) (largeNonzero : largeError ≠ 0)
    (positiveOneSelf :
      (2 : Coordinate) * normSq largeError ≤
        normSq (smallError - largeError))
    (negativeOneNext :
      2 * normSq smallError ≤ normSq (smallError + largeError))
    (positiveImaginaryNext :
      2 * normSq smallError ≤
        normSq (smallError -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError))
    (negativeImaginarySelf :
      2 * normSq largeError ≤
        normSq (smallError +
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError)) :
    False := by
  let largeNorm := normSq largeError
  let smallNorm := normSq smallError
  let realProjection :=
    smallError.re * largeError.re + smallError.im * largeError.im
  let imaginaryProjection :=
    -smallError.re * largeError.im + smallError.im * largeError.re
  have positiveOneExpansion :
      normSq (smallError - largeError) =
        smallNorm + largeNorm - 2 * realProjection := by
    dsimp only [smallNorm, largeNorm, realProjection, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im]
    ring1
  have negativeOneExpansion :
      normSq (smallError + largeError) =
        smallNorm + largeNorm + 2 * realProjection := by
    dsimp only [smallNorm, largeNorm, realProjection, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im]
    ring1
  have positiveImaginaryExpansion :
      normSq (smallError -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError) =
        smallNorm + largeNorm - 2 * imaginaryProjection := by
    dsimp only [smallNorm, largeNorm, imaginaryProjection, normSq, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_zero, Int.cast_one]
    ring1
  have negativeImaginaryExpansion :
      normSq (smallError +
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit * largeError) =
        smallNorm + largeNorm + 2 * imaginaryProjection := by
    dsimp only [smallNorm, largeNorm, imaginaryProjection, normSq, toGaussian,
      RFAP.HurwitzGeometry.imaginaryUnit]
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_zero, Int.cast_one]
    ring1
  rw [positiveOneExpansion] at positiveOneSelf
  rw [negativeOneExpansion] at negativeOneNext
  rw [positiveImaginaryExpansion] at positiveImaginaryNext
  rw [negativeImaginaryExpansion] at negativeImaginarySelf
  have realUpper : 2 * realProjection ≤ smallNorm - largeNorm := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (smallNorm + largeNorm - 2 * realProjection) - 2 * largeNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct positiveOneSelf
      _ = (smallNorm - largeNorm) - 2 * realProjection := by ring1
  have realLower : smallNorm - largeNorm ≤ 2 * realProjection := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (smallNorm + largeNorm + 2 * realProjection) - 2 * smallNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct negativeOneNext
      _ = 2 * realProjection - (smallNorm - largeNorm) := by ring1
  have realIdentity :
      2 * realProjection = smallNorm - largeNorm :=
    le_antisymm realUpper realLower
  have imaginaryUpper :
      2 * imaginaryProjection ≤ largeNorm - smallNorm := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (smallNorm + largeNorm - 2 * imaginaryProjection) -
            2 * smallNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct positiveImaginaryNext
      _ = (largeNorm - smallNorm) - 2 * imaginaryProjection := by ring1
  have imaginaryLower :
      largeNorm - smallNorm ≤ 2 * imaginaryProjection := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (smallNorm + largeNorm + 2 * imaginaryProjection) -
            2 * largeNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct negativeImaginarySelf
      _ = 2 * imaginaryProjection - (largeNorm - smallNorm) := by ring1
  have imaginaryIdentity :
      2 * imaginaryProjection = largeNorm - smallNorm :=
    le_antisymm imaginaryUpper imaginaryLower
  have projectionSquares :
      realProjection ^ 2 + imaginaryProjection ^ 2 =
        smallNorm * largeNorm := by
    dsimp only [realProjection, imaginaryProjection, smallNorm, largeNorm,
      normSq]
    ring1
  have scaledProjectionIdentity :
      2 * (2 * (smallNorm * largeNorm)) =
        2 * (smallNorm - largeNorm) ^ 2 := by
    calc
      2 * (2 * (smallNorm * largeNorm)) =
          2 * (2 *
            (realProjection ^ 2 + imaginaryProjection ^ 2)) := by
        rw [projectionSquares]
      _ = (2 * realProjection) ^ 2 +
          (2 * imaginaryProjection) ^ 2 := by ring1
      _ = (smallNorm - largeNorm) ^ 2 +
          (largeNorm - smallNorm) ^ 2 := by
        rw [realIdentity, imaginaryIdentity]
      _ = 2 * (smallNorm - largeNorm) ^ 2 := by ring1
  have productIdentity :
      2 * (smallNorm * largeNorm) =
        (smallNorm - largeNorm) ^ 2 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (2 : Coordinate) ≠ 0 by decide)
    simpa only [RFAP.ConstructiveFraction.mul_comm] using
      scaledProjectionIdentity
  have homogeneousSquare :
      (smallNorm - 2 * largeNorm) ^ 2 = 3 * largeNorm ^ 2 := by
    calc
      (smallNorm - 2 * largeNorm) ^ 2 =
          (smallNorm - largeNorm) ^ 2 -
            2 * (smallNorm * largeNorm) + 3 * largeNorm ^ 2 := by ring1
      _ = 3 * largeNorm ^ 2 := by rw [← productIdentity]; ring1
  have largeNormPositive : 0 < largeNorm := by
    dsimp only [largeNorm]
    exact normSq_pos largeNonzero
  have largeNormNonzero : largeNorm ≠ 0 := ne_of_gt largeNormPositive
  let forbiddenRoot : Coordinate :=
    (smallNorm - 2 * largeNorm) * largeNorm⁻¹
  have forbiddenSquare : forbiddenRoot ^ 2 = (3 : Coordinate) := by
    dsimp only [forbiddenRoot]
    rw [pow_two]
    calc
      ((smallNorm - 2 * largeNorm) * largeNorm⁻¹) *
          ((smallNorm - 2 * largeNorm) * largeNorm⁻¹) =
          ((smallNorm - 2 * largeNorm) *
              (smallNorm - 2 * largeNorm)) *
            (largeNorm⁻¹ * largeNorm⁻¹) :=
        RFAP.ConstructiveFraction.mul_pair_swap _ _ _ _
      _ = (3 * (largeNorm * largeNorm)) *
          (largeNorm⁻¹ * largeNorm⁻¹) := by
        rw [← pow_two, homogeneousSquare, pow_two]
      _ = 3 * ((largeNorm * largeNorm) *
          (largeNorm⁻¹ * largeNorm⁻¹)) :=
        RFAP.ConstructiveFraction.mul_assoc _ _ _
      _ = 3 * ((largeNorm * largeNorm⁻¹) *
          (largeNorm * largeNorm⁻¹)) := by
        rw [RFAP.ConstructiveFraction.mul_pair_swap largeNorm largeNorm
          largeNorm⁻¹ largeNorm⁻¹]
      _ = 3 := by
        rw [RFAP.ConstructiveFraction.mul_inv_cancel largeNorm
          largeNormNonzero]
        change (3 : Coordinate) * (1 * 1) = 3
        ring1
  exact RFAP.ConstructiveFraction.square_ne_three forbiddenRoot
    forbiddenSquare

/-- Eliminating the centered candidate gives a finite, square-root-free
obstruction for each of the four Gaussian units.  Either the scaled
half-difference misses the next cylinder through its error coordinate, or it
misses through its denominator coordinate. -/
theorem AreConsecutiveBest.centeredUnit_obstruction
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    (2 : Coordinate) * errorQuadrance source.value middle ≤
        errorQuadrance source.value
          (linearCombination lower middle (-unit) 1) ∨
      2 * denominatorQuadrance upper ≤
        denominatorQuadrance
          (linearCombination lower middle (-unit) 1) := by
  obtain ⟨candidate, _, centeredIdentity, outside⟩ :=
    first.exists_centeredUnitCandidate_outside_nextCylinder second
      leftIndexTwo unit unitNorm
  have determinantNorm :
      normNat (coefficientDeterminant lower middle) = 2 := by
    simpa only [coefficientIndexQuadrance] using leftIndexTwo
  have errorIdentity :=
    congrArg (errorQuadrance source.value) centeredIdentity
  rw [errorQuadrance_scalePair, determinantNorm] at errorIdentity
  have denominatorIdentity :=
    congrArg denominatorQuadrance centeredIdentity
  rw [denominatorQuadrance_scalePair, determinantNorm] at denominatorIdentity
  by_cases errorInside :
      errorQuadrance source.value candidate <
        errorQuadrance source.value middle
  · have denominatorNotInside :
        ¬ denominatorQuadrance candidate < denominatorQuadrance upper := by
      intro denominatorInside
      exact outside ⟨errorInside, denominatorInside⟩
    right
    calc
      2 * denominatorQuadrance upper ≤
          2 * denominatorQuadrance candidate :=
        Nat.mul_le_mul_left 2 (Nat.le_of_not_gt denominatorNotInside)
      _ = denominatorQuadrance
          (linearCombination lower middle (-unit) 1) := denominatorIdentity
  · have errorOutside :
        errorQuadrance source.value middle ≤
          errorQuadrance source.value candidate :=
      le_of_not_gt errorInside
    left
    calc
      (2 : Coordinate) * errorQuadrance source.value middle ≤
          (2 : Coordinate) * errorQuadrance source.value candidate :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          errorOutside (by decide)
      _ = errorQuadrance source.value
          (linearCombination lower middle (-unit) 1) := errorIdentity

/-- The next-cylinder obstruction in geometric coordinate form. -/
theorem AreConsecutiveBest.centeredUnit_nextCoordinateObstruction
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    (2 : Coordinate) * normSq (error source.value middle) ≤
        normSq (error source.value middle -
          toGaussian unit * error source.value lower) ∨
      (2 : Coordinate) * normSq (toGaussian upper.denominator) ≤
        normSq (toGaussian middle.denominator -
          toGaussian unit * toGaussian lower.denominator) := by
  rcases first.centeredUnit_obstruction second leftIndexTwo unit unitNorm with
    errorExterior | denominatorExterior
  · left
    rw [← error_linearCombination_negUnit_one]
    exact errorExterior
  · right
    have castExterior :=
      RFAP.ConstructiveFraction.natCast_le_direct denominatorExterior
    calc
      (2 : Coordinate) * normSq (toGaussian upper.denominator) =
          ((2 * denominatorQuadrance upper : Nat) : Coordinate) := by
        rw [normSq_toGaussian]
        change (2 : Coordinate) *
            (denominatorQuadrance upper : Coordinate) =
          ((2 * denominatorQuadrance upper : Nat) : Coordinate)
        rw [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤
          (denominatorQuadrance
            (linearCombination lower middle (-unit) 1) : Coordinate) :=
        castExterior
      _ = normSq
          (toGaussian
            (linearCombination lower middle (-unit) 1).denominator) :=
        (normSq_toGaussian _).symm
      _ = normSq (toGaussian middle.denominator -
          toGaussian unit * toGaussian lower.denominator) := by
        rw [toGaussian_denominator_linearCombination_negUnit_one]

/-- The four interleaved centered-unit tests cannot all escape through their
error coordinates.  Consequently at least one of the displayed denominator
exteriors is forced.  This removes the sole diagonal boundary pattern left
by the real polynomial relaxation before the remaining denominator cases
are considered. -/
theorem AreConsecutiveBest.centeredDiagonal_forces_denominator_obstruction
    {source : Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2) :
    ((2 : Coordinate) * normSq (toGaussian middle.denominator) ≤
        normSq (toGaussian middle.denominator -
          toGaussian (1 : GaussianInt) * toGaussian lower.denominator)) ∨
      ((2 : Coordinate) * normSq (toGaussian upper.denominator) ≤
        normSq (toGaussian middle.denominator -
          toGaussian (-1 : GaussianInt) * toGaussian lower.denominator)) ∨
      ((2 : Coordinate) * normSq (toGaussian upper.denominator) ≤
        normSq (toGaussian middle.denominator -
          toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
            toGaussian lower.denominator)) ∨
      ((2 : Coordinate) * normSq (toGaussian middle.denominator) ≤
        normSq (toGaussian middle.denominator -
          toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) *
            toGaussian lower.denominator)) := by
  have positiveOne := first.centeredUnit_selfCoordinateObstruction
    leftIndexTwo 1 rfl
  have negativeOne := first.centeredUnit_nextCoordinateObstruction second
    leftIndexTwo (-1) (by decide)
  have positiveImaginary := first.centeredUnit_nextCoordinateObstruction
    second leftIndexTwo RFAP.HurwitzGeometry.imaginaryUnit (by decide)
  have negativeImaginary := first.centeredUnit_selfCoordinateObstruction
    leftIndexTwo (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide)
  rcases positiveOne with positiveOneError | positiveOneDenominator
  · rcases negativeOne with negativeOneError | negativeOneDenominator
    · rcases positiveImaginary with
        positiveImaginaryError | positiveImaginaryDenominator
      · rcases negativeImaginary with
          negativeImaginaryError | negativeImaginaryDenominator
        · have errorOrdered :
              normSq (error source.value middle) <
                normSq (error source.value lower) :=
            first.2.1.2.1 lower first.1.1 first.2.2.1
          have largeNonzero : error source.value lower ≠ 0 := by
            intro errorZero
            have lowerNormZero := congrArg normSq errorZero
            rw [normSq_zero] at lowerNormZero
            have middleNonnegative := normSq_nonneg (error source.value middle)
            rw [lowerNormZero] at errorOrdered
            exact (not_lt_of_ge middleNonnegative) errorOrdered
          have negativeOneIdentity :
              error source.value middle -
                  toGaussian (-1 : GaussianInt) * error source.value lower =
                error source.value middle + error source.value lower := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [toGaussian_neg, toGaussian_one,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im,
                RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.add_re,
                RFAP.ConstructiveGaussian.Gaussian.add_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
              ring1
          have negativeImaginaryIdentity :
              error source.value middle -
                  toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) *
                    error source.value lower =
                error source.value middle +
                  toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                    error source.value lower := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [toGaussian_neg,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im,
                RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.add_re,
                RFAP.ConstructiveGaussian.Gaussian.add_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
              ring1
          rw [negativeOneIdentity] at negativeOneError
          rw [negativeImaginaryIdentity] at negativeImaginaryError
          have positiveOneError' :
              (2 : Coordinate) * normSq (error source.value lower) ≤
                normSq (error source.value middle -
                  error source.value lower) := by
            simpa only [toGaussian_one,
              RFAP.ConstructiveGaussian.Gaussian.one_mul] using
              positiveOneError
          exact (centered_diagonal_error_pattern_impossible
            (error source.value lower) (error source.value middle)
            largeNonzero positiveOneError' negativeOneError
            positiveImaginaryError negativeImaginaryError).elim
        · exact Or.inr (Or.inr (Or.inr negativeImaginaryDenominator))
      · exact Or.inr (Or.inr (Or.inl positiveImaginaryDenominator))
    · exact Or.inr (Or.inl negativeOneDenominator)
  · exact Or.inl positiveOneDenominator

/-- The empty-cylinder criterion excludes every nontrivial displayed integral
linear combination of two consecutive best pairs from the mixed interior. -/
theorem AreConsecutiveBest.linearCombination_not_in_mixedCylinder
    {source : Fraction} {left right : Pair}
    (consecutive : AreConsecutiveBest source.value left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    ¬ InOpenMixedCylinder source.value left right
      (linearCombination left right leftCoefficient rightCoefficient) := by
  have cylinderEmpty :=
    (areConsecutiveBest_iff_mixedCylinderEmpty source left right).mp consecutive
      |>.2.2.2
  exact cylinderEmpty _
    (consecutive.linearCombination_pairNonzero leftCoefficient rightCoefficient
      coefficientNonzero)

/-- Square-root-free exterior alternative for every nontrivial integral
combination: either its error reaches the lower boundary or its denominator
reaches the upper boundary. -/
theorem AreConsecutiveBest.linearCombination_outside_mixedCylinder
    {source : Fraction} {left right : Pair}
    (consecutive : AreConsecutiveBest source.value left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    errorQuadrance source.value left ≤
        errorQuadrance source.value
          (linearCombination left right leftCoefficient rightCoefficient) ∨
      denominatorQuadrance right ≤
        denominatorQuadrance
          (linearCombination left right leftCoefficient rightCoefficient) := by
  by_cases errorInside :
      errorQuadrance source.value
          (linearCombination left right leftCoefficient rightCoefficient) <
        errorQuadrance source.value left
  · by_cases denominatorInside :
        denominatorQuadrance
            (linearCombination left right leftCoefficient rightCoefficient) <
          denominatorQuadrance right
    · exact (consecutive.linearCombination_not_in_mixedCylinder
        leftCoefficient rightCoefficient coefficientNonzero
        ⟨errorInside, denominatorInside⟩).elim
    · exact Or.inr (Nat.le_of_not_gt denominatorInside)
  · exact Or.inl (le_of_not_gt errorInside)

/-- A source-computed finite bound for the coefficient-index quadrance of any
two consecutive best pairs.  The much sharper universal values `1` and `2`
require the local geometry-of-numbers argument; this bound uses only the
already verified global candidate rectangle. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_le_sourceBound
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    coefficientIndexQuadrance lower upper ≤
      4 * numeratorQuadranceBound source * normNat source.denominator := by
  have lowerNumeratorBound := numeratorQuadrance_le_bound
    consecutive.1.denominatorQuadrance_le_source
    consecutive.1.errorQuadrance_le_half
  have upperNumeratorBound := numeratorQuadrance_le_bound
    consecutive.2.1.denominatorQuadrance_le_source
    consecutive.2.1.errorQuadrance_le_half
  have lowerDenominatorBound := consecutive.1.denominatorQuadrance_le_source
  have upperDenominatorBound :=
    consecutive.2.1.denominatorQuadrance_le_source
  calc
    coefficientIndexQuadrance lower upper =
        normNat
          (lower.numerator * upper.denominator -
            upper.numerator * lower.denominator) := rfl
    _ ≤ 2 *
        (normNat (lower.numerator * upper.denominator) +
          normNat (upper.numerator * lower.denominator)) :=
      normNat_sub_le_two _ _
    _ = 2 *
        (normNat lower.numerator * normNat upper.denominator +
          normNat upper.numerator * normNat lower.denominator) := by
      rw [normNat_mul, normNat_mul]
    _ ≤ 2 *
        (numeratorQuadranceBound source * normNat source.denominator +
          numeratorQuadranceBound source * normNat source.denominator) := by
      exact Nat.mul_le_mul_left 2
        (Nat.add_le_add
          (Nat.mul_le_mul lowerNumeratorBound upperDenominatorBound)
          (Nat.mul_le_mul upperNumeratorBound lowerDenominatorBound))
    _ = 4 * numeratorQuadranceBound source *
        normNat source.denominator := by ring1

/-- Squared Dirichlet product attached to one consecutive pair: the upper
denominator quadrance times the lower pair's error quadrance. -/
def dirichletWindowQuadrance
    (source : Gaussian) (lower upper : Pair) : Coordinate :=
  (denominatorQuadrance upper : Coordinate) * errorQuadrance source lower

/-- The determinant quadrance of a consecutive pair is strictly less than
four times its squared Dirichlet-window product.  This is a wholly finite
reverse bound: the product cannot collapse toward zero while the displayed
coefficient determinant remains nonzero. -/
theorem AreConsecutiveBest.coefficientIndexQuadrance_lt_four_mul_dirichletWindow
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper) :
    (coefficientIndexQuadrance lower upper : Coordinate) <
      4 * dirichletWindowQuadrance source lower upper := by
  have denominatorOrdered :
      (denominatorQuadrance lower : Coordinate) <
        (denominatorQuadrance upper : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_lt_direct consecutive.2.2.1
  have errorOrdered :
      errorQuadrance source upper < errorQuadrance source lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have upperDenominatorPositive :
      (0 : Coordinate) < (denominatorQuadrance upper : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos consecutive.2.1.1)
  have crossProductStrict :
      (denominatorQuadrance lower : Coordinate) *
          errorQuadrance source upper <
        (denominatorQuadrance upper : Coordinate) *
          errorQuadrance source lower := by
    calc
      (denominatorQuadrance lower : Coordinate) *
            errorQuadrance source upper ≤
          (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source upper :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          denominatorOrdered.le (normSq_nonneg (error source upper))
      _ < (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          upperDenominatorPositive errorOrdered
  have sumStrict :
      (denominatorQuadrance lower : Coordinate) *
            errorQuadrance source upper +
          (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower <
        (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower +
          (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower :=
    by
      exact RFAP.ConstructiveFraction.add_lt_add_right_direct
        crossProductStrict
        ((denominatorQuadrance upper : Coordinate) *
          errorQuadrance source lower)
  have scaledStrict :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) sumStrict
  calc
    (coefficientIndexQuadrance lower upper : Coordinate) =
        normSq (toGaussian (coefficientDeterminant lower upper)) := by
      rw [normSq_toGaussian]
      rfl
    _ = normSq
        (toGaussian lower.denominator * error source upper -
          toGaussian upper.denominator * error source lower) := by
      rw [toGaussian_coefficientDeterminant]
    _ ≤ 2 *
        (normSq (toGaussian lower.denominator * error source upper) +
          normSq (toGaussian upper.denominator * error source lower)) :=
      normSq_sub_le_two _ _
    _ = 2 *
        ((denominatorQuadrance lower : Coordinate) *
            errorQuadrance source upper +
          (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower) := by
      rw [normSq_mul, normSq_mul, normSq_toGaussian, normSq_toGaussian]
      rfl
    _ < 2 *
        ((denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower +
          (denominatorQuadrance upper : Coordinate) *
            errorQuadrance source lower) := scaledStrict
    _ = 4 * dirichletWindowQuadrance source lower upper := by
      unfold dirichletWindowQuadrance
      ring1

/-- Every consecutive window has squared Dirichlet product strictly greater
than one quarter, stated without division. -/
theorem AreConsecutiveBest.one_lt_four_mul_dirichletWindow
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper) :
    (1 : Coordinate) < 4 * dirichletWindowQuadrance source lower upper := by
  have determinantPositive := consecutive.coefficientIndexQuadrance_pos
  have oneLeDeterminant : 1 ≤ coefficientIndexQuadrance lower upper := by
    omega
  exact (RFAP.ConstructiveFraction.natCast_le_direct oneLeDeterminant).trans_lt
    consecutive.coefficientIndexQuadrance_lt_four_mul_dirichletWindow

/-- In the index-two case the same determinant calculation strengthens the
universal lower bound from one quarter to one half, again without division. -/
theorem AreConsecutiveBest.two_lt_four_mul_dirichletWindow_of_indexTwo
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (2 : Coordinate) < 4 * dirichletWindowQuadrance source lower upper := by
  calc
    (2 : Coordinate) =
        (coefficientIndexQuadrance lower upper : Coordinate) := by
      simpa using congrArg (fun value : Nat => (value : Coordinate))
        indexTwo.symm
    _ < 4 * dirichletWindowQuadrance source lower upper :=
      consecutive.coefficientIndexQuadrance_lt_four_mul_dirichletWindow

/-- Throughout the natural-height window between two consecutive best levels,
the lower pair is an admissible approximation and its scaled error is bounded
by the displayed endpoint product.  This is the finite square-root-free form
of the consecutive-product expression for a Dirichlet constant. -/
theorem AreConsecutiveBest.lower_witnesses_dirichletWindow
    {source : Gaussian} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source lower upper)
    (request : Nat)
    (aboveLower : denominatorQuadrance lower < request)
    (noHigherThanUpper : request ≤ denominatorQuadrance upper) :
    lower.denominator ≠ 0 ∧
      denominatorQuadrance lower < request ∧
      (request : Coordinate) * errorQuadrance source lower ≤
        dirichletWindowQuadrance source lower upper := by
  refine ⟨consecutive.1.1, aboveLower, ?_⟩
  unfold dirichletWindowQuadrance
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (RFAP.ConstructiveFraction.natCast_le_direct noHigherThanUpper)
    (normSq_nonneg (error source lower))

/-- Every finite consecutive window for a displayed rational source has a
source-computed Dirichlet-product bound. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_sourceBound
    {source : Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      (normNat source.denominator : Coordinate) / 2 := by
  have denominatorBound :
      (denominatorQuadrance upper : Coordinate) ≤
        (normNat source.denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct
      consecutive.2.1.denominatorQuadrance_le_source
  have sourceDenominatorNonnegative :
      (0 : Coordinate) ≤ (normNat source.denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _)
  calc
    dirichletWindowQuadrance source.value lower upper =
        (denominatorQuadrance upper : Coordinate) *
          errorQuadrance source.value lower := rfl
    _ ≤ (normNat source.denominator : Coordinate) * (1 / 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct denominatorBound
        consecutive.1.errorQuadrance_le_half
        (normSq_nonneg (error source.value lower))
        sourceDenominatorNonnegative
    _ = (normNat source.denominator : Coordinate) / 2 := by
      change
        (normNat source.denominator : Coordinate) *
            (1 * (2 : Coordinate)⁻¹) =
          (normNat source.denominator : Coordinate) * (2 : Coordinate)⁻¹
      rw [RFAP.ConstructiveFraction.one_mul]

/-- The finite implication checked for one possible intermediate pair. -/
def CandidateNotIntermediate (source : Fraction) (lower upper middle : Pair) :
    Prop :=
  PassesBestTest source middle →
    ¬ (denominatorQuadrance lower < denominatorQuadrance middle ∧
      denominatorQuadrance middle < denominatorQuadrance upper)

instance candidateNotIntermediateDecidable
    (source : Fraction) (lower upper middle : Pair) :
    Decidable (CandidateNotIntermediate source lower upper middle) := by
  unfold CandidateNotIntermediate
  infer_instance

/-- Structural finite conjunction asserting that no candidate in a supplied
list is a best pair at an intermediate denominator level. -/
def EveryCandidateNotIntermediate
    (source : Fraction) (lower upper : Pair) : List Pair → Prop
  | [] => True
  | middle :: remaining =>
      CandidateNotIntermediate source lower upper middle ∧
        EveryCandidateNotIntermediate source lower upper remaining

instance everyCandidateNotIntermediateDecidable
    (source : Fraction) (lower upper : Pair) (list : List Pair) :
    Decidable (EveryCandidateNotIntermediate source lower upper list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons middle remaining inductionHypothesis =>
      letI : Decidable
          (EveryCandidateNotIntermediate source lower upper remaining) :=
        inductionHypothesis
      change Decidable
        (CandidateNotIntermediate source lower upper middle ∧
          EveryCandidateNotIntermediate source lower upper remaining)
      infer_instance

theorem EveryCandidateNotIntermediate.of_mem
    {source : Fraction} {lower upper middle : Pair} {list : List Pair}
    (every : EveryCandidateNotIntermediate source lower upper list)
    (member : middle ∈ list) :
    CandidateNotIntermediate source lower upper middle := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change CandidateNotIntermediate source lower upper head ∧
        EveryCandidateNotIntermediate source lower upper remaining at every
      rcases List.mem_cons.mp member with equal | tailMember
      · subst middle
        exact every.1
      · exact inductionHypothesis every.2 tailMember

theorem everyCandidateNotIntermediate_of_forall
    {source : Fraction} {lower upper : Pair} {list : List Pair}
    (noneBetween : ∀ middle ∈ list,
      CandidateNotIntermediate source lower upper middle) :
    EveryCandidateNotIntermediate source lower upper list := by
  induction list with
  | nil => trivial
  | cons middle remaining inductionHypothesis =>
      exact ⟨noneBetween middle List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          noneBetween candidate (List.mem_cons_of_mem _ member))⟩

/-- Executable certificate that two supplied pairs occupy consecutive best
denominator levels. -/
def PassesConsecutiveTest (source : Fraction) (lower upper : Pair) : Prop :=
  PassesBestTest source lower ∧ PassesBestTest source upper ∧
    denominatorQuadrance lower < denominatorQuadrance upper ∧
    EveryCandidateNotIntermediate source lower upper (candidates source)

instance passesConsecutiveTestDecidable
    (source : Fraction) (lower upper : Pair) :
    Decidable (PassesConsecutiveTest source lower upper) := by
  unfold PassesConsecutiveTest
  infer_instance

/-- Exactness of the bounded consecutive-level test. -/
theorem passesConsecutiveTest_iff
    (source : Fraction) (lower upper : Pair) :
    PassesConsecutiveTest source lower upper ↔
      AreConsecutiveBest source.value lower upper := by
  constructor
  · intro passes
    refine ⟨(passesBestTest_iff_isBest source lower).mp passes.1,
      (passesBestTest_iff_isBest source upper).mp passes.2.1,
      passes.2.2.1, ?_⟩
    intro middle middleBest between
    have middleMember := middleBest.mem_candidates
    have checked := EveryCandidateNotIntermediate.of_mem passes.2.2.2
      middleMember
    exact checked ((passesBestTest_iff_isBest source middle).mpr middleBest)
      between
  · intro consecutive
    refine ⟨(passesBestTest_iff_isBest source lower).mpr consecutive.1,
      (passesBestTest_iff_isBest source upper).mpr consecutive.2.1,
      consecutive.2.2.1, ?_⟩
    apply everyCandidateNotIntermediate_of_forall
    intro middle _ middlePasses between
    exact consecutive.2.2.2 middle
      ((passesBestTest_iff_isBest source middle).mp middlePasses) between

/-- Retain all candidates occupying the next best denominator level above a
supplied lower pair. -/
def retainConsecutiveSuccessors (source : Fraction) (lower : Pair) :
    List Pair → List Pair
  | [] => []
  | candidate :: remaining =>
      if PassesConsecutiveTest source lower candidate then
        candidate :: retainConsecutiveSuccessors source lower remaining
      else
        retainConsecutiveSuccessors source lower remaining

theorem mem_retainConsecutiveSuccessors_iff
    (source : Fraction) (lower candidate : Pair) (list : List Pair) :
    candidate ∈ retainConsecutiveSuccessors source lower list ↔
      candidate ∈ list ∧ PassesConsecutiveTest source lower candidate := by
  induction list with
  | nil =>
      simp only [retainConsecutiveSuccessors, List.not_mem_nil, false_and]
  | cons head remaining inductionHypothesis =>
      by_cases headPasses : PassesConsecutiveTest source lower head
      · rw [retainConsecutiveSuccessors, if_pos headPasses, List.mem_cons,
          inductionHypothesis, List.mem_cons]
        constructor
        · intro member
          rcases member with equal | tail
          · subst candidate
            exact ⟨Or.inl rfl, headPasses⟩
          · exact ⟨Or.inr tail.1, tail.2⟩
        · intro member
          rcases member.1 with equal | tailMember
          · exact Or.inl equal
          · exact Or.inr ⟨tailMember, member.2⟩
      · rw [retainConsecutiveSuccessors, if_neg headPasses,
          inductionHypothesis, List.mem_cons]
        constructor
        · intro member
          exact ⟨Or.inr member.1, member.2⟩
        · intro member
          rcases member.1 with equal | tailMember
          · subst candidate
            exact (headPasses member.2).elim
          · exact ⟨tailMember, member.2⟩

/-- Complete finite list of the pairs at the consecutive best denominator
level above `lower`.  The list is empty exactly when no such level exists. -/
def consecutiveSuccessors (source : Fraction) (lower : Pair) : List Pair :=
  retainConsecutiveSuccessors source lower (candidates source)

/-- Soundness and completeness of the finite consecutive-minimal-vector
successor list. -/
theorem mem_consecutiveSuccessors_iff
    (source : Fraction) (lower candidate : Pair) :
    candidate ∈ consecutiveSuccessors source lower ↔
      AreConsecutiveBest source.value lower candidate := by
  rw [consecutiveSuccessors, mem_retainConsecutiveSuccessors_iff]
  constructor
  · intro selected
    exact (passesConsecutiveTest_iff source lower candidate).mp selected.2
  · intro consecutive
    exact ⟨consecutive.2.1.mem_candidates,
      (passesConsecutiveTest_iff source lower candidate).mpr consecutive⟩

theorem retainConsecutiveSuccessors_length_le
    (source : Fraction) (lower : Pair) (list : List Pair) :
    (retainConsecutiveSuccessors source lower list).length ≤ list.length := by
  induction list with
  | nil => rfl
  | cons candidate remaining inductionHypothesis =>
      rw [retainConsecutiveSuccessors]
      by_cases passes : PassesConsecutiveTest source lower candidate
      · rw [if_pos passes, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ inductionHypothesis
      · rw [if_neg passes, List.length_cons]
        exact inductionHypothesis.trans (Nat.le_succ _)

/-- The consecutive successor list inherits the explicit all-best candidate
bound. -/
theorem consecutiveSuccessors_length_le (source : Fraction) (lower : Pair) :
    (consecutiveSuccessors source lower).length ≤
      16 * (normNat source.denominator + 1) ^ 2 *
        (numeratorQuadranceBound source + 1) ^ 2 := by
  exact
    (retainConsecutiveSuccessors_length_le source lower (candidates source)).trans_eq
      (candidates_length source)

end RFAP.BestApproximation
