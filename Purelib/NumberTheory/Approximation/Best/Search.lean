module
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Enumeration
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Util.CompileInductive

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section

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

namespace Purelib.NumberTheory.Approximation.Best.Search

/-- The displayed numerator and denominator of the source itself, viewed as
an exact competitor. -/
@[expose] def exactPair (source : GaussianInt.Fraction) :
  GaussianInt.Pair.Basic.ConvergentPair :=
  { numerator := source.numerator
    denominator := source.denominator }

/-- The exact source pair retains its original Gaussian-integer denominator. -/
@[simp] theorem exactPair_denominator (source :
  GaussianInt.Fraction) :
    (exactPair source).denominator = source.denominator := rfl

/-- The displayed source pair has zero division-free approximation error. -/
theorem exactPair_error (source : GaussianInt.Fraction) :
    Best.Error.error source.value (exactPair source) = 0 := by
  rw [Best.Error.error, exactPair, source.value_mul_denominator]
  exact Gaussian.Basic.sub_self _

/-- For a displayed rational source, every best approximation occurs no
later than the source's own displayed denominator height.  The exact source
pair is the finite witness excluding every larger denominator. -/
theorem IsBest.denominatorQuadrance_le_source
    {source : GaussianInt.Fraction} {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source.value reference) :
    Best.Error.denominatorQuadrance reference ≤ GaussianInt.normNat source.denominator := by
  apply Nat.le_of_not_gt
  intro sourceDenominatorSmaller
  have impossible := best.2.1 (exactPair source) source.denominatorNonzero
    sourceDenominatorSmaller
  change Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value reference) <
    Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value (exactPair source)) at impossible
  rw [exactPair_error, Gaussian.Norm.Basic.normSq_zero] at impossible
  exact (not_lt_of_ge (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value reference))) impossible

/-! ## Finite search bounds -/

/-- Clearing the displayed source denominator turns the rational error into
an exact Gaussian-integer record. -/
@[expose] def clearedError (source : GaussianInt.Fraction) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : GaussianInt :=
  source.numerator * pair.denominator -
    pair.numerator * source.denominator

/-- Embedding the cleared integer error multiplies the rational error by the source denominator. -/
theorem toGaussian_clearedError (source : GaussianInt.Fraction)
  (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    GaussianInt.toGaussian (clearedError source pair) =
      Best.Error.error source.value pair * GaussianInt.toGaussian source.denominator := by
  rw [clearedError,
    GaussianInt.toGaussian_sub,
    GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul, ← source.value_mul_denominator]
  apply Gaussian.Basic.ext <;>
    simp only [Best.Error.error,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
    ring1

/-- The cleared-error norm is the error quadrance times the source-denominator norm. -/
theorem clearedError_norm_identity (source : GaussianInt.Fraction)
  (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    (GaussianInt.normNat (clearedError source pair) : Fraction.Rational) =
      Best.Error.errorQuadrance source.value pair *
        (GaussianInt.normNat source.denominator : Fraction.Rational) := by
  rw [← GaussianInt.normSq_toGaussian, toGaussian_clearedError, Gaussian.Norm.Basic.normSq_mul,
    GaussianInt.normSq_toGaussian]
  rfl

/-- Error quadrance at most one half gives an integral cleared-error
quadrance no larger than the source denominator quadrance. -/
theorem clearedError_normNat_le_denominator
    {source : GaussianInt.Fraction} {pair : GaussianInt.Pair.Basic.ConvergentPair}
    (smallError : Best.Error.errorQuadrance source.value pair ≤ 1 / 2) :
    GaussianInt.normNat (clearedError source pair) ≤ GaussianInt.normNat source.denominator := by
  apply (Fraction.Cast.Order.natCast_le_iff_direct).1
  have denominatorNonnegative :
      (0 : Fraction.Rational) ≤ (GaussianInt.normNat source.denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  calc
    (GaussianInt.normNat (clearedError source pair) : Fraction.Rational) =
        Best.Error.errorQuadrance source.value pair *
          (GaussianInt.normNat source.denominator : Fraction.Rational) :=
      clearedError_norm_identity source pair
    _ ≤ (1 / 2 : Fraction.Rational) *
          (GaussianInt.normNat source.denominator : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        smallError denominatorNonnegative
    _ ≤ 1 * (GaussianInt.normNat source.denominator : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Fraction.Rational) ≤ 1 by decide) denominatorNonnegative
    _ = (GaussianInt.normNat source.denominator : Fraction.Rational) := by ring1

/-- Recover the cross-multiplied numerator by subtracting the retained cleared error. -/
theorem numerator_mul_denominator_eq (source :
  GaussianInt.Fraction) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair.numerator * source.denominator =
      source.numerator * pair.denominator - clearedError source pair := by
  apply GaussianInt.ext <;>
    simp only [clearedError,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im, -eq_self, -iff_self] <;>
    ring1

/-- A single source-computed numerator quadrance bound sufficient for every
pair with denominator no larger than the source and error at most one half. -/
@[expose] def numeratorQuadranceBound (source :
  GaussianInt.Fraction) : Nat :=
  2 * (GaussianInt.normNat source.numerator * GaussianInt.normNat source.denominator +
    GaussianInt.normNat source.denominator)

/-- The source-computed numerator bound contains every pair of bounded denominator and error at most one half. -/
theorem numeratorQuadrance_le_bound
    {source : GaussianInt.Fraction} {pair : GaussianInt.Pair.Basic.ConvergentPair}
    (denominatorBounded :
      Best.Error.denominatorQuadrance pair ≤ GaussianInt.normNat source.denominator)
    (smallError : Best.Error.errorQuadrance source.value pair ≤ 1 / 2) :
    GaussianInt.normNat pair.numerator ≤ numeratorQuadranceBound source := by
  have denominatorPositive := GaussianInt.normNat_pos source.denominatorNonzero
  have clearedBound :=
    clearedError_normNat_le_denominator (source := source) (pair := pair)
      smallError
  have productBound :
      GaussianInt.normNat (pair.numerator * source.denominator) ≤
        numeratorQuadranceBound source := by
    rw [numerator_mul_denominator_eq]
    have normBound := GaussianInt.Norm.Bounds.normNat_add_le_two
      (source.numerator * pair.denominator) (-clearedError source pair)
    rw [← GaussianInt.sub_eq_add_neg, GaussianInt.normNat_neg] at normBound
    refine normBound.trans ?_
    rw [GaussianInt.normNat_mul]
    exact Nat.mul_le_mul_left 2
      (Nat.add_le_add
        (Nat.mul_le_mul_left (GaussianInt.normNat source.numerator) denominatorBounded)
        clearedBound)
  calc
    GaussianInt.normNat pair.numerator = GaussianInt.normNat pair.numerator * 1 :=
      (Nat.mul_one _).symm
    _ ≤ GaussianInt.normNat pair.numerator * GaussianInt.normNat source.denominator :=
      Nat.mul_le_mul_left _ denominatorPositive
    _ = GaussianInt.normNat (pair.numerator * source.denominator) :=
      (GaussianInt.normNat_mul _ _).symm
    _ ≤ numeratorQuadranceBound source := productBound

/-- Finite rectangular over-enumeration containing every possible best pair
for this displayed rational source. -/
@[expose] def candidates (source : GaussianInt.Fraction) : List
  GaussianInt.Pair.Basic.ConvergentPair :=
  (GaussianInt.componentSquare
      (GaussianInt.normNat source.denominator)).flatMap fun denominator =>
    (GaussianInt.componentSquare
      (numeratorQuadranceBound source)).map fun numerator =>
        { numerator := numerator
          denominator := denominator }

/-- Exact size of the finite rectangular over-enumeration. -/
@[simp] theorem candidates_length (source : GaussianInt.Fraction)
  :
    (candidates source).length =
      16 * Nat.pow (GaussianInt.normNat source.denominator + 1) 2 *
        Nat.pow (numeratorQuadranceBound source + 1) 2 := by
  rw [candidates, List.Flatten.length_flatMap_map]
  simp only [
    GaussianInt.componentSquare_length, -eq_self, -iff_self]
  ring1

/-- A denominator-bounded pair with error at most one half belongs to the finite source rectangle. -/
theorem mem_candidates_of_bounds {source : GaussianInt.Fraction}
  {pair : GaussianInt.Pair.Basic.ConvergentPair}
    (denominatorBounded :
      Best.Error.denominatorQuadrance pair ≤ GaussianInt.normNat source.denominator)
    (smallError : Best.Error.errorQuadrance source.value pair ≤ 1 / 2) :
    pair ∈ candidates source := open Purelib in by
  rw [candidates]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨pair.denominator,
    GaussianInt.mem_componentSquare_of_normNat_le
      denominatorBounded, ?_⟩
  apply Data.List.Map.mem_map.mpr
  refine ⟨pair.numerator,
    GaussianInt.mem_componentSquare_of_normNat_le
      (numeratorQuadrance_le_bound denominatorBounded smallError), ?_⟩
  cases pair
  rfl

/-- Every best pair occurs in the explicit candidate rectangle for its rational source. -/
theorem IsBest.mem_candidates {source : GaussianInt.Fraction}
  {pair : GaussianInt.Pair.Basic.ConvergentPair}
    (best : Best.Basic.IsBest source.value pair) : pair ∈ candidates source :=
  mem_candidates_of_bounds (Best.Search.IsBest.denominatorQuadrance_le_source best)
    best.errorQuadrance_le_half

/-! ## Executable all-best selection -/

/-- The two comparisons which one bounded candidate must satisfy relative to
the proposed best pair. -/
@[expose] def RespectsCandidate (source : GaussianInt.Fraction)
  (reference candidate : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  (candidate.denominator ≠ 0 →
      Best.Error.denominatorQuadrance candidate < Best.Error.denominatorQuadrance reference →
      Best.Error.errorQuadrance source.value reference <
        Best.Error.errorQuadrance source.value candidate) ∧
    (candidate.denominator ≠ 0 →
      Best.Error.denominatorQuadrance candidate ≤ Best.Error.denominatorQuadrance reference →
      Best.Error.errorQuadrance source.value reference ≤
        Best.Error.errorQuadrance source.value candidate)

/-- Decide the two exact comparisons for one retained candidate and reference pair. -/
instance respectsCandidateDecidable
    (source : GaussianInt.Fraction) (reference candidate : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (RespectsCandidate source reference candidate) := by
  unfold RespectsCandidate
  infer_instance

/-- A structural finite conjunction over the displayed candidate list. -/
@[expose] def EveryCandidateRespects (source :
  GaussianInt.Fraction) (reference : GaussianInt.Pair.Basic.ConvergentPair) :
    List GaussianInt.Pair.Basic.ConvergentPair → Prop
  | [] => True
  | candidate :: remaining =>
      RespectsCandidate source reference candidate ∧
        EveryCandidateRespects source reference remaining

/-- Decide the comparison conjunction by structural recursion over the retained finite list. -/
instance everyCandidateRespectsDecidable
    (source : GaussianInt.Fraction) (reference : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
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

/-- Extract the comparison certificate for a member of the checked candidate list. -/
theorem EveryCandidateRespects.of_mem
    {source : GaussianInt.Fraction} {reference candidate : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
    (every : EveryCandidateRespects source reference list)
    (member : candidate ∈ list) :
    RespectsCandidate source reference candidate := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change RespectsCandidate source reference head ∧
        EveryCandidateRespects source reference remaining at every
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · subst candidate
        exact every.1
      · exact inductionHypothesis every.2 tailMember

/-- Assemble the structural comparison conjunction from certificates for every original list member. -/
theorem everyCandidateRespects_of_forall
    {source : GaussianInt.Fraction} {reference : GaussianInt.Pair.Basic.ConvergentPair} {list : List
      GaussianInt.Pair.Basic.ConvergentPair}
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
@[expose] def PassesBestTest (source : GaussianInt.Fraction)
  (reference : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  reference.denominator ≠ 0 ∧
    Best.Error.denominatorQuadrance reference ≤ GaussianInt.normNat source.denominator ∧
    Best.Error.errorQuadrance source.value reference ≤ 1 / 2 ∧
    EveryCandidateRespects source reference (candidates source)

/-- Decide the source cutoffs and complete finite comparison test. -/
instance passesBestTestDecidable (source : GaussianInt.Fraction)
  (reference : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (PassesBestTest source reference) := by
  unfold PassesBestTest
  infer_instance

/-- The bounded executable test is extensionally exact: it accepts precisely
the best approximations quantified over all displayed Gaussian-integer
pairs. -/
theorem passesBestTest_iff_isBest (source : GaussianInt.Fraction)
  (reference : GaussianInt.Pair.Basic.ConvergentPair) :
    PassesBestTest source reference ↔ Best.Basic.IsBest source.value reference := by
  constructor
  · intro passes
    refine ⟨passes.1, ?_, ?_⟩
    · intro competitor competitorNonzero denominatorSmaller
      apply lt_of_not_ge
      intro competitorLe
      have competitorDenominatorBounded :
          Best.Error.denominatorQuadrance competitor ≤ GaussianInt.normNat source.denominator :=
        denominatorSmaller.le.trans passes.2.1
      have competitorSmallError :
          Best.Error.errorQuadrance source.value competitor ≤ 1 / 2 :=
        competitorLe.trans passes.2.2.1
      have member := mem_candidates_of_bounds competitorDenominatorBounded
        competitorSmallError
      have respects := Best.Search.EveryCandidateRespects.of_mem passes.2.2.2 member
      exact (not_lt_of_ge competitorLe
        (respects.1 competitorNonzero denominatorSmaller)).elim
    · intro competitor competitorNonzero denominatorNoLarger
      by_cases referenceLe :
          Best.Error.errorQuadrance source.value reference ≤
            Best.Error.errorQuadrance source.value competitor
      · exact referenceLe
      · have competitorLt := lt_of_not_ge referenceLe
        have competitorDenominatorBounded :
            Best.Error.denominatorQuadrance competitor ≤ GaussianInt.normNat source.denominator :=
          denominatorNoLarger.trans passes.2.1
        have competitorSmallError :
            Best.Error.errorQuadrance source.value competitor ≤ 1 / 2 :=
          competitorLt.le.trans passes.2.2.1
        have member := mem_candidates_of_bounds competitorDenominatorBounded
          competitorSmallError
        have respects := Best.Search.EveryCandidateRespects.of_mem passes.2.2.2 member
        exact respects.2 competitorNonzero denominatorNoLarger
  · intro best
    refine ⟨best.1, Best.Search.IsBest.denominatorQuadrance_le_source best,
      best.errorQuadrance_le_half, ?_⟩
    apply everyCandidateRespects_of_forall
    intro candidate _
    exact ⟨best.2.1 candidate, best.2.2 candidate⟩

/-- Retain exactly the records carrying a successful finite best test. -/
@[expose] def retainPassing (source : GaussianInt.Fraction) : List
  GaussianInt.Pair.Basic.ConvergentPair → List GaussianInt.Pair.Basic.ConvergentPair
  | [] => []
  | candidate :: remaining =>
      if PassesBestTest source candidate then
        candidate :: retainPassing source remaining
      else
        retainPassing source remaining

/-- The retained list contains exactly the original entries that pass the finite best test. -/
theorem mem_retainPassing_iff
    (source : GaussianInt.Fraction) (pair : GaussianInt.Pair.Basic.ConvergentPair) (list : List
      GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ retainPassing source list ↔
      pair ∈ list ∧ PassesBestTest source pair := by
  induction list with
  | nil =>
      exact ⟨fun member => (List.not_mem_nil member).elim,
        fun selected => (List.not_mem_nil selected.1).elim⟩
  | cons head remaining inductionHypothesis =>
      by_cases headPasses : PassesBestTest source head
      · rw [retainPassing, if_pos headPasses]
        constructor
        · intro member
          rcases List.Membership.mem_cons.mp member with equal | tailMember
          · subst pair
            exact ⟨List.Membership.mem_cons.mpr (Or.inl rfl), headPasses⟩
          · have selected := inductionHypothesis.mp tailMember
            exact ⟨List.Membership.mem_cons.mpr (Or.inr selected.1), selected.2⟩
        · intro selected
          rcases List.Membership.mem_cons.mp selected.1 with equal | tailMember
          · exact List.Membership.mem_cons.mpr (Or.inl equal)
          · exact List.Membership.mem_cons.mpr
              (Or.inr (inductionHypothesis.mpr ⟨tailMember, selected.2⟩))
      · rw [retainPassing, if_neg headPasses]
        constructor
        · intro member
          have selected := inductionHypothesis.mp member
          exact ⟨List.Membership.mem_cons.mpr (Or.inr selected.1), selected.2⟩
        · intro selected
          rcases List.Membership.mem_cons.mp selected.1 with equal | tailMember
          · subst pair
            exact (headPasses selected.2).elim
          · exact inductionHypothesis.mpr ⟨tailMember, selected.2⟩

/-- Execute the finite search returning all and only the best approximation
pairs for a displayed rational source. -/
@[expose] def allBest (source : GaussianInt.Fraction) : List
  GaussianInt.Pair.Basic.ConvergentPair :=
  retainPassing source (candidates source)

/-- Filtering by the finite best test cannot increase the original list length. -/
theorem retainPassing_length_le
    (source : GaussianInt.Fraction) (list : List GaussianInt.Pair.Basic.ConvergentPair) :
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
theorem allBest_length_le (source : GaussianInt.Fraction) :
    (allBest source).length ≤
      16 * Nat.pow (GaussianInt.normNat source.denominator + 1) 2 *
        Nat.pow (numeratorQuadranceBound source + 1) 2 := by
  exact (retainPassing_length_le source (candidates source)).trans_eq
    (candidates_length source)

/-- Soundness and completeness of the finite all-best algorithm. -/
theorem mem_allBest_iff_isBest (source : GaussianInt.Fraction)
  (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ allBest source ↔ Best.Basic.IsBest source.value pair := by
  constructor
  · intro member
    have selected := (mem_retainPassing_iff source pair _).mp member
    exact (passesBestTest_iff_isBest source pair).mp selected.2
  · intro best
    exact (mem_retainPassing_iff source pair _).mpr
      ⟨Best.Search.IsBest.mem_candidates best,
        (passesBestTest_iff_isBest source pair).mpr best⟩

/-! ## Constructive descent to a best pair -/

/-- Lexicographic comparison used for finite descent: first minimize error
quadrance, then minimize denominator quadrance among exact error ties. -/
@[expose] def RankLE (source : Gaussian.Basic.Canonical) (left
  right : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Error.errorQuadrance source left < Best.Error.errorQuadrance source right ∨
    (Best.Error.errorQuadrance source left = Best.Error.errorQuadrance source right ∧
      Best.Error.denominatorQuadrance left ≤ Best.Error.denominatorQuadrance right)

/-- Decide the error-first, denominator-second ordering of two retained pairs. -/
instance rankLEDecidable (source : Gaussian.Basic.Canonical) (left
  right : GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (RankLE source left right) := by
  unfold RankLE
  infer_instance

/-- Every pair is weakly ranked before itself. -/
theorem rankLE_refl (source : Gaussian.Basic.Canonical) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) :
    RankLE source pair pair :=
  Or.inr ⟨rfl, le_rfl⟩

/-- The lexicographic rank comparison implies weak comparison of error quadrances. -/
theorem RankLE.errorQuadrance_le
    {source : Gaussian.Basic.Canonical} {left right : GaussianInt.Pair.Basic.ConvergentPair}
    (ranked : RankLE source left right) :
    Best.Error.errorQuadrance source left ≤ Best.Error.errorQuadrance source right := by
  rcases ranked with strict | tied
  · exact strict.le
  · exact tied.1.le

/-- The error-first, denominator-second ordering is transitive. -/
theorem RankLE.trans
    {source : Gaussian.Basic.Canonical} {first second third : GaussianInt.Pair.Basic.ConvergentPair}
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

/-- Every two pairs can be compared by error and then by denominator quadrance. -/
theorem rankLE_total (source : Gaussian.Basic.Canonical) (left
  right : GaussianInt.Pair.Basic.ConvergentPair) :
    RankLE source left right ∨ RankLE source right left := by
  by_cases leftStrict :
      Best.Error.errorQuadrance source left < Best.Error.errorQuadrance source right
  · exact Or.inl (Or.inl leftStrict)
  · by_cases rightStrict :
        Best.Error.errorQuadrance source right < Best.Error.errorQuadrance source left
    · exact Or.inr (Or.inl rightStrict)
    · have errorEqual :
          Best.Error.errorQuadrance source left = Best.Error.errorQuadrance source right :=
        le_antisymm (le_of_not_gt rightStrict) (le_of_not_gt leftStrict)
      rcases Nat.le_total (Best.Error.denominatorQuadrance left)
          (Best.Error.denominatorQuadrance right) with leftLe | rightLe
      · exact Or.inl (Or.inr ⟨errorEqual, leftLe⟩)
      · exact Or.inr (Or.inr ⟨errorEqual.symm, rightLe⟩)

/-- Return a lexicographically least pair from a finite list, or `none` for
the empty list.  Ties retain the earlier displayed record. -/
@[expose] def selectRankMinimum (source :
  Gaussian.Basic.Canonical) : List GaussianInt.Pair.Basic.ConvergentPair → Option GaussianInt.Pair.Basic.ConvergentPair
  | [] => none
  | candidate :: remaining =>
      match selectRankMinimum source remaining with
      | none => some candidate
      | some selected =>
          if RankLE source candidate selected then some candidate
          else some selected

/-- A successful minimum selection returns an entry of the original finite list. -/
theorem selectRankMinimum_mem
    {source : Gaussian.Basic.Canonical} {list : List GaussianInt.Pair.Basic.ConvergentPair} {selected :
      GaussianInt.Pair.Basic.ConvergentPair}
    (selection : selectRankMinimum source list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [selectRankMinimum, -eq_self, -iff_self] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectRankMinimum, -eq_self, -iff_self] at selection
      cases recursive : selectRankMinimum source remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe : RankLE source candidate recursiveSelected
          · simp only [recursive, if_pos candidateLe, -eq_self, -iff_self] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe, -eq_self, -iff_self] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

/-- The minimum selector returns no pair exactly when its input list is empty. -/
theorem selectRankMinimum_eq_none_iff
    (source : Gaussian.Basic.Canonical) (list : List GaussianInt.Pair.Basic.ConvergentPair) :
    selectRankMinimum source list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectRankMinimum, -eq_self, -iff_self] at impossible
        cases recursive : selectRankMinimum source remaining with
        | none =>
            simp only [recursive, -eq_self, -iff_self] at impossible
            cases impossible
        | some selected =>
            by_cases candidateLe : RankLE source candidate selected
            · simp only [recursive, if_pos candidateLe, -eq_self, -iff_self] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe, -eq_self, -iff_self] at impossible
              cases impossible
      · intro impossible
        cases impossible

/-- A selected minimum is ranked no later than any original list member. -/
theorem selectRankMinimum_le_of_mem
    {source : Gaussian.Basic.Canonical} {list : List GaussianInt.Pair.Basic.ConvergentPair} {selected candidate :
      GaussianInt.Pair.Basic.ConvergentPair}
    (selection : selectRankMinimum source list = some selected)
    (member : candidate ∈ list) :
    RankLE source selected candidate := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [selectRankMinimum, -eq_self, -iff_self] at selection
      cases recursive : selectRankMinimum source remaining with
      | none =>
          have remainingEmpty :=
            (selectRankMinimum_eq_none_iff source remaining).mp recursive
          subst remaining
          simp only [selectRankMinimum, -eq_self, -iff_self] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          have singletonIdentity := List.Membership.mem_singleton.mp member
          clear member
          have member := singletonIdentity
          subst candidate
          exact rankLE_refl source head
      | some recursiveSelected =>
          by_cases headLe : RankLE source head recursiveSelected
          · simp only [recursive, if_pos headLe, -eq_self, -iff_self] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact rankLE_refl source head
            · exact headLe.trans
                (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe, -eq_self, -iff_self] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              rcases rankLE_total source head recursiveSelected with
                impossible | recursiveLe
              · exact (headLe impossible).elim
              · exact recursiveLe
            · exact inductionHypothesis recursive remainingMember

/-- Eligibility for the finite descent search below a supplied denominator
quadrance. -/
@[expose] def HeightEligible (bound : Nat) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  pair.denominator ≠ 0 ∧ Best.Error.denominatorQuadrance pair ≤ bound

/-- Decide denominator nonvanishing and the supplied finite height cutoff. -/
instance heightEligibleDecidable (bound : Nat) (pair :
  GaussianInt.Pair.Basic.ConvergentPair) :
    Decidable (HeightEligible bound pair) := by
  unfold HeightEligible
  infer_instance

/-- The source-bounded candidate rectangle, restricted to nonzero
denominators no higher than `bound`. -/
@[expose] def candidatesAtMost (source : GaussianInt.Fraction)
  (bound : Nat) : List GaussianInt.Pair.Basic.ConvergentPair :=
  (candidates source).filter fun pair => decide (HeightEligible bound pair)

/-- The height-restricted rectangle contains exactly the original candidates with eligible denominators. -/
theorem mem_candidatesAtMost_iff
    (source : GaussianInt.Fraction) (bound : Nat) (pair : GaussianInt.Pair.Basic.ConvergentPair) :
    pair ∈ candidatesAtMost source bound ↔
      pair ∈ candidates source ∧ HeightEligible bound pair := by
  constructor
  · intro member
    have filtered := List.Filter.mem_filter.mp member
    exact ⟨filtered.1, of_decide_eq_true filtered.2⟩
  · intro eligible
    exact List.Filter.mem_filter.mpr ⟨eligible.1, decide_eq_true eligible.2⟩

/-- Every bounded small-error pair constructively descends to a genuine best
pair with no greater denominator and no greater error. -/
theorem exists_best_below_of_small
    {source : GaussianInt.Fraction} {candidate : GaussianInt.Pair.Basic.ConvergentPair}
    (candidateNonzero : candidate.denominator ≠ 0)
    (denominatorBounded :
      Best.Error.denominatorQuadrance candidate ≤ GaussianInt.normNat source.denominator)
    (smallError : Best.Error.errorQuadrance source.value candidate ≤ 1 / 2) :
    ∃ selected : GaussianInt.Pair.Basic.ConvergentPair,
      Best.Basic.IsBest source.value selected ∧
        Best.Error.denominatorQuadrance selected ≤ Best.Error.denominatorQuadrance candidate ∧
        Best.Error.errorQuadrance source.value selected ≤
          Best.Error.errorQuadrance source.value candidate := by
  let bound := Best.Error.denominatorQuadrance candidate
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
          Best.Error.errorQuadrance source.value selected ≤
            Best.Error.errorQuadrance source.value candidate :=
        selectedRanksCandidate.errorQuadrance_le
      have selectedSmall :
          Best.Error.errorQuadrance source.value selected ≤ 1 / 2 :=
        selectedErrorBound.trans smallError
      have selectedBest : Best.Basic.IsBest source.value selected := by
        refine ⟨selectedEligible.1, ?_, ?_⟩
        · intro competitor competitorNonzero denominatorSmaller
          by_cases competitorSmall :
              Best.Error.errorQuadrance source.value competitor ≤ 1 / 2
          · have competitorDenominatorBound :
                Best.Error.denominatorQuadrance competitor ≤
                  GaussianInt.normNat source.denominator :=
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
              Best.Error.errorQuadrance source.value competitor ≤ 1 / 2
          · have competitorDenominatorBound :
                Best.Error.denominatorQuadrance competitor ≤
                  GaussianInt.normNat source.denominator :=
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
end Purelib.NumberTheory.Approximation.Best.Search

end
