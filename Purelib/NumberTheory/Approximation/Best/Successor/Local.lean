module
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Data.List.Append
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Data.Nat.Division
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Divisibility.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Norm.Small
public import Purelib.Data.GaussianInt.Pair.Division
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.NumberTheory.Approximation.Best.Basic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.Search

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Enumeration
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Conjugate
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.GaussianInt.Pair

/-!
# Local finite successors of best Gaussian approximations

This file replaces the existential division in the centered coefficient
coset by an executable coordinate calculation.  It then uses the consecutive
index dichotomy and the no-repeated-index theorem to build a finite successor
search from one adjacent best pair rather than from the full source rectangle.
-/

public section

namespace Purelib.NumberTheory.Approximation.Best.Successor.Local

open Purelib.Data
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation

/-- A source- and state-computed quadrance bound for the trailing coefficient
in either local successor form. -/
@[expose] def trailingCoefficientBound (source : GaussianInt.Fraction) (previous :
  Basic.ConvergentPair) : Nat :=
  4 * (GaussianInt.normNat source.denominator +
    Error.denominatorQuadrance previous)

/-- The quadrance-one and quadrance-two possibilities for the leading local
coefficient. -/
@[expose] def leadingCoefficients : List GaussianInt :=
  [1, -1, GaussianInt.Norm.Small.imaginaryUnit,
    -GaussianInt.Norm.Small.imaginaryUnit,
    ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩]

/-- The source/state-bounded trailing coefficient search. -/
@[expose] def trailingCoefficients (source : GaussianInt.Fraction) (previous : Basic.ConvergentPair) :
    List GaussianInt :=
  GaussianInt.componentSquare (trailingCoefficientBound source previous)

/-- Every Gaussian integer of quadrance one or two occurs among the eight leading coefficients. -/
theorem mem_leadingCoefficients_of_norm_eq_one_or_two
    {coefficient : GaussianInt}
    (coefficientNorm : GaussianInt.normNat coefficient = 1 ∨
      GaussianInt.normNat coefficient = 2) :
    coefficient ∈ leadingCoefficients := by
  rcases coefficientNorm with normOne | normTwo
  · have unit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one normOne
    rcases unit with coefficientCase | coefficientCase | coefficientCase | coefficientCase
    · subst coefficient; exact List.Mem.head _
    · subst coefficient; exact List.Mem.tail _ (List.Mem.head _)
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · have diagonal := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two normTwo
    rcases diagonal with coefficientCase | coefficientCase | coefficientCase | coefficientCase
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
    · subst coefficient; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

/-- A trailing coefficient within the computed quadrance bound occurs in the finite coordinate square. -/
theorem mem_trailingCoefficients_of_norm_le
    {source : GaussianInt.Fraction} {previous : Basic.ConvergentPair} {coefficient : GaussianInt}
    (bounded : GaussianInt.normNat coefficient ≤ trailingCoefficientBound source previous) :
    coefficient ∈ trailingCoefficients source previous := by
  exact GaussianInt.mem_componentSquare_of_normNat_le bounded

/-- Any local coefficient identity whose scale and leading coefficient have
quadrance at most two forces the trailing coefficient into the displayed
source/state bound. -/
theorem trailingCoefficient_norm_le
    {source : GaussianInt.Fraction} {previous current next : Basic.ConvergentPair}
    {scale leftCoefficient rightCoefficient : GaussianInt}
    (currentDenominatorNonzero : current.denominator ≠ 0)
    (nextDenominatorBound :
      Error.denominatorQuadrance next ≤
        GaussianInt.normNat source.denominator)
    (scaleNorm : GaussianInt.normNat scale ≤ 2)
    (leftCoefficientNorm : GaussianInt.normNat leftCoefficient ≤ 2)
    (identity :
      LinearCombination.scalePair scale next =
        LinearCombination.linearCombination previous current
          leftCoefficient rightCoefficient) :
    GaussianInt.normNat rightCoefficient ≤ trailingCoefficientBound source previous := by
  have denominatorIdentity := congrArg
    (fun pair : Basic.ConvergentPair => pair.denominator) identity
  change scale * next.denominator =
    leftCoefficient * previous.denominator +
      rightCoefficient * current.denominator at denominatorIdentity
  have productIdentity :
      rightCoefficient * current.denominator =
        scale * next.denominator - leftCoefficient * previous.denominator := by
    calc
      rightCoefficient * current.denominator =
          (leftCoefficient * previous.denominator +
            rightCoefficient * current.denominator) -
              leftCoefficient * previous.denominator := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.add_re,
            GaussianInt.add_im,
            GaussianInt.sub_re,
            GaussianInt.sub_im,
            GaussianInt.mul_re,
            GaussianInt.mul_im] <;>
          ring1
      _ = scale * next.denominator -
          leftCoefficient * previous.denominator := by
        rw [← denominatorIdentity]
  have productBound :
      GaussianInt.normNat rightCoefficient * GaussianInt.normNat current.denominator ≤
        trailingCoefficientBound source previous := by
    calc
      GaussianInt.normNat rightCoefficient * GaussianInt.normNat current.denominator =
          GaussianInt.normNat (rightCoefficient * current.denominator) :=
        (GaussianInt.normNat_mul _ _).symm
      _ = GaussianInt.normNat
          (scale * next.denominator -
            leftCoefficient * previous.denominator) := by
        rw [productIdentity]
      _ ≤ 2 *
          (GaussianInt.normNat (scale * next.denominator) +
            GaussianInt.normNat (leftCoefficient * previous.denominator)) :=
        by
          rw [GaussianInt.sub_eq_add_neg]
          have retained := GaussianInt.Norm.Bounds.normNat_add_le_two
            (scale * next.denominator) (-(leftCoefficient * previous.denominator))
          rw [GaussianInt.normNat_neg] at retained
          exact retained
      _ = 2 *
          (GaussianInt.normNat scale * Error.denominatorQuadrance next +
            GaussianInt.normNat leftCoefficient *
              Error.denominatorQuadrance previous) := by
        rw [GaussianInt.normNat_mul, GaussianInt.normNat_mul]
        rfl
      _ ≤ 2 *
          (2 * GaussianInt.normNat source.denominator +
            2 * Error.denominatorQuadrance previous) := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add
          (Nat.mul_le_mul scaleNorm nextDenominatorBound)
          (Nat.mul_le_mul_right
            (Error.denominatorQuadrance previous)
            leftCoefficientNorm)
      _ = trailingCoefficientBound source previous := by
        unfold trailingCoefficientBound
        ring1
  have currentNormPositive := GaussianInt.normNat_pos currentDenominatorNonzero
  calc
    GaussianInt.normNat rightCoefficient = GaussianInt.normNat rightCoefficient * 1 :=
      (Nat.mul_one _).symm
    _ ≤ GaussianInt.normNat rightCoefficient * GaussianInt.normNat current.denominator :=
      Nat.mul_le_mul_left _ currentNormPositive
    _ ≤ trailingCoefficientBound source previous := productBound

/-- Integral local successor candidates in the coefficient basis supplied by
the preceding adjacent pair. -/
@[expose] def integralCandidates (source : GaussianInt.Fraction) (previous current :
  Basic.ConvergentPair) :
    List Basic.ConvergentPair :=
  leadingCoefficients.flatMap fun leftCoefficient =>
    (trailingCoefficients source previous).map fun rightCoefficient =>
      LinearCombination.linearCombination previous current
        leftCoefficient rightCoefficient

/-- Centered local successor candidates, computed by exact quadrance-two
division.  When the determinant has quadrance one these are harmless extra
records; exact successor completeness chooses the appropriate branch. -/
@[expose] def centeredCandidates (source : GaussianInt.Fraction) (previous current :
  Basic.ConvergentPair) :
    List Basic.ConvergentPair :=
  let determinantValue :=
    LinearCombination.coefficientDeterminant previous current
  leadingCoefficients.flatMap fun leftCoefficient =>
    (trailingCoefficients source previous).map fun rightCoefficient =>
      Division.dividePairByNormTwo determinantValue
        (LinearCombination.linearCombination previous current
          leftCoefficient rightCoefficient)

/-- Finite local over-enumeration of the next best level from one supplied
adjacent pair. -/
@[expose] def candidates (source : GaussianInt.Fraction) (previous current : Basic.ConvergentPair) :
  List Basic.ConvergentPair :=
  integralCandidates source previous current ++
    centeredCandidates source previous current

/-- An integral combination of retained leading and trailing coefficients is a local candidate. -/
theorem integral_mem_candidates
    {source : GaussianInt.Fraction} {previous current : Basic.ConvergentPair}
    {leftCoefficient rightCoefficient : GaussianInt}
    (leftMember : leftCoefficient ∈ leadingCoefficients)
    (rightMember : rightCoefficient ∈ trailingCoefficients source previous) :
    LinearCombination.linearCombination previous current
        leftCoefficient rightCoefficient ∈
      candidates source previous current := open Purelib in by
  rw [candidates]
  apply List.Membership.mem_append.mpr
  apply Or.inl
  apply Data.List.Flatten.mem_flatMap.mpr
  exact ⟨leftCoefficient, leftMember,
    Data.List.Map.mem_map_of_mem rightMember⟩

/-- The norm-two quotient of a retained coefficient combination is a centered local candidate. -/
theorem centered_mem_candidates
    {source : GaussianInt.Fraction} {previous current : Basic.ConvergentPair}
    {leftCoefficient rightCoefficient : GaussianInt}
    (leftMember : leftCoefficient ∈ leadingCoefficients)
    (rightMember : rightCoefficient ∈ trailingCoefficients source previous) :
    Division.dividePairByNormTwo
        (LinearCombination.coefficientDeterminant previous current)
        (LinearCombination.linearCombination previous current
          leftCoefficient rightCoefficient) ∈
      candidates source previous current := open Purelib in by
  rw [candidates]
  apply List.Membership.mem_append.mpr
  apply Or.inr
  apply Data.List.Flatten.mem_flatMap.mpr
  exact ⟨leftCoefficient, leftMember,
    Data.List.Map.mem_map_of_mem rightMember⟩

/-- Every actual next consecutive best level occurs in the bounded local
candidate list generated from the preceding adjacent pair.  This is the
no-skipped-level completeness theorem for candidate generation. -/
theorem next_mem_candidates
    {source : GaussianInt.Fraction} {previous current next : Basic.ConvergentPair}
    (first : Consecutive.Basic.AreConsecutiveBest
      source.value previous current)
    (second : Consecutive.Basic.AreConsecutiveBest
      source.value current next) :
    next ∈ candidates source previous current := by
  rcases (Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two first) with
    firstIndexOne | firstIndexTwo
  · let determinantValue :=
      LinearCombination.coefficientDeterminant previous current
    let leftCoefficient :=
      GaussianInt.conj determinantValue *
        LinearCombination.coefficientDeterminant next current
    let rightCoefficient :=
      GaussianInt.conj determinantValue *
        LinearCombination.coefficientDeterminant previous next
    have expansion :=
      LinearCombination.linearCombination_cramer_of_index_one
        previous current next firstIndexOne
    have identity :
        next = LinearCombination.linearCombination previous current
          leftCoefficient rightCoefficient := by
      simpa only [determinantValue, leftCoefficient, rightCoefficient] using
        expansion.symm
    have indexIdentity := Division.coefficientIndexQuadrance_eq_of_linearCombination
      previous current next leftCoefficient rightCoefficient identity
    have leftCoefficientNorm :
        GaussianInt.normNat leftCoefficient = 1 ∨ GaussianInt.normNat leftCoefficient = 2 := by
      rcases (Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two second) with
        secondIndexOne | secondIndexTwo
      · left
        rw [firstIndexOne, secondIndexOne] at indexIdentity
        simpa only [Nat.mul_one] using indexIdentity.symm
      · right
        rw [firstIndexOne, secondIndexTwo] at indexIdentity
        simpa only [Nat.mul_one] using indexIdentity.symm
    have leftCoefficientBound : GaussianInt.normNat leftCoefficient ≤ 2 := by
      rcases leftCoefficientNorm with normOne | normTwo
      · rw [normOne]
        decide
      · rw [normTwo]
    have scaledIdentity :
        LinearCombination.scalePair 1 next =
          LinearCombination.linearCombination previous current
            leftCoefficient rightCoefficient := by
      rw [Division.scalePair_one]
      exact identity
    have rightCoefficientBound := trailingCoefficient_norm_le
      first.2.1.1 (Search.IsBest.denominatorQuadrance_le_source second.2.1)
      (show GaussianInt.normNat (1 : GaussianInt) ≤ 2 by decide)
      leftCoefficientBound scaledIdentity
    rw [identity]
    exact integral_mem_candidates
      (mem_leadingCoefficients_of_norm_eq_one_or_two leftCoefficientNorm)
      (mem_trailingCoefficients_of_norm_le rightCoefficientBound)
  · have secondIndexOne :=
      Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second firstIndexTwo
    rcases (Consecutive.Index.AreConsecutiveBest.coefficientSpan_or_centeredCoset first) next with
      integral | centered
    · rcases integral with
        ⟨leftCoefficient, rightCoefficient, identity⟩
      have indexIdentity := Division.coefficientIndexQuadrance_eq_of_linearCombination
        previous current next leftCoefficient rightCoefficient identity
      rw [firstIndexTwo, secondIndexOne] at indexIdentity
      have impossible : ¬ GaussianInt.normNat leftCoefficient * 2 = 1 := by
        cases countIdentity : GaussianInt.normNat leftCoefficient with
        | zero => rw [Nat.zero_mul]; decide
        | succ count =>
            intro productOne
            have lower : 2 ≤ (count + 1) * 2 := Nat.mul_le_mul_right 2 (Nat.zero_lt_succ count)
            rw [productOne] at lower
            exact (by decide : ¬ (2 : Nat) ≤ 1) lower
      exact (impossible indexIdentity.symm).elim
    · let determinantValue :=
        LinearCombination.coefficientDeterminant previous current
      change ∃ leftCoefficient rightCoefficient : GaussianInt,
        ¬ GaussianInt.Divisibility.Basic.Divides determinantValue leftCoefficient ∧
        ¬ GaussianInt.Divisibility.Basic.Divides determinantValue rightCoefficient ∧
        LinearCombination.scalePair determinantValue next =
          LinearCombination.linearCombination previous current
            leftCoefficient rightCoefficient at centered
      rcases centered with
        ⟨leftCoefficient, rightCoefficient, _, _, scaledIdentity⟩
      have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
        simpa only [determinantValue,
          LinearCombination.coefficientIndexQuadrance] using firstIndexTwo
      have indexIdentity :=
        Division.coefficientIndexQuadrance_scale_eq_of_scalePair_eq previous current
          next determinantValue leftCoefficient rightCoefficient
          scaledIdentity
      have leftCoefficientNorm : GaussianInt.normNat leftCoefficient = 1 := by
        rw [determinantNorm, firstIndexTwo, secondIndexOne] at indexIdentity
        have divided := congrArg (fun value : Nat => value / 2) indexIdentity.symm
        rw [Nat.mul_one, Nat.mul_comm (GaussianInt.normNat leftCoefficient) 2,
          Nat.Division.mul_div_cancel_left _ (by decide)] at divided
        exact divided
      have rightCoefficientBound := trailingCoefficient_norm_le
        first.2.1.1 (Search.IsBest.denominatorQuadrance_le_source second.2.1)
        (by rw [determinantNorm])
        (by rw [leftCoefficientNorm]; decide) scaledIdentity
      have candidateIdentity := Division.eq_dividePairByNormTwo_of_scalePair_eq
        determinantValue next
          (LinearCombination.linearCombination previous current
            leftCoefficient rightCoefficient)
          determinantNorm scaledIdentity
      rw [candidateIdentity]
      exact centered_mem_candidates
        (mem_leadingCoefficients_of_norm_eq_one_or_two
          (Or.inl leftCoefficientNorm))
        (mem_trailingCoefficients_of_norm_le rightCoefficientBound)

/-- Select a pair of least denominator quadrance from a finite list.  Ties
retain the earlier displayed record. -/
@[expose] def selectDenominatorMinimum : List Basic.ConvergentPair → Option
  Basic.ConvergentPair
  | [] => none
  | candidate :: remaining =>
      match Local.selectDenominatorMinimum remaining with
      | none => some candidate
      | some selected =>
          if Error.denominatorQuadrance candidate ≤
              Error.denominatorQuadrance selected then
            some candidate
          else
            some selected

/-- A successful denominator-minimum selection returns a member of its input list. -/
theorem selectDenominatorMinimum_mem
    {list : List Basic.ConvergentPair} {selected : Basic.ConvergentPair}
    (selection : selectDenominatorMinimum list = some selected) :
    selected ∈ list := by
  induction list with
  | nil =>
      simp only [selectDenominatorMinimum] at selection
      cases selection
  | cons candidate remaining inductionHypothesis =>
      simp only [selectDenominatorMinimum] at selection
      cases recursive : selectDenominatorMinimum remaining with
      | none =>
          rw [recursive] at selection
          cases selection
          exact List.mem_cons_self
      | some recursiveSelected =>
          by_cases candidateLe :
              Error.denominatorQuadrance candidate ≤
                Error.denominatorQuadrance recursiveSelected
          · simp only [recursive, if_pos candidateLe] at selection
            cases selection
            exact List.mem_cons_self
          · simp only [recursive, if_neg candidateLe] at selection
            cases selection
            exact List.mem_cons_of_mem _ (inductionHypothesis recursive)

/-- The denominator-minimum selector returns no pair exactly for an empty list. -/
theorem selectDenominatorMinimum_eq_none_iff (list : List Basic.ConvergentPair) :
    selectDenominatorMinimum list = none ↔ list = [] := by
  cases list with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons candidate remaining =>
      constructor
      · intro impossible
        simp only [selectDenominatorMinimum] at impossible
        cases recursive : selectDenominatorMinimum remaining with
        | none =>
            simp only [recursive] at impossible
            cases impossible
        | some selected =>
            by_cases candidateLe :
                Error.denominatorQuadrance candidate ≤
                  Error.denominatorQuadrance selected
            · simp only [recursive, if_pos candidateLe] at impossible
              cases impossible
            · simp only [recursive, if_neg candidateLe] at impossible
              cases impossible
      · intro impossible
        cases impossible

/-- The selected denominator quadrance is no greater than that of every input member. -/
theorem selectDenominatorMinimum_le_of_mem
    {list : List Basic.ConvergentPair} {selected candidate : Basic.ConvergentPair}
    (selection : selectDenominatorMinimum list = some selected)
    (member : candidate ∈ list) :
    Error.denominatorQuadrance selected ≤
      Error.denominatorQuadrance candidate := by
  induction list generalizing selected candidate with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      simp only [selectDenominatorMinimum] at selection
      cases recursive : selectDenominatorMinimum remaining with
      | none =>
          have remainingEmpty :=
            (selectDenominatorMinimum_eq_none_iff remaining).mp recursive
          subst remaining
          simp only [selectDenominatorMinimum] at selection
          have selectedIdentity : head = selected := Option.some.inj selection
          subst selected
          have identity := List.Membership.mem_singleton.mp member
          cases identity
          exact Nat.le_refl _
      | some recursiveSelected =>
          by_cases headLe :
              Error.denominatorQuadrance head ≤
                Error.denominatorQuadrance recursiveSelected
          · simp only [recursive, if_pos headLe] at selection
            have selectedIdentity : head = selected := Option.some.inj selection
            subst selected
            rcases List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact Nat.le_refl _
            · exact headLe.trans
                (inductionHypothesis recursive remainingMember)
          · simp only [recursive, if_neg headLe] at selection
            have selectedIdentity : recursiveSelected = selected :=
              Option.some.inj selection
            subst selected
            rcases List.Membership.mem_cons.mp member with headIdentity | remainingMember
            · subst candidate
              exact Nat.le_of_not_ge headLe
            · exact inductionHypothesis recursive remainingMember

/-- Best pairs strictly above a supplied best denominator, drawn from the
proved finite all-best list.  This list appears only in the correctness proof
of the local update, not in the executable local update itself. -/
@[expose] def bestStrictlyAbove (source : GaussianInt.Fraction) (lower : Basic.ConvergentPair) : List
  Basic.ConvergentPair :=
  (Search.allBest source).filter fun pair =>
    decide (Error.denominatorQuadrance lower <
      Error.denominatorQuadrance pair)

/-- The filtered list contains exactly best pairs strictly above the supplied denominator level. -/
theorem mem_bestStrictlyAbove_iff
    (source : GaussianInt.Fraction) (lower pair : Basic.ConvergentPair) :
    pair ∈ bestStrictlyAbove source lower ↔
      Basic.IsBest source.value pair ∧
        Error.denominatorQuadrance lower <
          Error.denominatorQuadrance pair := by
  change pair ∈ (Search.allBest source).filter _ ↔ _
  constructor
  · intro selected
    rcases List.Filter.mem_filter.mp selected with ⟨member, accepted⟩
    exact ⟨(Search.mem_allBest_iff_isBest source pair).mp member, of_decide_eq_true accepted⟩
  · rintro ⟨best, ordered⟩
    exact List.Filter.mem_filter.mpr
      ⟨(Search.mem_allBest_iff_isBest source pair).mpr best, decide_eq_true ordered⟩

/-- A displayed later best pair contains a first occupied best denominator
above `lower`.  The witness is selected from a finite list and therefore uses
neither an infinite well-ordering argument nor choice. -/
theorem exists_consecutiveBest_below
    {source : GaussianInt.Fraction} {lower later : Basic.ConvergentPair}
    (lowerBest : Basic.IsBest source.value lower)
    (laterBest : Basic.IsBest source.value later)
    (ordered : Error.denominatorQuadrance lower <
      Error.denominatorQuadrance later) :
    ∃ next : Basic.ConvergentPair,
      Consecutive.Basic.AreConsecutiveBest source.value lower next ∧
        Error.denominatorQuadrance next ≤
          Error.denominatorQuadrance later := by
  let list := bestStrictlyAbove source lower
  have laterMember : later ∈ list :=
    (mem_bestStrictlyAbove_iff source lower later).mpr
      ⟨laterBest, ordered⟩
  cases selection : selectDenominatorMinimum list with
  | none =>
      have listEmpty := (selectDenominatorMinimum_eq_none_iff list).mp selection
      rw [listEmpty] at laterMember
      exact (List.not_mem_nil laterMember).elim
  | some next =>
      have nextMember := selectDenominatorMinimum_mem selection
      have nextData :=
        (mem_bestStrictlyAbove_iff source lower next).mp nextMember
      have nextNoHigher :=
        selectDenominatorMinimum_le_of_mem selection laterMember
      refine ⟨next, ⟨lowerBest, nextData.1, nextData.2, ?_⟩,
        nextNoHigher⟩
      intro middle middleBest between
      have middleMember : middle ∈ list :=
        (mem_bestStrictlyAbove_iff source lower middle).mpr
          ⟨middleBest, between.1⟩
      have nextLeMiddle :=
        selectDenominatorMinimum_le_of_mem selection middleMember
      exact (Nat.not_le_of_gt between.2) nextLeMiddle

/-- A locally improving record lies strictly above `current`, remains within
the displayed source denominator bound, and has strictly smaller error. -/
@[expose] def IsLocalImprovement (source : GaussianInt.Fraction) (current candidate :
  Basic.ConvergentPair) : Prop :=
  candidate.denominator ≠ 0 ∧
    Error.denominatorQuadrance current <
      Error.denominatorQuadrance candidate ∧
    Error.denominatorQuadrance candidate ≤
      GaussianInt.normNat source.denominator ∧
    Error.errorQuadrance source.value candidate <
      Error.errorQuadrance source.value current

/-- Decide denominator nonzeroness, the source bound and both strict improvement comparisons. -/
instance isLocalImprovementDecidable
    (source : GaussianInt.Fraction) (current candidate : Basic.ConvergentPair) :
    Decidable (IsLocalImprovement source current candidate) := by
  unfold IsLocalImprovement
  infer_instance

/-- One locally generated contender does not precede `reference`; on the
same denominator level it also does not improve upon `reference`. -/
@[expose] def CandidateNotEarlier
    (source : GaussianInt.Fraction) (current reference contender : Basic.ConvergentPair) : Prop :=
  IsLocalImprovement source current contender →
    Error.denominatorQuadrance reference ≤
      Error.denominatorQuadrance contender ∧
    (Error.denominatorQuadrance contender =
        Error.denominatorQuadrance reference →
      Error.errorQuadrance source.value reference ≤
        Error.errorQuadrance source.value contender)

/-- Decide whether an improving contender precedes or improves the reference at its denominator level. -/
instance candidateNotEarlierDecidable
    (source : GaussianInt.Fraction) (current reference contender : Basic.ConvergentPair) :
    Decidable (CandidateNotEarlier source current reference contender) := by
  unfold CandidateNotEarlier
  infer_instance

/-- Finite conjunction of the local no-earlier-candidate comparisons. -/
@[expose] def EveryCandidateNotEarlier
    (source : GaussianInt.Fraction) (current reference : Basic.ConvergentPair) : List
      Basic.ConvergentPair → Prop
  | [] => True
  | contender :: remaining =>
      CandidateNotEarlier source current reference contender ∧
        Local.EveryCandidateNotEarlier source current reference
          remaining

/-- Decide the structural conjunction of local contender comparisons over a finite list. -/
instance everyCandidateNotEarlierDecidable
    (source : GaussianInt.Fraction) (current reference : Basic.ConvergentPair) (list : List
      Basic.ConvergentPair) :
    Decidable (EveryCandidateNotEarlier source current reference list) := by
  induction list with
  | nil =>
      change Decidable True
      infer_instance
  | cons contender remaining inductionHypothesis =>
      letI : Decidable
          (EveryCandidateNotEarlier source current reference remaining) :=
        inductionHypothesis
      change Decidable
        (CandidateNotEarlier source current reference contender ∧
          EveryCandidateNotEarlier source current reference remaining)
      infer_instance

/-- Extract the no-earlier comparison for a member of the certified contender list. -/
theorem EveryCandidateNotEarlier.of_mem
    {source : GaussianInt.Fraction} {current reference contender : Basic.ConvergentPair} {list : List
      Basic.ConvergentPair}
    (every : EveryCandidateNotEarlier source current reference list)
    (member : contender ∈ list) :
    CandidateNotEarlier source current reference contender := by
  induction list with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      change CandidateNotEarlier source current reference head ∧
        EveryCandidateNotEarlier source current reference remaining at every
      rcases List.Membership.mem_cons.mp member with equal | tailMember
      · subst contender
        exact every.1
      · exact inductionHypothesis every.2 tailMember

/-- Build the structural list certificate from one no-earlier comparison for each member. -/
theorem everyCandidateNotEarlier_of_forall
    {source : GaussianInt.Fraction} {current reference : Basic.ConvergentPair} {list : List
      Basic.ConvergentPair}
    (noneEarlier : ∀ contender ∈ list,
      CandidateNotEarlier source current reference contender) :
    EveryCandidateNotEarlier source current reference list := by
  induction list with
  | nil => trivial
  | cons contender remaining inductionHypothesis =>
      exact ⟨noneEarlier contender List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          noneEarlier candidate (List.mem_cons_of_mem _ member))⟩

/-- The wholly coefficient-local successor test.  It compares the proposed
record only with the bounded candidates generated from the adjacent state;
it does not scan the source numerator--denominator rectangle. -/
@[expose] def PassesLocalSuccessorTest
    (source : GaussianInt.Fraction) (previous current candidate : Basic.ConvergentPair) : Prop :=
  IsLocalImprovement source current candidate ∧
    EveryCandidateNotEarlier source current candidate
      (candidates source previous current)

/-- Decide the proposed improvement and its comparisons with every generated local contender. -/
instance passesLocalSuccessorTestDecidable
    (source : GaussianInt.Fraction) (previous current candidate : Basic.ConvergentPair) :
    Decidable (PassesLocalSuccessorTest source previous current candidate) := by
  unfold PassesLocalSuccessorTest
  infer_instance

/-- An actual next best level passes the coefficient-local test. -/
theorem passesLocalSuccessorTest_of_consecutive
    {source : GaussianInt.Fraction} {previous current next : Basic.ConvergentPair}
    (first : Consecutive.Basic.AreConsecutiveBest
      source.value previous current)
    (second : Consecutive.Basic.AreConsecutiveBest
      source.value current next) :
    PassesLocalSuccessorTest source previous current next := by
  have nextImproves : IsLocalImprovement source current next :=
    ⟨second.2.1.1, second.2.2.1,
      (Search.IsBest.denominatorQuadrance_le_source second.2.1),
      second.2.1.2.1 current first.2.1.1 second.2.2.1⟩
  refine ⟨nextImproves, ?_⟩
  apply everyCandidateNotEarlier_of_forall
  intro contender _ contenderImproves
  have cylinderEmpty :=
    (Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty
      source current next).mp second |>.2.2.2
  have nextNoHigher :
      Error.denominatorQuadrance next ≤
        Error.denominatorQuadrance contender := by
    apply Nat.le_of_not_gt
    intro contenderEarlier
    exact cylinderEmpty contender (Or.inr contenderImproves.1)
      ⟨contenderImproves.2.2.2, contenderEarlier⟩
  refine ⟨nextNoHigher, ?_⟩
  intro sameHeight
  exact second.2.1.2.2 contender contenderImproves.1 sameHeight.le

/-- Bestness is invariant under replacing a displayed record by another
record at exactly the same denominator and error quadrances. -/
theorem isBest_of_same_quadrances
    {source : Gaussian.Basic.Canonical} {best tied : Basic.ConvergentPair}
    (bestness : Basic.IsBest source best)
    (tiedDenominatorNonzero : tied.denominator ≠ 0)
    (sameDenominator :
      Error.denominatorQuadrance tied =
        Error.denominatorQuadrance best)
    (sameError : Error.errorQuadrance source tied =
      Error.errorQuadrance source best) :
    Basic.IsBest source tied := by
  refine ⟨tiedDenominatorNonzero, ?_, ?_⟩
  · intro competitor competitorNonzero denominatorSmaller
    rw [sameDenominator] at denominatorSmaller
    rw [sameError]
    exact bestness.2.1 competitor competitorNonzero denominatorSmaller
  · intro competitor competitorNonzero denominatorNoLarger
    rw [sameDenominator] at denominatorNoLarger
    rw [sameError]
    exact bestness.2.2 competitor competitorNonzero denominatorNoLarger

/-- Passing the coefficient-local test is sound whenever the supplied state
is one adjacent best pair. -/
theorem consecutive_of_passesLocalSuccessorTest
    {source : GaussianInt.Fraction} {previous current candidate : Basic.ConvergentPair}
    (first : Consecutive.Basic.AreConsecutiveBest
      source.value previous current)
    (passes : PassesLocalSuccessorTest source previous current candidate) :
    Consecutive.Basic.AreConsecutiveBest
      source.value current candidate := by
  obtain ⟨later, laterBest, laterNoHigher, laterErrorNoLarger⟩ :=
    Search.exists_best_below_of_small passes.1.1
      passes.1.2.2.1
      (passes.1.2.2.2.le.trans (Basic.IsBest.errorQuadrance_le_half first.2.1))
  have currentBelowLater :
      Error.denominatorQuadrance current <
        Error.denominatorQuadrance later := by
    apply Nat.lt_of_not_ge
    intro laterNoHigherThanCurrent
    have currentErrorNoLarger := first.2.1.2.2 later laterBest.1
      laterNoHigherThanCurrent
    exact (not_lt_of_ge (currentErrorNoLarger.trans laterErrorNoLarger))
      passes.1.2.2.2
  obtain ⟨next, second, nextNoHigher⟩ :=
    exists_consecutiveBest_below first.2.1 laterBest currentBelowLater
  have nextMember := next_mem_candidates first second
  have nextImproves : IsLocalImprovement source current next :=
    ⟨second.2.1.1, second.2.2.1,
      (Search.IsBest.denominatorQuadrance_le_source second.2.1),
      second.2.1.2.1 current first.2.1.1 second.2.2.1⟩
  have candidateNoHigher :=
    (EveryCandidateNotEarlier.of_mem passes.2 nextMember nextImproves).1
  have nextNoHigherThanCandidate :
      Error.denominatorQuadrance next ≤
        Error.denominatorQuadrance candidate :=
    nextNoHigher.trans laterNoHigher
  have sameDenominator :
      Error.denominatorQuadrance candidate =
        Error.denominatorQuadrance next :=
    Nat.le_antisymm candidateNoHigher nextNoHigherThanCandidate
  have candidateErrorNoLarger :
      Error.errorQuadrance source.value candidate ≤
        Error.errorQuadrance source.value next :=
    (EveryCandidateNotEarlier.of_mem passes.2 nextMember nextImproves).2
      sameDenominator.symm
  have nextErrorNoLarger :
      Error.errorQuadrance source.value next ≤
        Error.errorQuadrance source.value candidate :=
    second.2.1.2.2 candidate passes.1.1 sameDenominator.le
  have sameError :
      Error.errorQuadrance source.value candidate =
        Error.errorQuadrance source.value next :=
    le_antisymm candidateErrorNoLarger nextErrorNoLarger
  have candidateBest := isBest_of_same_quadrances second.2.1 passes.1.1
    sameDenominator sameError
  refine ⟨first.2.1, candidateBest, ?_, ?_⟩
  · rw [sameDenominator]
    exact second.2.2.1
  · intro middle middleBest between
    apply second.2.2.2 middle middleBest
    rw [sameDenominator] at between
    exact between

/-- Exact logical specification of the coefficient-local validation test,
assuming the supplied state is one adjacent best pair. -/
theorem passesLocalSuccessorTest_iff
    {source : GaussianInt.Fraction} {previous current candidate : Basic.ConvergentPair}
    (first : Consecutive.Basic.AreConsecutiveBest
      source.value previous current) :
    PassesLocalSuccessorTest source previous current candidate ↔
      Consecutive.Basic.AreConsecutiveBest
        source.value current candidate := by
  constructor
  · exact consecutive_of_passesLocalSuccessorTest first
  · exact passesLocalSuccessorTest_of_consecutive first

/-- Execute only the coefficient-local comparisons on the locally generated
candidate list. -/
@[expose] def successors (source : GaussianInt.Fraction) (previous current : Basic.ConvergentPair) :
  List Basic.ConvergentPair :=
  (candidates source previous current).filter fun candidate =>
    decide (PassesLocalSuccessorTest source previous current candidate)

/-- Exactness of the local successor calculation, assuming the supplied
state really is one adjacent best pair.  Both candidate generation and
validation use only the bounded coefficient list derived from that state. -/
theorem mem_successors_iff
    {source : GaussianInt.Fraction} {previous current : Basic.ConvergentPair}
    (first : Consecutive.Basic.AreConsecutiveBest
      source.value previous current)
    (candidate : Basic.ConvergentPair) :
    candidate ∈ successors source previous current ↔
      Consecutive.Basic.AreConsecutiveBest
        source.value current candidate := by
  change candidate ∈ (candidates source previous current).filter _ ↔ _
  constructor
  · intro selected
    exact consecutive_of_passesLocalSuccessorTest first (of_decide_eq_true
      (List.Filter.mem_filter.mp selected).2)
  · intro consecutive
    exact List.Filter.mem_filter.mpr
      ⟨next_mem_candidates first consecutive,
        decide_eq_true (passesLocalSuccessorTest_of_consecutive first consecutive)⟩

/-- The finite leading-coefficient list has eight entries. -/
theorem leadingCoefficients_length : leadingCoefficients.length = 8 := rfl

/-- The locally generated candidate list has a quadratic coefficient-space
bound.  It avoids the source numerator bound used by the global rectangle. -/
theorem candidates_length_le (source : GaussianInt.Fraction) (previous current : Basic.ConvergentPair)
  :
    (candidates source previous current).length ≤
      64 * (trailingCoefficientBound source previous + 1) ^ 2 := by
  have trailingLength :
      (trailingCoefficients source previous).length =
        4 * (trailingCoefficientBound source previous + 1) ^ 2 := by
    rw [trailingCoefficients, GaussianInt.componentSquare_length]
    rfl
  have integralLength :
      (integralCandidates source previous current).length =
        leadingCoefficients.length *
          (trailingCoefficients source previous).length := by
    rw [integralCandidates, List.Flatten.length_flatMap_map]
  have centeredLength :
      (centeredCandidates source previous current).length =
        leadingCoefficients.length *
          (trailingCoefficients source previous).length := by
    rw [centeredCandidates]
    exact List.Flatten.length_flatMap_map _ _ _
  rw [candidates, List.Append.length_append, integralLength, centeredLength,
    trailingLength]
  rw [leadingCoefficients_length]
  calc
    8 *
          (4 * (trailingCoefficientBound source previous + 1) ^ 2) +
        8 *
          (4 * (trailingCoefficientBound source previous + 1) ^ 2) =
        64 * (trailingCoefficientBound source previous + 1) ^ 2 := by
      ring1
    _ ≤ 64 * (trailingCoefficientBound source previous + 1) ^ 2 := Nat.le_refl _

end Purelib.NumberTheory.Approximation.Best.Successor.Local
