module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

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

namespace Purelib.NumberTheory.Approximation.Best.Basic

/-- Chevallier's two-tier best-approximation condition, expressed with exact
quadrances.  Smaller nonzero denominators require strict improvement; at an
equal or smaller denominator the candidate may only tie the reference. -/
def IsBest (source : Gaussian.Basic.Canonical) (reference :
  GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  reference.denominator ≠ 0 ∧
    (∀ competitor : GaussianInt.Pair.Basic.ConvergentPair, competitor.denominator ≠ 0 →
      Best.Error.denominatorQuadrance competitor < Best.Error.denominatorQuadrance reference →
      Best.Error.errorQuadrance source reference < Best.Error.errorQuadrance source competitor) ∧
    (∀ competitor : GaussianInt.Pair.Basic.ConvergentPair, competitor.denominator ≠ 0 →
      Best.Error.denominatorQuadrance competitor ≤ Best.Error.denominatorQuadrance reference →
      Best.Error.errorQuadrance source reference ≤ Best.Error.errorQuadrance source competitor)

/-- The weaker lower-height condition proved unconditionally by the finite
Hurwitz--Lakein theorem. -/
def IsWeakLowerBest (source : Gaussian.Basic.Canonical) (reference
  : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ competitor : GaussianInt.Pair.Basic.ConvergentPair, competitor.denominator ≠ 0 →
      Best.Error.denominatorQuadrance competitor < Best.Error.denominatorQuadrance reference →
      Best.Error.errorQuadrance source reference ≤ Best.Error.errorQuadrance source competitor

/-- Membership in the closed coordinate cylinder determined by `reference`.
This is the square-root-free form of the product of the two closed discs used
in the Gaussian-lattice definition. -/
def InClosedCylinder (source : Gaussian.Basic.Canonical) (reference
  candidate : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Error.errorQuadrance source candidate ≤ Best.Error.errorQuadrance source reference ∧
    Best.Error.denominatorQuadrance candidate ≤ Best.Error.denominatorQuadrance reference

/-- A candidate lies on both coordinate boundaries of the reference
cylinder. -/
def OnCylinderBoundary (source : Gaussian.Basic.Canonical)
    (reference candidate : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Error.errorQuadrance source candidate = Best.Error.errorQuadrance source reference ∧
    Best.Error.denominatorQuadrance candidate = Best.Error.denominatorQuadrance reference

/-- Minimality of the displayed vector `(qz-p,q)` in the source lattice.
The nonzero-second-coordinate clause is the `q \ne 0` side condition in the
best-approximation correspondence. -/
def IsGaussLatticeMinimal (source : Gaussian.Basic.Canonical)
  (reference : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ candidate : GaussianInt.Pair.Basic.ConvergentPair, GaussianInt.Pair.LinearCombination.PairNonzero candidate →
      InClosedCylinder source reference candidate →
      OnCylinderBoundary source reference candidate

namespace IsBest

/-- A best approximation satisfies the weak comparison used by the finite
Hurwitz--Lakein theorem. -/
theorem isWeakLowerBest {source : Gaussian.Basic.Canonical}
  {reference : GaussianInt.Pair.Basic.ConvergentPair}
    (best : IsBest source reference) : IsWeakLowerBest source reference := by
  refine ⟨best.1, ?_⟩
  intro competitor competitorNonzero denominatorSmaller
  exact (best.2.1 competitor competitorNonzero denominatorSmaller).le

end IsBest
/-- Restrict lattice minimality to candidates with nonzero denominators. -/
def IsDenominatorMinimal (source : Gaussian.Basic.Canonical)
  (reference : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  reference.denominator ≠ 0 ∧
    ∀ candidate : GaussianInt.Pair.Basic.ConvergentPair, candidate.denominator ≠ 0 →
      InClosedCylinder source reference candidate →
      OnCylinderBoundary source reference candidate

/-- Best approximation is equivalent to minimality in the closed cylinder among nonzero-denominator pairs.

The strict comparison at smaller denominator height and weak comparison at equal height force both boundary equalities.
-/
theorem isBest_iff_isDenominatorMinimal
    (source : Gaussian.Basic.Canonical) (reference : GaussianInt.Pair.Basic.ConvergentPair) :
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
def nearestPair (source : Gaussian.Basic.Canonical) (denominator :
  GaussianInt) : GaussianInt.Pair.Basic.ConvergentPair :=
  { numerator := GaussianInt.Nearest.nearest
      (source * GaussianInt.toGaussian denominator)
    denominator := denominator }

/-- Choosing the nearest numerator preserves the supplied denominator. -/
@[simp] theorem nearestPair_denominator
    (source : Gaussian.Basic.Canonical) (denominator : GaussianInt) :
    (nearestPair source denominator).denominator = denominator := rfl

/-- The nearest-numerator pair has exactly the nearest Gaussian-integer remainder as its error. -/
theorem nearestPair_error (source : Gaussian.Basic.Canonical)
  (denominator : GaussianInt) :
    Best.Error.error source (nearestPair source denominator) =
      GaussianInt.Nearest.remainder (source * GaussianInt.toGaussian denominator) := rfl

namespace IsBest

/-- The equal-height clause forces every best approximation into the usual
nearest-integer error cylinder. -/
theorem errorQuadrance_le_half
    {source : Gaussian.Basic.Canonical} {reference : GaussianInt.Pair.Basic.ConvergentPair} (best : IsBest
      source reference) :
    Best.Error.errorQuadrance source reference ≤ 1 / 2 := by
  calc
    Best.Error.errorQuadrance source reference ≤
        Best.Error.errorQuadrance source (Best.Basic.nearestPair source reference.denominator) :=
      best.2.2 (Best.Basic.nearestPair source reference.denominator) best.1 le_rfl
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.Nearest.remainder
          (source * GaussianInt.toGaussian reference.denominator)) := by
      rw [Best.Error.errorQuadrance, Best.Basic.nearestPair_error]
    _ ≤ 1 / 2 := GaussianInt.Nearest.remainder_normSq_le_half _

end IsBest
/-- A nonzero numerator with zero denominator has error quadrance at least one. -/
public theorem one_le_errorQuadrance_of_vertical
    (source : Gaussian.Basic.Canonical) {candidate : GaussianInt.Pair.Basic.ConvergentPair}
    (numeratorNonzero : candidate.numerator ≠ 0)
    (denominatorZero : candidate.denominator = 0) :
    (1 : Fraction.Rational) ≤ Best.Error.errorQuadrance source candidate := by
  have oneLeNorm : 1 ≤ GaussianInt.normNat candidate.numerator :=
    GaussianInt.normNat_pos numeratorNonzero
  have castBound : (1 : Fraction.Rational) ≤ (GaussianInt.normNat candidate.numerator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct oneLeNorm
  rw [Best.Error.errorQuadrance, Best.Error.error, denominatorZero, GaussianInt.toGaussian_zero,
    Gaussian.Basic.mul_zero]
  rw [_root_.zero_sub, Gaussian.Norm.Basic.normSq_neg, GaussianInt.normSq_toGaussian]
  exact castBound

/-- The exact finite analogue of the minimal-vector/best-approximation
correspondence: a displayed pair is best precisely when its source-lattice
vector is minimal in the closed product cylinder and has nonzero second
coordinate. -/
theorem isBest_iff_isGaussLatticeMinimal
    (source : Gaussian.Basic.Canonical) (reference : GaussianInt.Pair.Basic.ConvergentPair) :
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
      have impossible : (1 : Fraction.Rational) ≤ 1 / 2 :=
        oneLeCandidate.trans (inside.1.trans referenceLeHalf)
      exact ((show ¬ ((1 : Fraction.Rational) ≤ 1 / 2) by decide) impossible).elim
  · intro minimal
    apply (isBest_iff_isDenominatorMinimal source reference).mpr
    refine ⟨minimal.1, ?_⟩
    intro candidate candidateNonzero inside
    exact minimal.2 candidate (Or.inr candidateNonzero) inside
end Purelib.NumberTheory.Approximation.Best.Basic

end
