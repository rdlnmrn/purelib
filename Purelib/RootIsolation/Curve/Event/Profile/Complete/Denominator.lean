module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Classification
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Sign
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Rational.Factorization (ConditionRelation)
open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentProfileRequestFamilyProfileAnalysisAlias)
open Purelib.RootIsolation.Curve.Event.Profile.Basic
  (ProfileEventLeaf
   SourcePersistentProfileRequestFamilyProfileEventLeafAlias)
open Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic (CompleteRequestLeaf)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Complete
section Profile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
  Geometry.Projective.Hermitian.HermitianForm}
variable {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
variable {data : Curve.Event.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box
  chart data
  gcdDegreePositive}
variable {analysis : SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}

/-! ## Explicit denominator relation of every final profile -/

set_option genInjectivity false in
/-- The first retained profile relation is the homogeneous curve-denominator
quadrance.  Keeping its membership proof makes the pole/apart split available
without searching an unbounded carrier. -/
structure Denominator.ProfileDenominatorRelation
    (analysis : SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis) where
  /-- The exact equality or apart relation of the curve-denominator quadrance to the original profile factor. -/
    relation : ConditionRelation
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve)
    analysis.profile.factor
  /-- The retained denominator relation belongs to the original aligned profile-relation list. -/ member :
    (⟨Curve.Coordinates.denominatorNormSq
        chart.parameterization.curve, relation⟩ :
      Curve.Event.Profile.Classification.ProfileRelation
        analysis) ∈ analysis.profile.relations

constructive_injectivity Denominator.ProfileDenominatorRelation

/-- Recover the denominator relation from the exact finite list-alignment
certificate. -/
@[expose] def Denominator.profileDenominatorRelation
    (analysis : SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis) :
    Denominator.ProfileDenominatorRelation analysis := by
  cases relationsEq : analysis.profile.relations with
  | nil =>
      have aligned := analysis.profile.conditions_eq
      rw [relationsEq] at aligned
      simp only [-eq_self, -iff_self, List.map_nil,
        Curve.Box.profiledConditionPolynomials]
        at aligned
      cases aligned
  | cons head tail =>
      rcases head with ⟨condition, relation⟩
      have aligned := analysis.profile.conditions_eq
      rw [relationsEq] at aligned
      simp only [-eq_self, -iff_self, List.map_cons,
        Curve.Box.profiledConditionPolynomials]
        at aligned
      have conditionEq := (List.cons.inj aligned).1
      subst condition
      exact
        { relation := relation
          member := by rw [relationsEq]; exact List.mem_cons_self }

namespace Denominator.ProfileDenominatorRelation

/-- Positive rational affine-denominator lower bound contributed by an apart
denominator relation.  The minimum with one avoids taking a square root. -/
@[expose] def
  apartLower
    {analysis : SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}
    (_entry : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation analysis)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)) : Fraction.Rational :=
  min 1
    (ProfileEventLeaf.apartConditionLower
      analysis
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)
        apart)

/-- The apart denominator relation supplies a positive rational lower bound. -/
theorem apartLower_pos
    {analysis : SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}
    (entry : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation analysis)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)) :
    0 < entry.apartLower apart :=
  Fraction.Order.Basic.lt_min (by decide)
    (ProfileEventLeaf.apartConditionLower_pos
      analysis
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)
        apart)

end Denominator.ProfileDenominatorRelation

namespace Basic.CompleteRequestLeaf

/-- An apart denominator relation supplies a uniform positive rational lower
bound for the affine denominator quadrance throughout the retained cell. -/
theorem
  denominatorNormSq_lower_of_apart
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation analysis)
    (apart : CoprimeCertificate
      analysis.profile.factor.polynomial
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve))
    (relationEq : denominator.relation =
      ConditionRelation.apart apart)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis)
    (parameter : Fraction.Rational)
    (inside : requestEntry.cell.interval.Contains parameter) :
    denominator.apartLower apart ≤
      Data.Gaussian.Norm.Basic.normSq
        (chart.parameterization.curve.denominatorAt parameter) := by
  have relationMember := denominator.member
  rw [relationEq] at relationMember
  have epsilonLeApart : epsilon ≤
      ProfileEventLeaf.apartSignWidth
        analysis
          (Curve.Coordinates.denominatorNormSq
            chart.parameterization.curve)
          apart :=
    epsilonLe.trans
      (Curve.Event.Profile.Sign.profileSignWidth_le_apart
        analysis
          (Curve.Coordinates.denominatorNormSq
            chart.parameterization.curve)
          apart relationMember)
  have squareLower := requestEntry.apartConditionLower_lt_eval_sq
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve)
    apart positive epsilonLeApart parameter inside
  let value := Data.Gaussian.Norm.Basic.normSq
    (chart.parameterization.curve.denominatorAt parameter)
  have lowerLtSquare :
      ProfileEventLeaf.apartConditionLower
          analysis
            (Curve.Coordinates.denominatorNormSq
              chart.parameterization.curve)
            apart < value ^ 2 := by
    simpa only [-eq_self, -iff_self, value,
      Curve.Coordinates.eval_denominatorNormSq] using
      squareLower
  have valueNonnegative : 0 ≤ value :=
    Gaussian.Norm.Basic.normSq_nonneg _
  by_cases oneLe : 1 ≤ value
  · exact (Fraction.Order.Basic.min_le_left _ _).trans oneLe
  · have valueLeOne : value ≤ 1 := le_of_not_ge oneLe
    have squareLeValue : value ^ 2 ≤ value := by
      rw [pow_two]
      calc
        value * value ≤ 1 * value :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            valueLeOne valueNonnegative
        _ = value := by ring1
    exact (Fraction.Order.Basic.min_le_right _ _).trans (lowerLtSquare.le.trans squareLeValue)

set_option genInjectivity false in
/-- Exact finite pole/apart classification of the denominator relation on a
retained child.  The apart branch carries a uniform rational denominator
lower bound; the pole branch carries only its explicit factorization and
does not assert a factor zero. -/
inductive DenominatorClassification
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation analysis) where
  /-- Retain the exact denominator-quadrance factorization and its identity with the original equality relation. -/ |
    pole
      (cofactor : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
      (factorization : Polynomial.Dense.Rational.Factorization
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)
        analysis.profile.factor.polynomial cofactor)
      (relationEq : denominator.relation =
        ConditionRelation.equality
          cofactor factorization)
  /-- Retain the original coprimality witness, its relation identity and the uniform denominator-quadrance lower bound
    on the child. -/ | apart
      (certificate : CoprimeCertificate
        analysis.profile.factor.polynomial
          (Curve.Coordinates.denominatorNormSq
            chart.parameterization.curve))
      (relationEq : denominator.relation =
        ConditionRelation.apart
          certificate)
      (lower : ∀ parameter : Fraction.Rational,
        requestEntry.cell.interval.Contains parameter →
        denominator.apartLower certificate ≤
          Data.Gaussian.Norm.Basic.normSq
            (chart.parameterization.curve.denominatorAt parameter))

constructive_injectivity
  DenominatorClassification

/-- Execute the profile's finite pole/apart denominator split and attach the
uniform lower bound in the apart branch. -/
@[expose] def classifyDenominator
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (requestEntry : CompleteRequestLeaf leaf epsilon)
    (denominator : Curve.Event.Profile.Complete.Denominator.ProfileDenominatorRelation analysis)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis) :
    DenominatorClassification requestEntry denominator := by
  match relationEq : denominator.relation with
  | .equality cofactor factorization =>
      exact .pole cofactor factorization relationEq
  | .apart certificate =>
      exact .apart certificate relationEq (by
        intro parameter inside
        exact requestEntry.denominatorNormSq_lower_of_apart denominator
          certificate relationEq positive epsilonLe parameter inside)

end Basic.CompleteRequestLeaf
end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete

end
