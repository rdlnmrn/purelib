module
-- Public relation conditions retain the finite universal-predicate owner.
public import Purelib.Data.List.All
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Sign
import Mathlib.Data.List.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Request
import Purelib.RootIsolation.Sturm.Track.Basic

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts
  (SourcePersistentConditionProfilesProfileAnalysisAlias
   SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (ProfileEventLeaf)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Classification

/-! ## Exhaustive inside/outside classification of profile roots -/

/-- A condition polynomial paired with its exact equality or apart relation to the retained profile factor. -/
abbrev ProfileRelation
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) :=
  Sigma fun condition =>
    Dense.Rational.Factorization.ConditionRelation condition
      analysis.profile.factor

/-- The condition is nonnegative at every displayed rational factor zero in the requested interval. -/
@[expose] def RootNonnegativeOnRequest
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry :
      ProfileRelation analysis)
    (epsilon : Fraction.Rational) : Prop :=
  ∀ parameter : Fraction.Rational,
    (leaf.request epsilon).cell.interval.Contains parameter →
    analysis.profile.factor.polynomial.eval parameter = 0 →
    0 ≤ entry.1.eval parameter

/-- The condition is strictly negative throughout the requested rational interval. -/
@[expose] def ConditionNegativeOnRequest
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry :
      ProfileRelation analysis)
    (epsilon : Fraction.Rational) : Prop :=
  ∀ parameter : Fraction.Rational,
    (leaf.request epsilon).cell.interval.Contains parameter →
    entry.1.eval parameter < 0

set_option genInjectivity false in
/-- One relation is either nonnegative at every displayed rational parameter
where the profile factor evaluates exactly to zero, or strictly negative
throughout the entire rational request interval. -/
inductive RootConditionClassification
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry :
      ProfileRelation analysis)
    (epsilon : Fraction.Rational) where
  /-- The condition is nonnegative at each displayed factor zero in the request. -/ | nonnegative (holds :
    RootNonnegativeOnRequest leaf entry epsilon)
  /-- The condition is strictly negative throughout the request interval. -/ | negative (holds :
    ConditionNegativeOnRequest leaf entry epsilon)

constructive_injectivity RootConditionClassification

/-- Classify one equality/apart relation using one displayed event sample.
Equality ownership is read exactly at roots; an apart relation transports the
sample's strict sign across the whole request. -/
@[expose] def classifyRootCondition
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry :
      ProfileRelation analysis)
    (member : entry ∈ analysis.profile.relations)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ Curve.Event.Profile.Sign.profileSignWidth analysis)
    (sample : Fraction.Rational)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    RootConditionClassification leaf entry epsilon := by
  rcases entry with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact .nonnegative (by
        intro parameter _inside factorZero
        rw [Dense.Rational.Factorization.eval_factorization
          factorization parameter, factorZero,
          Fraction.Field.zero_mul_direct])
  | apart apart =>
      have apartWidthLe : epsilon ≤
          ProfileEventLeaf.apartSignWidth analysis condition apart :=
        epsilonLe.trans
          (Curve.Event.Profile.Sign.profileSignWidth_le_apart analysis condition apart member)
      have sampleStable := leaf.condition_eval_mul_pos_of_le condition apart
        epsilon positive apartWidthLe sampleInside sampleInside
      by_cases sampleNegative : condition.eval sample < 0
      · exact .negative (by
          intro parameter parameterInside
          exact Purelib.Data.Rat.Fraction.Order.Arithmetic.negative_of_mul_pos_right_neg
            (leaf.condition_eval_mul_pos_of_le condition apart epsilon positive
              apartWidthLe parameterInside sampleInside)
            sampleNegative)
      · have sampleNonnegative : 0 ≤ condition.eval sample :=
          le_of_not_gt sampleNegative
        have sampleNonzero : condition.eval sample ≠ 0 := by
          intro sampleZero
          rw [sampleZero, Fraction.Field.zero_mul_direct]
            at sampleStable
          exact (lt_irrefl 0 sampleStable).elim
        have samplePositive : 0 < condition.eval sample :=
          lt_of_le_of_ne sampleNonnegative (Ne.symm sampleNonzero)
        exact .nonnegative (by
          intro parameter parameterInside _factorZero
          exact (Purelib.Data.Rat.Fraction.Order.Arithmetic.positive_of_mul_pos_right_pos
            (leaf.condition_eval_mul_pos_of_le condition apart epsilon positive
              apartWidthLe parameterInside sampleInside)
            samplePositive).le)

set_option genInjectivity false in
/-- Finite scan result for a displayed sublist of the profile relations. -/
inductive RootRelationsClassification
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Fraction.Rational)
    (relations : List (ProfileRelation analysis)) where
  /-- Every retained relation is nonnegative at the displayed factor zeros of the request. -/ | inside (holds : ∀ entry
    ∈ relations,
      RootNonnegativeOnRequest leaf entry epsilon)
  /-- Retain a particular member relation that is strictly negative throughout the request. -/ | outside (entry :
    ProfileRelation analysis) (member : entry ∈ relations)
      (fails : ConditionNegativeOnRequest leaf entry epsilon)

constructive_injectivity RootRelationsClassification

/-- Execute the finite equality/apart scan for any displayed relation
sublist whose entries come from the complete profile. -/
@[expose] def classifyRootRelations
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ Curve.Event.Profile.Sign.profileSignWidth analysis)
    (sample : Fraction.Rational)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    ∀ (relations : List (ProfileRelation analysis)),
      (∀ entry ∈ relations, entry ∈ analysis.profile.relations) →
        RootRelationsClassification leaf epsilon relations
  | [], _ => .inside (by intro entry member; nomatch member)
  | head :: tail, subset =>
      match classifyRootCondition leaf head
          (subset head List.mem_cons_self) epsilon positive epsilonLe sample
            sampleInside with
      | .negative fails => .outside head List.mem_cons_self fails
      | .nonnegative headHolds =>
          match classifyRootRelations leaf epsilon positive
            epsilonLe sample
              sampleInside tail
              (fun entry member => subset entry
                (List.mem_cons_of_mem head member)) with
          | .outside entry member fails =>
              .outside entry (List.mem_cons_of_mem head member) fails
          | .inside tailHolds =>
              .inside (by
                intro entry member
                rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
                · exact headHolds
                · exact tailHolds entry tailMember)

/-- Pointwise list-shaped nonnegativity of every relation in one profile. -/
@[expose] def RelationsNonnegativeAt
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (parameter :
      Fraction.Rational) :
    Prop :=
  Data.List.Forall (fun entry =>
    0 ≤ entry.1.eval parameter) analysis.profile.relations

/-- The profile's relation list is aligned with the denominator quadrance
followed by the four cleared box conditions.  The first condition is
automatically nonnegative, so complete relation nonnegativity is equivalent
to the original four-condition box predicate. -/
theorem relationsNonnegativeAt_iff_listedHolds
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) (parameter :
      Fraction.Rational) :
    RelationsNonnegativeAt analysis parameter ↔
      Curve.Box.ListedHolds
        chart.parameterization.curve box parameter := by
  let predicate := fun condition :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial =>
        0 ≤ condition.eval parameter
  have mapped : RelationsNonnegativeAt analysis parameter ↔
      Data.List.Forall predicate (analysis.profile.relations.map Sigma.fst) := by
    change Data.List.Forall (predicate ∘ Sigma.fst)
        analysis.profile.relations ↔
      Data.List.Forall predicate (analysis.profile.relations.map Sigma.fst)
    exact (Data.List.All.forall_map_iff (values := analysis.profile.relations)
      (predicate := predicate) (map := Sigma.fst)).symm
  have aligned :
      Data.List.Forall predicate (analysis.profile.relations.map Sigma.fst) =
        Data.List.Forall predicate (Curve.Box.profiledConditionPolynomials
          chart.parameterization.curve box) :=
    congrArg (fun conditions => Data.List.Forall predicate conditions)
      analysis.profile.conditions_eq
  have profiled :=
    Curve.Box.profiledListedHolds_iff_listedHolds
      chart.parameterization.curve box parameter
  exact mapped.trans
    ⟨fun holds => profiled.mp (aligned.mp holds),
      fun holds => aligned.mpr (profiled.mpr holds)⟩

set_option genInjectivity false in
/-- The complete requested profile event is classified semantically: every
aligned denominator/box relation is nonnegative at every displayed rational
profile root, or one fixed aligned relation is strictly negative at every
such root.  `ConditionProfile.conditions_eq` identifies these relations with
the denominator quadrance followed by the four box conditions. -/
inductive ProfileEventBoxClassification
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Fraction.Rational) where
  /-- Every retained relation is nonnegative at the displayed factor zeros of the request. -/ | inside (holds : ∀ entry
    ∈ analysis.profile.relations,
      RootNonnegativeOnRequest leaf entry epsilon)
  /-- Retain a particular member relation that is strictly negative throughout the request. -/ | outside (entry :
    ProfileRelation analysis)
      (member : entry ∈ analysis.profile.relations)
      (fails : ConditionNegativeOnRequest leaf entry epsilon)

constructive_injectivity ProfileEventBoxClassification

/-- Compute the whole-profile-event box classification from one displayed
parameter in the profile-wide request. -/
@[expose] def classifyProfileEventBox
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ Curve.Event.Profile.Sign.profileSignWidth analysis)
    (sample : Fraction.Rational)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    ProfileEventBoxClassification leaf epsilon := by
  have classified := classifyRootRelations leaf epsilon positive epsilonLe
    sample sampleInside analysis.profile.relations
    (by intro entry member; exact member)
  cases classified with
  | inside allNonnegative =>
      exact .inside allNonnegative
  | outside entry entryMember fails =>
      exact .outside entry entryMember fails

/-- Total whole-event classifier.  The lower endpoint is already a
displayed rational sample in the closed requested cell; no affine point or
denominator choice is needed to determine the profile-root signs. -/
@[expose] def classifyRequestedProfileEventBox
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    ProfileEventBoxClassification leaf (Curve.Event.Profile.Sign.profileSignWidth
      analysis) :=
  classifyProfileEventBox leaf (Curve.Event.Profile.Sign.profileSignWidth analysis)
    (Curve.Event.Profile.Sign.profileSignWidth_pos analysis) le_rfl
    (leaf.request (Curve.Event.Profile.Sign.profileSignWidth analysis)).cell.interval.lower
    ⟨le_rfl,
      (leaf.request (Curve.Event.Profile.Sign.profileSignWidth analysis)).cell.proper.le⟩

set_option genInjectivity false in
/-- Affine meaning of the total profile classification.  The inside branch
is conditional on a supplied displayed rational factor zero; it asserts no
root existence.  The outside branch excludes every displayed non-pole
parameter in the whole requested interval and needs no root premise. -/
inductive ProfileEventAffineClassification
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Fraction.Rational) where
  /-- Every displayed non-pole factor zero in the request maps into the original box. -/ | inside (contains : ∀
    parameter : Fraction.Rational,
      (leaf.request epsilon).cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter = 0 →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      box.Contains (chart.parameterization.curve.point parameter))
  /-- Every displayed non-pole parameter in the request maps outside the original box. -/ | outside (excludes : ∀
    parameter : Fraction.Rational,
      (leaf.request epsilon).cell.interval.Contains parameter →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      ¬ box.Contains (chart.parameterization.curve.point parameter))

constructive_injectivity ProfileEventAffineClassification

/-- Convert a sufficiently narrow finite aligned-sign request into its exact
affine box semantics, without constructing or quantifying over a completed
root. -/
@[expose] def classifyProfileEventAffine
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ Curve.Event.Profile.Sign.profileSignWidth analysis) :
    ProfileEventAffineClassification leaf epsilon := by
  let sample := (leaf.request epsilon).cell.interval.lower
  have sampleInside : (leaf.request epsilon).cell.interval.Contains sample :=
    ⟨le_rfl, (leaf.request epsilon).cell.proper.le⟩
  match classifyProfileEventBox leaf epsilon positive epsilonLe sample
      sampleInside with
  | .inside allNonnegative =>
      exact .inside (by
        intro parameter parameterInside factorZero denominatorNonzero
        have relationsNonnegative : RelationsNonnegativeAt analysis
            parameter :=
          Data.List.All.forall_iff_mem.mpr (by
            intro entry member
            exact allNonnegative entry member parameter parameterInside
              factorZero)
        have listed :=
          (relationsNonnegativeAt_iff_listedHolds analysis parameter).mp
            relationsNonnegative
        have holds :=
          (Curve.Box.listedHolds_iff_holds
            chart.parameterization.curve box parameter).mp listed
        exact (Curve.Box.holds_iff_contains
          chart.parameterization.curve box parameter denominatorNonzero).mp
            holds)
  | .outside entry member negative =>
      exact .outside (by
        intro parameter parameterInside denominatorNonzero contained
        have holds :=
          (Curve.Box.holds_iff_contains
            chart.parameterization.curve box parameter denominatorNonzero).mpr
              contained
        have listed :=
          (Curve.Box.listedHolds_iff_holds
            chart.parameterization.curve box parameter).mpr holds
        have relationsNonnegative :=
          (relationsNonnegativeAt_iff_listedHolds analysis parameter).mpr
            listed
        have entryNonnegative :=
          (Data.List.All.forall_iff_mem.mp relationsNonnegative) entry member
        exact (not_lt_of_ge entryNonnegative)
          (negative parameter parameterInside))

/-- Specialization at the computed profile-sign width. -/
@[expose] def classifyRequestedProfileEventAffine
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    ProfileEventAffineClassification leaf (Curve.Event.Profile.Sign.profileSignWidth
      analysis) :=
  classifyProfileEventAffine leaf (Curve.Event.Profile.Sign.profileSignWidth
    analysis)
    (Curve.Event.Profile.Sign.profileSignWidth_pos analysis) le_rfl
end Purelib.RootIsolation.Curve.Event.Profile.Classification

end
