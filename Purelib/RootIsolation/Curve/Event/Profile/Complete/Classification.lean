module
import Purelib.Data.List.All
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Classification
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.ScalarBounds
import Purelib.RootIsolation.Curve.Event.Profile.Sign
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Residual
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis

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
variable {analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}
section CompleteRequestLeaf

/-- Every apart condition remains uniformly separated from zero throughout a
retained child at any positive width below its rational sign width. -/
theorem
  Basic.CompleteRequestLeaf.apartConditionLower_lt_eval_sq
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (condition : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.apartSignWidth
        analysis condition apart)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    Curve.Event.Profile.Basic.ProfileEventLeaf.apartConditionLower
        analysis condition apart <
      condition.eval parameter ^ 2 :=
  Curve.Event.Profile.Basic.ProfileEventLeaf.apartConditionLower_lt_eval_sq_on_cell
    entry.cell condition apart epsilon positive epsilonLe entry.refines_chart
      (entry.width_le positive)
      (fun value valueInside =>
        entry.factor_eval_sq_le positive value valueInside)
      parameter inside

/-- Every apart condition has one stable strict sign throughout a retained
child at any positive width below the profile-wide sign width. -/
theorem Basic.CompleteRequestLeaf.condition_eval_mul_pos
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (condition : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Basic.ProfileEventLeaf.apartSignWidth
        analysis condition apart)
    {left right : Fraction.Rational}
    (leftInside : entry.cell.interval.Contains left)
    (rightInside : entry.cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  Curve.Event.Profile.Basic.ProfileEventLeaf.condition_eval_mul_pos_on_cell
    entry.cell condition apart epsilon positive epsilonLe entry.refines_chart
      (entry.width_le positive)
      (fun parameter parameterInside =>
        entry.factor_eval_sq_le positive parameter parameterInside)
      leftInside rightInside

/-- Constructive nonnegativity data appropriate to one exact profile
relation.  Equality-owned conditions are required only at a separately
supplied displayed rational factor zero; apart conditions retain their stable
nonnegative sign throughout the whole rational cell. -/
@[expose] def Basic.CompleteRequestLeaf.ConditionNonnegative
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation
        analysis) : Prop :=
  match relation with
  | ⟨condition, .equality _cofactor _factorization⟩ =>
      ∀ parameter : Fraction.Rational,
        entry.cell.interval.Contains parameter →
        analysis.profile.factor.polynomial.eval parameter = 0 →
        0 ≤ condition.eval parameter
  | ⟨condition, .apart _apart⟩ =>
      ∀ parameter : Fraction.Rational,
        entry.cell.interval.Contains parameter →
        0 ≤ condition.eval parameter

/-- Either form of the retained relation certificate supplies nonnegativity
at a separately supplied displayed rational profile zero. -/
theorem
  Basic.CompleteRequestLeaf.ConditionNonnegative.atFactorZero
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    {entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon}
    {relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis}
    (holds : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter)
    (factorZero :
      analysis.profile.factor.polynomial.eval parameter = 0) :
    0 ≤ relation.1.eval parameter := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact holds parameter inside factorZero
  | apart apart =>
      exact holds parameter inside

/-- One relation is strictly negative at every rational parameter of a
retained child. -/
@[expose] def Basic.CompleteRequestLeaf.ConditionNegative
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation
        analysis) : Prop :=
  ∀ parameter : Fraction.Rational,
    entry.cell.interval.Contains parameter →
    relation.1.eval parameter < 0

set_option genInjectivity false in
/-- Exact finite classification of one relation on a retained child. -/
inductive Basic.CompleteRequestLeaf.RelationClassification
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation
        analysis) where
  /-- Retain the equality-at-roots or whole-cell apart nonnegativity appropriate to this exact relation. -/ |
    nonnegative (holds : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
  /-- Retain strict negativity of the condition throughout the displayed child cell. -/ | negative (holds :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNegative entry relation)

constructive_injectivity Basic.CompleteRequestLeaf.RelationClassification

/-- Classify one equality/apart relation from one rational sample in the
retained child. -/
@[expose] def Basic.CompleteRequestLeaf.classifyRelation
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation
        analysis)
    (member : relation ∈ analysis.profile.relations)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis)
    (sample : Fraction.Rational)
    (sampleInside : entry.cell.interval.Contains sample) :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.RelationClassification entry relation := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact .nonnegative (by
        intro parameter _inside factorZero
        rw [Dense.Rational.Factorization.eval_factorization
          factorization parameter, factorZero,
          Fraction.Field.zero_mul_direct])
  | apart apart =>
      have apartWidthLe : epsilon ≤
          Curve.Event.Profile.Basic.ProfileEventLeaf.apartSignWidth
            analysis condition apart :=
        epsilonLe.trans
          (Curve.Event.Profile.Sign.profileSignWidth_le_apart
            analysis condition apart member)
      have sampleStable := entry.condition_eval_mul_pos condition apart
        positive apartWidthLe sampleInside sampleInside
      by_cases sampleNegative : condition.eval sample < 0
      · exact .negative (by
          intro parameter parameterInside
          exact Purelib.Data.Rat.Fraction.Order.Arithmetic.negative_of_mul_pos_right_neg
            (entry.condition_eval_mul_pos condition apart positive apartWidthLe
              parameterInside sampleInside)
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
          intro parameter parameterInside
          exact (Purelib.Data.Rat.Fraction.Order.Arithmetic.positive_of_mul_pos_right_pos
            (entry.condition_eval_mul_pos condition apart positive apartWidthLe
              parameterInside sampleInside)
            samplePositive).le)

set_option genInjectivity false in
/-- Finite scan result for any displayed sublist of a retained child's
profile relations. -/
inductive Basic.CompleteRequestLeaf.RelationsClassification
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relations : List
      (Curve.Event.Profile.Classification.ProfileRelation
        analysis)) where
  /-- Every retained member relation has its appropriate nonnegativity certificate on this child. -/ | inside (holds : ∀
    relation ∈ relations,
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
  /-- Retain one member relation that is strictly negative throughout this child. -/ | outside (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
      (member : relation ∈ relations)
      (fails : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNegative entry relation)

constructive_injectivity Basic.CompleteRequestLeaf.RelationsClassification

/-- Execute the exact equality/apart scan for a retained child. -/
@[expose] def Basic.CompleteRequestLeaf.classifyRelations
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis)
    (sample : Fraction.Rational)
    (sampleInside : entry.cell.interval.Contains sample) :
    ∀ relations : List
        (Curve.Event.Profile.Classification.ProfileRelation
          analysis),
      (∀ relation ∈ relations, relation ∈ analysis.profile.relations) →
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.RelationsClassification entry relations
  | [], _ => .inside (by intro relation member; nomatch member)
  | head :: tail, subset =>
      match Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.classifyRelation entry head (subset head
        List.mem_cons_self)
          positive epsilonLe sample sampleInside with
      | .negative fails => .outside head List.mem_cons_self fails
      | .nonnegative headHolds =>
          match Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.classifyRelations entry
            positive epsilonLe sample sampleInside
              tail (fun relation member =>
                subset relation (List.mem_cons_of_mem head member)) with
          | .outside relation member fails =>
              .outside relation (List.mem_cons_of_mem head member) fails
          | .inside tailHolds =>
              .inside (by
                intro relation member
                rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
                · exact headHolds
                · exact tailHolds relation tailMember)

set_option genInjectivity false in
/-- Semantic box classification of a complete retained child. -/
inductive Basic.CompleteRequestLeaf.BoxClassification
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) where
  /-- Every retained member relation has its appropriate nonnegativity certificate on this child. -/ | inside (holds : ∀
    relation ∈ analysis.profile.relations,
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
  /-- Retain one member relation that is strictly negative throughout this child. -/ | outside (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
      (member : relation ∈ analysis.profile.relations)
      (fails : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNegative entry relation)

constructive_injectivity Basic.CompleteRequestLeaf.BoxClassification

/-- Compute the whole retained-child box classification from its rational
lower endpoint. -/
@[expose] def Basic.CompleteRequestLeaf.classifyBox
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis) : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.BoxClassification entry := by
  let sample := entry.cell.interval.lower
  have sampleInside : entry.cell.interval.Contains sample :=
    ⟨le_rfl, entry.cell.proper.le⟩
  have classified := Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.classifyRelations entry positive epsilonLe
    sample
    sampleInside analysis.profile.relations
    (by intro relation member; exact member)
  cases classified with
  | inside allNonnegative => exact .inside allNonnegative
  | outside relation member fails => exact .outside relation member fails

set_option genInjectivity false in
/-- Affine meaning of a retained child's exact finite classification.  The
inside branch remains conditional on a supplied displayed rational profile
zero; the outside branch excludes every non-pole rational parameter. -/
inductive Basic.CompleteRequestLeaf.AffineClassification
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) where
  /-- Every displayed non-pole profile zero in the retained child maps into the original box. -/ | inside (contains : ∀
    parameter : Fraction.Rational,
      entry.cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter = 0 →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      box.Contains (chart.parameterization.curve.point parameter))
  /-- Every displayed non-pole parameter in the retained child maps outside the original box. -/ | outside (excludes : ∀
    parameter : Fraction.Rational,
      entry.cell.interval.Contains parameter →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      ¬ box.Contains (chart.parameterization.curve.point parameter))

constructive_injectivity Basic.CompleteRequestLeaf.AffineClassification

/-- Exact affine containment recovered from the complete retained
per-relation certificate and a separately supplied displayed rational profile
zero. -/
theorem
  Basic.CompleteRequestLeaf.contains_of_relations_nonnegative
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (allNonnegative : ∀ relation ∈ analysis.profile.relations,
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
    (parameter : Fraction.Rational)
    (parameterInside : entry.cell.interval.Contains parameter)
    (factorZero :
      analysis.profile.factor.polynomial.eval parameter = 0)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    box.Contains (chart.parameterization.curve.point parameter) := by
  have relationsNonnegative :
      Curve.Event.Profile.Classification.RelationsNonnegativeAt
        analysis parameter :=
    Data.List.All.forall_iff_mem.mpr (by
      intro relation member
      exact (allNonnegative relation member).atFactorZero parameter
        parameterInside factorZero)
  have listed :=
    (Curve.Event.Profile.Classification.relationsNonnegativeAt_iff_listedHolds
      analysis parameter).mp relationsNonnegative
  have holds :=
    (Curve.Box.listedHolds_iff_holds
      chart.parameterization.curve box parameter).mp listed
  exact (Curve.Box.holds_iff_contains
    chart.parameterization.curve box parameter denominatorNonzero).mp holds

/-- Exact whole-cell affine exclusion recovered from one retained negative
relation. -/
theorem
  Basic.CompleteRequestLeaf.excludes_of_relation_negative
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations)
    (negative : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNegative entry relation)
    (parameter : Fraction.Rational)
    (parameterInside : entry.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0) :
    ¬box.Contains (chart.parameterization.curve.point parameter) := by
  intro contained
  have holds :=
    (Curve.Box.holds_iff_contains
      chart.parameterization.curve box parameter denominatorNonzero).mpr
        contained
  have listed :=
    (Curve.Box.listedHolds_iff_holds
      chart.parameterization.curve box parameter).mpr holds
  have relationsNonnegative :=
    (Curve.Event.Profile.Classification.relationsNonnegativeAt_iff_listedHolds
      analysis parameter).mpr listed
  have relationNonnegative :=
    (Data.List.All.forall_iff_mem.mp relationsNonnegative) relation member
  exact (not_lt_of_ge relationNonnegative)
    (negative parameter parameterInside)

/-- Convert one retained finite box classification into its exact affine
semantics without discarding the original per-relation certificate. -/
@[expose] def
  Classification.CompleteRequestLeaf.BoxClassification.toAffine
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    {entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon}
    (classification : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.BoxClassification entry) :
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.AffineClassification entry :=
  match classification with
  | .inside allNonnegative =>
      .inside (entry.contains_of_relations_nonnegative allNonnegative)
  | .outside relation member negative =>
      .outside (entry.excludes_of_relation_negative relation member negative)

/-- Convert the retained child's finite sign scan into exact affine box
semantics. -/
@[expose] def Basic.CompleteRequestLeaf.classifyAffine
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤
      Curve.Event.Profile.Sign.profileSignWidth
        analysis) : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.AffineClassification entry :=
  Curve.Event.Profile.Complete.Classification.CompleteRequestLeaf.BoxClassification.toAffine (entry.classifyBox positive
    epsilonLe)
end CompleteRequestLeaf

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete

end
