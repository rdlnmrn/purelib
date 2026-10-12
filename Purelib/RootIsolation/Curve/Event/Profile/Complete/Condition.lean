module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Refinement
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Residual

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

open Purelib.Algebra
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

/-- Fixed finite coefficient carrying a profile-factor residual through an
equality-owned condition's retained cofactor. -/
@[expose] def
  Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (cofactor : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial) :
    Fraction.Rational :=
  Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient
      analysis *
    Dense.Rational.Bounds.Horner.evalSqBound cofactor chart.cell.interval

/-- The profile residual coefficient multiplied by the retained equality-cofactor Horner bound is nonnegative. -/
theorem
  Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (cofactor : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial) :
    0 ≤ Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient analysis cofactor :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
      analysis)
    (Dense.Rational.Bounds.Horner.evalSqBound_nonneg cofactor
      chart.cell.interval)

/-- Equality ownership remains quantitative without naming a factor root:
throughout a requested event, the condition residual is bounded by the
profile residual times the explicit equality cofactor bound. -/
theorem
  Basic.CompleteRequestLeaf.equality_condition_eval_sq_le
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (condition cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization : Polynomial.Dense.Rational.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 ≤
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient analysis cofactor *
        epsilon ^ 2 := by
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨entry.refines_chart.1.trans inside.1,
      inside.2.trans entry.refines_chart.2⟩
  have factorBound := entry.factor_eval_sq_le positive parameter inside
  have cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  rw [Dense.Rational.Factorization.eval_factorization factorization
    parameter, Semiring.Normalization.product_pow]
  exact
    (Fraction.Order.Arithmetic.mul_le_mul_direct factorBound cofactorBound
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (cofactor.eval parameter))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
          analysis)
        (Fraction.Order.Arithmetic.sq_nonneg_direct epsilon))).trans_eq (by
          simp only [-eq_self, -iff_self,
            Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient]
          ring1)

/-- Positive event width forcing one equality-owned condition residual below
an arbitrary supplied rational target. -/
@[expose] def Basic.CompleteRequestLeaf.equalityConditionWidth
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (cofactor : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (target : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.SmallWidth.shrinkingWidth
    (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient analysis cofactor)
      target

/-- A positive residual target gives a positive coefficient-computed width for the equality condition. -/
theorem Basic.CompleteRequestLeaf.equalityConditionWidth_pos
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (cofactor : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor target :=
  Data.Rat.SmallWidth.shrinkingWidth_pos
    (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg analysis
      cofactor)
    targetPositive

/-- At every narrower requested width, the explicit equality cofactor turns
the profile-factor approximation into the requested strict condition bound. -/
theorem
  Basic.CompleteRequestLeaf.equality_condition_eval_sq_lt
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon
      target : Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (positive : 0 < epsilon)
    (condition cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization : Polynomial.Dense.Rational.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (epsilonLe : epsilon ≤ Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis
      cofactor target)
    (targetPositive : 0 < target)
    (parameter : Fraction.Rational)
    (inside : entry.cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < target := by
  have widthSquareLe : epsilon ^ 2 ≤
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor target ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct positive.le epsilonLe 2
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquareLe
      (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg analysis
        cofactor)
  exact (entry.equality_condition_eval_sq_le positive condition cofactor
      factorization parameter inside).trans_lt
    (scaled.trans_lt
      (Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg analysis
          cofactor)
        targetPositive))

/-- The same equality-cofactor estimate on a later deterministic request from
an already retained child.  The conclusion concerns every supplied rational
parameter of that descendant and does not assert a factor zero. -/
theorem
  Basic.CompleteRequestLeaf.request_equality_condition_eval_sq_lt
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon
      target bound : Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < target)
    (condition cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization : Polynomial.Dense.Rational.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (targetLe : target ≤ Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor
      bound)
    (boundPositive : 0 < bound)
    (parameter : Fraction.Rational)
    (inside : (entry.request target).cell.interval.Contains parameter) :
    condition.eval parameter ^ 2 < bound := by
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨(entry.request_refines_chart target).1.trans inside.1,
      inside.2.trans (entry.request_refines_chart target).2⟩
  have factorBound := entry.request_factor_eval_sq_le target positive
    parameter inside
  have cofactorBound :=
    Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have conditionBound : condition.eval parameter ^ 2 ≤
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient analysis cofactor *
        target ^ 2 := by
    rw [Dense.Rational.Factorization.eval_factorization
      factorization parameter, Semiring.Normalization.product_pow]
    exact
      (Fraction.Order.Arithmetic.mul_le_mul_direct factorBound cofactorBound
        (Fraction.Order.Arithmetic.sq_nonneg_direct (cofactor.eval parameter))
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Curve.Event.Profile.Basic.ProfileEventLeaf.factorResidualCoefficient_nonneg
            analysis)
          (Fraction.Order.Arithmetic.sq_nonneg_direct target))).trans_eq (by
            simp only [-eq_self, -iff_self,
              Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient]
            ring1)
  have targetSquareLe : target ^ 2 ≤
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor bound ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct positive.le targetLe 2
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct targetSquareLe
      (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg analysis
        cofactor)
  exact conditionBound.trans_lt
    (scaled.trans_lt
      (Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
        (Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionResidualCoefficient_nonneg analysis
          cofactor)
        boundPositive))
end CompleteRequestLeaf

/-! ## Uniform quantitative widths for equality-owned profile conditions -/

/-- Width assigned to one profile relation when controlling approximate box
conditions.  Equality relations use their retained cofactor bound; apart
relations already have a stable strict sign and need no additional shrink. -/
@[expose] def Condition.relationConditionRequestWidth
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    (target : Fraction.Rational) : Fraction.Rational :=
  match relation.2 with
  | .equality cofactor _factorization =>
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor target
  | .apart _apart => 1

/-- Every retained equality or apart relation contributes a positive width for a positive condition target. -/
theorem Condition.relationConditionRequestWidth_pos
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth analysis relation target := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth_pos analysis cofactor
        targetPositive
  | apart apart =>
      exact (show (0 : Fraction.Rational) < 1 by decide)

/-- Finite list of the quantitative condition widths for one exact profile. -/
@[expose] def Condition.profileConditionRequestWidths
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (target : Fraction.Rational) : List Fraction.Rational :=
  analysis.profile.relations.map fun relation =>
    Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth analysis relation target

/-- The width for a member profile relation occurs in the computed finite condition-width list. -/
theorem Condition.relationConditionRequestWidth_mem
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (target : Fraction.Rational)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations) :
    Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth analysis relation target ∈
      Curve.Event.Profile.Complete.Condition.profileConditionRequestWidths analysis target :=
  Data.List.Map.mem_map.mpr ⟨relation, member, rfl⟩

/-- Every width in the original profile's finite condition-width list is positive. -/
theorem Condition.profileConditionRequestWidths_positive
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    ∀ width ∈ Curve.Event.Profile.Complete.Condition.profileConditionRequestWidths analysis target, 0 < width := by
  intro width member
  dsimp only [Curve.Event.Profile.Complete.Condition.profileConditionRequestWidths] at member
  have member := Data.List.Map.mem_map.mp member
  rcases member with ⟨relation, _relationMember, rfl⟩
  exact Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth_pos analysis relation targetPositive

/-- One positive rational width below every equality-cofactor condition width
in a profile.  An empty relation list retains the harmless value `1`. -/
@[expose] def Condition.profileConditionRequestWidth
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (target : Fraction.Rational) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidths analysis target)

/-- The finite common condition width is positive for a positive target. -/
theorem Condition.profileConditionRequestWidth_pos
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis target :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidths_positive analysis targetPositive)

/-- The common condition width is no larger than the width for each retained member relation. -/
theorem Condition.profileConditionRequestWidth_le_relation
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis)
    (target : Fraction.Rational)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations) :
    Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis target ≤
      Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth analysis relation target :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
    (Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth_mem analysis target relation member)

section CompleteRequestLeaf

/-- Quantitative negative-cap bound for one equality-owned relation on the
common condition-controlled descendant. -/
theorem
  Basic.CompleteRequestLeaf.request_equality_condition_eval_gt_neg_cap
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (condition cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization : Polynomial.Dense.Rational.Factorization
      condition analysis.profile.factor.polynomial cofactor)
    (member :
      (⟨condition,
        Dense.Rational.Factorization.ConditionRelation.equality
          cofactor factorization⟩ :
        Curve.Event.Profile.Classification.ProfileRelation
          analysis) ∈ analysis.profile.relations)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (parameter : Fraction.Rational)
    (inside : (entry.request
      (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < condition.eval parameter := by
  let target := Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis (cap ^ 2)
  have capSquarePositive : 0 < cap ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct capPositive 2
  have targetPositive : 0 < target := by
    simpa only [-eq_self, -iff_self, target] using
      Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth_pos analysis capSquarePositive
  have targetLe : target ≤
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.equalityConditionWidth analysis cofactor (cap ^ 2) := by
    have relationLe := Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth_le_relation analysis
      (cap ^ 2)
      (⟨condition,
        Dense.Rational.Factorization.ConditionRelation.equality
          cofactor factorization⟩ :
        Curve.Event.Profile.Classification.ProfileRelation
          analysis)
      member
    simpa only [-eq_self, -iff_self, target, Curve.Event.Profile.Complete.Condition.relationConditionRequestWidth] using
      relationLe
  have squareSmall := entry.request_equality_condition_eval_sq_lt
    targetPositive condition cofactor factorization targetLe
      capSquarePositive parameter (by simpa only [-eq_self, -iff_self, target] using inside)
  have negSquareSmall : (-condition.eval parameter) ^ 2 < cap ^ 2 := by
    have same : (-condition.eval parameter) ^ 2 = condition.eval parameter ^ 2 := by ring1
    exact same.symm ▸ squareSmall
  have negEvalLtCap :=
    Data.Rat.Bounds.Square.lt_of_sq_lt_sq_of_nonneg
      capPositive.le negSquareSmall
  simpa only [-eq_self, -iff_self, neg_neg] using
    Fraction.Order.Arithmetic.neg_lt_neg_direct negEvalLtCap

/-- Negative-cap bound for one apart relation from its retained stable
nonnegative sign. -/
theorem
  Basic.CompleteRequestLeaf.request_apart_condition_eval_gt_neg_cap
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (condition : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (apart : Dense.Rational.Bezout.Basic.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (nonnegative : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry
      (⟨condition,
        Dense.Rational.Factorization.ConditionRelation.apart apart⟩ :
        Curve.Event.Profile.Classification.ProfileRelation
          analysis))
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (parameter : Fraction.Rational)
    (inside : (entry.request
      (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < condition.eval parameter := by
  have descendantRefines := entry.request_refines
    (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis (cap ^ 2))
  have parentInside : entry.cell.interval.Contains parameter :=
    ⟨descendantRefines.1.trans inside.1,
      inside.2.trans descendantRefines.2⟩
  have negative : -cap < (0 : Fraction.Rational) := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct capPositive
    have zeroNeg : -(0 : Fraction.Rational) = 0 := by ring1
    rewrite [zeroNeg] at reversed
    exact reversed
  exact negative.trans_le (nonnegative parameter parentInside)

/-- On the deterministic descendant requested at the profile-wide condition
width, every retained relation is greater than the same negative rational
cap.  Apart relations use their stable nonnegative sign; equality relations
use their explicit cofactor residual bound. -/
theorem
  Basic.CompleteRequestLeaf.request_condition_eval_gt_neg_cap
    {leaf : Curve.Event.Profile.Basic.SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (allNonnegative : ∀ relation ∈ analysis.profile.relations,
      Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.ConditionNonnegative entry relation)
    (relation :
      Curve.Event.Profile.Classification.ProfileRelation analysis)
    (member : relation ∈ analysis.profile.relations)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (parameter : Fraction.Rational)
    (inside : (entry.request
      (Curve.Event.Profile.Complete.Condition.profileConditionRequestWidth analysis (cap ^ 2))).cell.interval.Contains
        parameter) :
    -cap < relation.1.eval parameter := by
  rcases relation with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact entry.request_equality_condition_eval_gt_neg_cap condition
        cofactor factorization member capPositive parameter inside
  | apart apart =>
      exact entry.request_apart_condition_eval_gt_neg_cap condition apart
        (allNonnegative
          (⟨condition,
            Dense.Rational.Factorization.ConditionRelation.apart
              apart⟩ :
            Curve.Event.Profile.Classification.ProfileRelation
              analysis)
          member)
        capPositive parameter inside

end CompleteRequestLeaf
end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete

end
