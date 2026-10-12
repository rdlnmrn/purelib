module
import Purelib.Data.List.Attach
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts
  (SourcePersistentConditionProfilesProfileAnalysisAlias
   SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (ProfileEventLeaf)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Family

/-- Retain an original profile subdivision cell when its displayed Sturm count is nonzero. -/
def profileEventLeaf?
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
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis)
    (cell : Data.Rat.Interval.Proper.Cell)
    (member : cell ∈ analysis.partition.tree.leaves) :
    Option (ProfileEventLeaf analysis) := by
  let classification := analysis.partition.classify cell member
  if countNonzero : classification.eventCount ≠ 0 then
    exact some ⟨cell, member, countNonzero⟩
  else
    exact none

/-- Collect all nonzero-count leaves of the original condition-profile analysis. -/
def profileEventLeaves
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
    (analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) :
    List (ProfileEventLeaf analysis) :=
  analysis.partition.tree.leaves.attach.filterMap fun entry =>
    profileEventLeaf? analysis entry.1 entry.2

/-- Testing an already retained profile event leaf returns its exact original record. -/
theorem profileEventLeaf?_eq_some
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
    profileEventLeaf? analysis leaf.cell leaf.member = some leaf := by
  simp only [-eq_self, -iff_self, profileEventLeaf?, dif_pos leaf.countNonzero]
  rfl

/-- Every retained nonzero-count profile leaf occurs in the computed leaf list. -/
theorem mem_profileEventLeaves
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
    leaf ∈ profileEventLeaves analysis := by
  rw [profileEventLeaves]
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨⟨leaf.cell, leaf.member⟩, ?_, ?_⟩
  · exact Data.List.Attach.mem_attach _ _
  · exact profileEventLeaf?_eq_some leaf

/-- An original condition-profile analysis paired with one of its retained nonzero-count leaves. -/
abbrev ProfileEventEntry
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive) :=
  Sigma fun analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis =>
    ProfileEventLeaf analysis

/-- Collect nonzero-count event leaves across all original condition-profile analyses. -/
def profileEventFamily
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive) : List (ProfileEventEntry factorAnalysis) :=
  (Curve.Chart.analyzeConditionProfiles
    factorAnalysis).flatMap fun analysis =>
      (profileEventLeaves analysis).map fun leaf => ⟨analysis, leaf⟩

/-- A retained event leaf of an original member profile belongs to the complete computed event family. -/
theorem mem_profileEventFamily
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
    (analysisMember : analysis ∈
      Curve.Chart.analyzeConditionProfiles
        factorAnalysis)
    (leaf : ProfileEventLeaf analysis) :
    (⟨analysis, leaf⟩ : ProfileEventEntry factorAnalysis) ∈
      profileEventFamily factorAnalysis := by
  rw [profileEventFamily]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨analysis, analysisMember, ?_⟩
  apply Data.List.Map.mem_map.mpr
  exact ⟨leaf, mem_profileEventLeaves leaf, rfl⟩
end Purelib.RootIsolation.Curve.Event.Profile.Family

end

section
@[expose] public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Family
/-- The original profile-analysis and event-leaf pair used by persistent boundary events. -/
abbrev
  SourcePersistentProfileBoundaryEventsProfileEventEntryAlias
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileBoundaryEventsSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive) :=
  ProfileEventEntry
    factorAnalysis
end Purelib.RootIsolation.Curve.Event.Profile.Family

end
