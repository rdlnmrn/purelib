module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Basic

set_option genInjectivity false in
/-- One nonzero-count Sturm leaf for a final box-condition profile factor. -/
structure ProfileEventLeaf
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis) where
  /-- The actual retained leaf of the original condition-profile event partition. -/ cell :
    Data.Rat.Interval.Proper.Cell
  /-- The retained cell belongs to the original profile partition's leaf list. -/ member : cell ∈
    analysis.partition.tree.leaves
  /-- The original profile classification has a nonzero doubled event count. -/ countNonzero :
    (analysis.partition.classify cell member).eventCount ≠ 0

constructive_injectivity ProfileEventLeaf

namespace ProfileEventLeaf

/-- Read the original condition-profile partition's classification of this retained leaf. -/
@[expose] def classification
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) :=
  analysis.partition.classify leaf.cell leaf.member

/-- Construct the persistent Sturm state of the original profiled factor on the retained nonzero-count leaf. -/
@[expose] def state
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) :
    Sturm.Track.Basic.State
      analysis.profile.factor.polynomial :=
  leaf.classification.eventState leaf.countNonzero

/-- The profile partition's classification retains the original leaf cell exactly. -/
theorem classification_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) :
    leaf.classification.cell = leaf.cell :=
  analysis.partition.classify_cell leaf.cell leaf.member

/-- The profiled event state uses the exact original retained leaf. -/
theorem state_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) : leaf.state.cell = leaf.cell :=
  leaf.classification_cell

/-- The retained profiled event leaf refines the original bounded chart interval. -/
theorem cell_refines_chart
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) :
    leaf.cell.interval.Refines chart.cell.interval := by
  rw [← leaf.classification_cell]
  exact leaf.classification.refines
end ProfileEventLeaf
end Purelib.RootIsolation.Curve.Event.Profile.Basic

end

section
public section

/-!
# Original-polynomial residuals on condition-profile CCL events

A condition profile is a further finite factor of one squarefree curve-gcd
factor.  Its Sturm request directly bounds only that final profile factor.
This module multiplies through the displayed finite cofactors, then through
the two cleared curve coordinates, to recover a coefficient-computed bound
for the original Gaussian polynomial at every displayed affine point of the
requested profile cylinder.

All parameters and coefficients are constructive rationals.  The estimates
hold pointwise throughout a finite request interval and make no root
existence assertion.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Basic
/-- The original nonzero-count event leaf indexed by its retained condition-profile analysis. -/
abbrev SourcePersistentProfileResidualProfileEventLeafAlias
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileResidualSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis) :=
  Curve.Event.Profile.Basic.ProfileEventLeaf analysis

end Purelib.RootIsolation.Curve.Event.Profile.Basic

end

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Basic
/-- The retained profile's original nonzero-count event leaf with its exact partition membership. -/
abbrev SourcePersistentProfileRequestFamilyProfileEventLeafAlias
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    (analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis) :=
  Curve.Event.Profile.Basic.SourcePersistentProfileResidualProfileEventLeafAlias analysis

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Basic

end
