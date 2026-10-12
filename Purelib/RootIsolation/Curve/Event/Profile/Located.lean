module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Attach
public import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Family
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Locate
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Located

set_option genInjectivity false in
/-- A displayed rational root of an original squarefree factor, assigned by
finite scans to one exact condition profile and one nonzero profile event. -/
structure LocatedProfileEvent
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive)
    (parameter : Fraction.Rational) where
  /-- The actual condition-profile analysis and event leaf selected by the original finite scans. -/ entry :
    Curve.Event.Profile.Family.ProfileEventEntry factorAnalysis
  /-- The selected profile event belongs to the original computed profile-event family. -/ member : entry ∈
    Curve.Event.Profile.Family.profileEventFamily factorAnalysis
  /-- The supplied rational parameter is a zero of the selected original profile factor. -/ profileZero :
    entry.1.profile.factor.polynomial.eval parameter = 0
  /-- The selected original profile-event interval contains the supplied rational parameter. -/ contains :
    entry.2.cell.interval.Contains parameter

constructive_injectivity LocatedProfileEvent

/-- Execute the profile scan and the aligned Sturm-tree locator.  Thus every
displayed rational root of the original squarefree factor belongs to an
entry of the complete profile-event family. -/
def locateProfileEvent
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive)
    (parameter : Fraction.Rational)
    (inside : chart.cell.interval.Contains parameter)
    (factorZero : factorAnalysis.factor.polynomial.eval parameter = 0) :
    LocatedProfileEvent factorAnalysis parameter := by
  let locatedProfile := factorAnalysis.conditionProfiles.locateRoot parameter
    factorZero
  let analysis : CCL.Boundary.Charts.SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis :=
    { profile := locatedProfile.profile
      partition :=
        Curve.Event.Partition.Squarefree.classifySquarefreeEvents
          locatedProfile.profile.factor.polynomial
            locatedProfile.profile.factor.nonzero
              locatedProfile.profile.factor.squarefree
                chart.parameterization.curve box chart.cell }
  have analysisMember : analysis ∈
      Curve.Chart.analyzeConditionProfiles
        factorAnalysis := by
    simp only [Curve.Chart.analyzeConditionProfiles, -eq_self, -iff_self]
    apply Data.List.Map.mem_map.mpr
    exact ⟨⟨locatedProfile.profile, locatedProfile.member⟩,
      Data.List.Attach.mem_attach _ _, rfl⟩
  let location := analysis.partition.locate parameter inside
  have parameterInside :
      location.classification.cell.interval.Contains parameter := by
    rw [location.classification_cell]
    exact location.contains
  have countNonzero :=
    location.classification.eventCount_ne_zero_of_root parameter
      parameterInside locatedProfile.zero
  let leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis :=
    { cell := location.leaf
      member := location.member
      countNonzero := by
        rw [← location.classification_eq]
        exact countNonzero }
  exact
    { entry := ⟨analysis, leaf⟩
      member := Curve.Event.Profile.Family.mem_profileEventFamily analysisMember leaf
      profileZero := locatedProfile.zero
      contains := location.contains }

end Purelib.RootIsolation.Curve.Event.Profile.Located

end
