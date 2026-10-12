module
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Chart (SquarefreeFactorAnalysis)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite event families for one CCL boundary

An unresolved Hermitian boundary can have two bounded rational charts.  The
owner calculation must therefore retain the nonzero events of every chart,
not merely the first nonconstant analysis.  This module flattens those
heterogeneous chart-local families into one finite boundary family.

The coverage theorem is pointwise and finite: any displayed rational
polynomial root on the unresolved boundary is located in one explicit member
of that computed family.  No root set or completed parameter is introduced.
-/

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev SourcePersistentBoundaryEventsSquarefreeFactorAnalysisAlias :=
  SquarefreeFactorAnalysis
end Purelib.RootIsolation.CCL.Boundary.Charts

end

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

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias
  :=
  SquarefreeFactorAnalysis
/-- The original condition-profile analysis indexed by its retained squarefree factor and explicit condition list. -/
abbrev SourcePersistentConditionProfilesProfileAnalysisAlias
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
      gcdDegreePositive)
    (conditions : List
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial :=
        Curve.Box.profiledConditionPolynomials
          chart.parameterization.curve box) :=
  Curve.Chart.ConditionProfileAnalysis factorAnalysis
    conditions

end Purelib.RootIsolation.CCL.Boundary.Charts

end

section
@[expose] public section

/-!
# Persistent projective shrinking of nonzero CCL curve events

Every nonconstant curve analysis has already been split into squarefree
coordinate factors and an aligned finite partition.  This module extracts the
nonzero-count leaves as explicit finite event records.  Each record carries
the existing central-third Sturm transducer and, simultaneously, a homogeneous
projective image bound for its rational boundary chart.

The homogeneous estimate remains valid across an affine pole.  It is therefore
combined with each chart's positive homogeneous-weight lower bound to obtain
the genuine finite `chi^2` shrinking fact needed to couple a narrowing
parameter event to a narrowing winding box without choosing a completed
parameter or root.
-/

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias :=
  SquarefreeFactorAnalysis

end Purelib.RootIsolation.CCL.Boundary.Charts

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

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev
  SourcePersistentProfileBoundaryEventsSquarefreeFactorAnalysisAlias :=
  SquarefreeFactorAnalysis
end Purelib.RootIsolation.CCL.Boundary.Charts

end

section
@[expose] public section

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

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev SourcePersistentProfileResidualSquarefreeFactorAnalysisAlias :=
  SquarefreeFactorAnalysis
/-- The original condition-profile analysis with the retained chart's default box-condition polynomials. -/
abbrev SourcePersistentProfileResidualProfileAnalysisAlias
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentProfileResidualSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) :=
  SourcePersistentConditionProfilesProfileAnalysisAlias
    factorAnalysis

end Purelib.RootIsolation.CCL.Boundary.Charts

end

section
@[expose] public section

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

namespace Purelib.RootIsolation.CCL.Boundary.Charts
/-- The original squarefree curve-factor analysis, retaining its chart, source polynomial, membership and aligned event
partition. -/
abbrev
  SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias :=
  SquarefreeFactorAnalysis
/-- The retained factor's original default box-condition profile analysis. -/
abbrev SourcePersistentProfileRequestFamilyProfileAnalysisAlias
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive) :=
  SourcePersistentProfileResidualProfileAnalysisAlias factorAnalysis

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.CCL.Boundary.Charts

end
