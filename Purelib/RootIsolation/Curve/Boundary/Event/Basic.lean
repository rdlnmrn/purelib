module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
public import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Curve.Event.Family
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Curve.Event.Basic

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Curve.Boundary.Event.Basic

set_option genInjectivity false in
/-- One chart-local event together with its exact provenance in the complete
analysis list of the dispatched boundary. -/
structure BoundaryEventEntry
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) where
  /-- The actual bounded chart of the original boundary form. -/ chart :
    Geometry.Projective.Hermitian.Chart.BoundedChart atom.form
  /-- The retained nontrivial polynomial substitution on this original chart. -/ data : Curve.Event.Nontrivial p
    chart.parameterization.curve
  /-- The original chart-substitution gcd has positive degree. -/ gcdDegreePositive : 0 <
    (Curve.Substitution.gcdPolynomial p
      chart.parameterization.curve).natDegree
  /-- The retained squarefree factor analyses for this exact chart and boundary box. -/ factors : List
    (CCL.Boundary.Charts.SourcePersistentBoundaryEventsSquarefreeFactorAnalysisAlias p current chart data
    gcdDegreePositive)
  /-- The retained factor list equals the original chart analyzer output. -/ factors_eq : factors =
    Curve.Chart.analyzeSquarefreeFactors p current chart
      data gcdDegreePositive
  /-- This exact chart analysis occurs in the original dispatched boundary analysis list. -/ analysisMember :
    (⟨chart, Curve.Chart.BoundedAnalysis.events data
      gcdDegreePositive factors factors_eq⟩ :
      Sigma fun chart : Geometry.Projective.Hermitian.Chart.BoundedChart atom.form =>
        Curve.Chart.BoundedAnalysis p current chart) ∈
      boundary.analyses
  /-- The original factor analysis and nonzero-count event leaf selected on this chart. -/ event :
    Curve.Event.Family.SourcePersistentBoundaryEventsEventEntryAlias (p := p) (box := current) (form := atom.form)
    (chart := chart) (data := data)
      (gcdDegreePositive := gcdDegreePositive)
  /-- The retained event occurs in the complete event family of the retained factor list. -/ eventMember : event ∈
    Curve.Event.Family.eventFamily factors

constructive_injectivity BoundaryEventEntry

end Purelib.RootIsolation.Curve.Boundary.Event.Basic

end

section
public section

/-!
# Complete condition-profile event families for one CCL boundary

This module lifts the exact box-condition profiles through the already
complete finite boundary-event family.  It also transports the existing
pointwise locator in the safe direction: a supplied displayed rational
polynomial root is assigned to a computed profile event.  No nonzero Sturm
count is converted into a root-existence statement.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Basic
/-- The original boundary event entry retained for condition-profile refinement. -/
abbrev
  SourcePersistentProfileBoundaryEventsBoundaryEventEntryAlias
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  BoundaryEventEntry boundary
end Purelib.RootIsolation.Curve.Boundary.Event.Basic

end

section
public section

/-!
# Finite ownership of persistent CCL events

One boundary-event request must be compared with a complete finite family of
pairwise-separated winding regions, not just one selected pair.  This module
computes a single positive rational request width below every pair-specific
width and proves uniqueness of any explicit region meeting at that request.

The construction folds finite lists of displayed rationals.  It introduces
no root set, completed point, infinite minimum, or choice operation.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Basic
/-- The original boundary event entry retained with its chart and complete-family provenance. -/
abbrev SourcePersistentRegionOwnershipBoundaryEventEntryAlias
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) :=
  BoundaryEventEntry boundary
end Purelib.RootIsolation.Curve.Boundary.Event.Basic

end
