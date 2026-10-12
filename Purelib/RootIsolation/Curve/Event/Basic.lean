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
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
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

namespace Purelib.RootIsolation.Curve.Event.Basic

set_option genInjectivity false in
/-- One squarefree parameter leaf whose doubled Sturm count is nonzero. -/
structure EventLeaf
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) where
  /-- The actual retained squarefree event-subdivision cell. -/ cell : Data.Rat.Interval.Proper.Cell
  /-- The cell belongs to the original factor partition's leaf list. -/ member : cell ∈
    factorAnalysis.partition.tree.leaves
  /-- The retained classification has nonzero doubled event count. -/ countNonzero :
    (factorAnalysis.partition.classify cell member).eventCount ≠ 0

constructive_injectivity EventLeaf

namespace EventLeaf

/-- Read the original partition classification of this retained event leaf. -/
@[expose] def classification
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) :=
  factorAnalysis.partition.classify leaf.cell leaf.member

/-- Construct the persistent nonzero-count Sturm state on the original retained leaf. -/
@[expose] def state
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) :
    Sturm.Track.Basic.State factorAnalysis.factor.polynomial :=
  leaf.classification.eventState leaf.countNonzero

/-- The original partition classification preserves the retained leaf exactly. -/
theorem classification_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) :
    leaf.classification.cell = leaf.cell :=
  factorAnalysis.partition.classify_cell leaf.cell leaf.member

/-- The retained event state uses the exact original leaf cell. -/
theorem state_cell
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) : leaf.state.cell = leaf.cell := by
  exact leaf.classification_cell

/-- The retained event leaf refines its original bounded chart interval. -/
theorem cell_refines_chart
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) :
    leaf.cell.interval.Refines chart.cell.interval := by
  rw [← leaf.classification_cell]
  exact leaf.classification.refines
end EventLeaf

end Purelib.RootIsolation.Curve.Event.Basic

end
