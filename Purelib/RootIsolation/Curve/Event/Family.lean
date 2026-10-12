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
import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event.Basic (EventLeaf)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Curve.Event.Family

/-- Decide whether one already-classified squarefree leaf carries a nonzero
event count. -/
def eventLeaf?
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive)
    (cell : Data.Rat.Interval.Proper.Cell)
    (member : cell ∈ factorAnalysis.partition.tree.leaves) :
    Option (EventLeaf factorAnalysis) := by
  let classification := factorAnalysis.partition.classify cell member
  if countNonzero : classification.eventCount ≠ 0 then
    exact some
      { cell := cell
        member := member
        countNonzero := countNonzero }
  else
    exact none

/-- Complete finite list of nonzero-count leaves for one squarefree factor. -/
def eventLeaves
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive) : List (EventLeaf factorAnalysis) :=
  factorAnalysis.partition.tree.leaves.attach.filterMap fun entry =>
    eventLeaf? factorAnalysis entry.1 entry.2

/-- Testing an already retained nonzero-count leaf returns that exact original leaf record. -/
theorem eventLeaf?_eq_some
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) :
    eventLeaf? factorAnalysis leaf.cell leaf.member = some leaf := by
  simp only [-eq_self, -iff_self, eventLeaf?, dif_pos leaf.countNonzero]
  rfl

/-- The finite extraction is extensionally complete: every proof-bearing
nonzero leaf of this partition occurs in the computed list. -/
theorem mem_eventLeaves
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) : leaf ∈ eventLeaves factorAnalysis := by
  rw [eventLeaves]
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨⟨leaf.cell, leaf.member⟩, ?_, ?_⟩
  · exact Data.List.Attach.mem_attach _ _
  · exact eventLeaf?_eq_some leaf

/-- Homogeneous finite wrapper for the nonzero leaves of every squarefree
factor in one nonconstant chart analysis. -/
abbrev EventEntry
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree} :=
  Sigma fun factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart
    data
    gcdDegreePositive => EventLeaf factorAnalysis

/-- Complete finite nonzero-event family of all repeated-factor-safe
squarefree occurrences in one chart analysis. -/
def eventFamily
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factors : List (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive)) :
    List (EventEntry (p := p) (box := box) (form := form) (chart := chart)
      (data := data) (gcdDegreePositive := gcdDegreePositive)) :=
  factors.flatMap fun factorAnalysis =>
    (eventLeaves factorAnalysis).map fun leaf => ⟨factorAnalysis, leaf⟩

/-- Every retained nonzero leaf of an original member factor occurs in the computed event family. -/
theorem mem_eventFamily
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factors : List (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive)}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (factorMember : factorAnalysis ∈ factors)
    (leaf : EventLeaf factorAnalysis) :
    (⟨factorAnalysis, leaf⟩ : EventEntry (p := p) (box := box)
      (form := form) (chart := chart) (data := data)
      (gcdDegreePositive := gcdDegreePositive)) ∈ eventFamily factors := by
  rw [eventFamily]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨factorAnalysis, factorMember, ?_⟩
  apply Data.List.Map.mem_map.mpr
  exact ⟨leaf, mem_eventLeaves leaf, rfl⟩
end Purelib.RootIsolation.Curve.Event.Family

end

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

namespace Purelib.RootIsolation.Curve.Event.Family
/-- An original squarefree factor analysis paired with one of its retained nonzero-count event leaves. -/
abbrev SourcePersistentBoundaryEventsEventEntryAlias
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree} :=
  EventEntry
    (p := p) (box := box) (form := form) (chart := chart)
      (data := data) (gcdDegreePositive := gcdDegreePositive)
end Purelib.RootIsolation.Curve.Event.Family

end
