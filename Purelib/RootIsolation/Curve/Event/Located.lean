module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
public import Purelib.RootIsolation.Curve.Event.Family
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Decomposition
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Event.Factor
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event.Family (EventEntry)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Curve.Event.Located

namespace LocatedSquarefreeCurveRoot

/-- Repackage the factor selected by the finite first-zero scan as the
factor-analysis record consumed by the persistent event API. -/
@[reducible] def factorAnalysis
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data gcdDegreePositive
      where
  factor := located.factor
  member := located.factorMember
  conditionProfiles :=
    Dense.Rational.Factorization.classifyConditions located.factor
      (Curve.Box.profiledConditionPolynomials
        chart.parameterization.curve box)
  partition := located.partition

/-- Every displayed rational curve root is assigned to a nonzero squarefree
event leaf.  This is the pointwise coverage theorem for the finite event
enumeration; it introduces neither a completed parameter nor a root set. -/
def eventLeaf
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    Curve.Event.Basic.EventLeaf (factorAnalysis located) := by
  have parameterInside :
      located.location.classification.cell.interval.Contains parameter := by
    rw [located.location.classification_cell]
    exact located.location.contains
  have countNonzero :=
    located.location.classification.eventCount_ne_zero_of_root parameter
      parameterInside located.factorZero
  exact
    { cell := located.location.leaf
      member := located.location.member
      countNonzero := by
        rw [← located.location.classification_eq]
        exact countNonzero }

end LocatedSquarefreeCurveRoot

/-- The selected original squarefree root leaf belongs to its factor analysis's computed event list. -/
theorem LocatedSquarefreeCurveRoot.eventLeaf_mem
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    LocatedSquarefreeCurveRoot.eventLeaf located ∈
      Curve.Event.Family.eventLeaves (LocatedSquarefreeCurveRoot.factorAnalysis located) :=
  Curve.Event.Family.mem_eventLeaves (LocatedSquarefreeCurveRoot.eventLeaf located)

/-- The factor selected by the first-zero scan is one of the factor analyses
computed by the chart analyzer.  Retaining this membership is essential: it
connects pointwise root coverage to the executable event-family list. -/
theorem LocatedSquarefreeCurveRoot.factorAnalysis_mem
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    LocatedSquarefreeCurveRoot.factorAnalysis located ∈
      Curve.Chart.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive := by
  simp only [Curve.Chart.analyzeSquarefreeFactors, -eq_self, -iff_self]
  apply Data.List.Map.mem_map.mpr
  refine ⟨⟨located.factor, located.factorMember⟩,
    Data.List.Attach.mem_attach _ _, ?_⟩
  cases located with
  | mk factor factorMember factorZero partition partition_eq location
      boxConditions =>
      simp only [LocatedSquarefreeCurveRoot.factorAnalysis]
      cases partition_eq
      rfl

/-- Every displayed rational polynomial root on a non-pole part of an
executed chart is represented by an entry of that chart's complete computed
event family. -/
theorem LocatedSquarefreeCurveRoot.eventLeaf_mem_completeFamily
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      Curve.Event.Family.eventFamily
        (Curve.Chart.analyzeSquarefreeFactors p box chart
          data gcdDegreePositive) :=
  Curve.Event.Family.mem_eventFamily
    (LocatedSquarefreeCurveRoot.factorAnalysis_mem located)
    (LocatedSquarefreeCurveRoot.eventLeaf located)

/-- Transfer pointwise event coverage through the completeness equality
carried by an executed `BoundedAnalysis.events` constructor. -/
theorem LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
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
    (factors_eq : factors =
      Curve.Chart.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive)
    {parameter : Fraction.Rational}
    (located : Curve.Chart.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      Curve.Event.Family.eventFamily factors := by
  rw [factors_eq]
  exact LocatedSquarefreeCurveRoot.eventLeaf_mem_completeFamily located

set_option genInjectivity false in
/-- Executable location of a displayed polynomial root in the complete
finite nonzero-event family of one nonconstant chart analysis. -/
structure LocatedEvent
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive))
    (parameter : Fraction.Rational) where
  /-- The original located squarefree factor and leaf containing the supplied rational parameter. -/ located :
    Curve.Chart.LocatedSquarefreeCurveRoot
    p box chart data gcdDegreePositive parameter
  /-- The selected original factor-and-leaf pair occurs in the retained complete event family. -/ member :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      Curve.Event.Family.eventFamily factors

constructive_injectivity LocatedEvent

/-- Locate a supplied rational polynomial root in the original chart event family.

The finite factor scan and Sturm locator retain the selected factor, its nonzero-count leaf and membership in the exact
supplied analyzer output. -/
def locateEvent
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive))
    (factors_eq : factors =
      Curve.Chart.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive)
    (parameter : Fraction.Rational)
    (parameterInside : chart.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (root : p.eval (chart.parameterization.curve.point parameter) = 0)
    (inside : box.Contains (chart.parameterization.curve.point parameter)) :
    LocatedEvent chart data gcdDegreePositive factors parameter := by
  let located := Curve.Chart.locateSquarefreeCurveRoot
    p box chart data gcdDegreePositive parameter parameterInside
      denominatorNonzero root inside
  exact
    { located := located
      member :=
        LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
          factors_eq located }

end Purelib.RootIsolation.Curve.Event.Located

end
