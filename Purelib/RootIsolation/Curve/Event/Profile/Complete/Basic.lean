module
import Purelib.Data.Int.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.List.Attach
import Purelib.Data.List.FilterMap
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Data.Rat.Interval.Refinement
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
public import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Event.Resolution
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Data.Rat.Interval.Width
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.RootIsolation.Curve.Event.Partition (Subdivision)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (SourcePersistentProfileRequestFamilyProfileEventLeafAlias)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
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

/-- A finite subdivision depth making the original profile leaf width no larger than the requested positive accuracy. -/
def completeRequestDepth (leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis)
    (epsilon : Fraction.Rational) : Nat :=
  Approximation.Rational.Contraction.geometricDepth (Bounds.width leaf.cell.interval)
    epsilon

/-- Subdivide the original counted profile leaf at the depth chosen for the requested accuracy.

The returned finite subdivision retains its original Sturm factor and exact child-count accounting. -/
def completeRequestSubdivision (leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis)
    (epsilon : Fraction.Rational) :=
  Subdivision.build
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      chart.parameterization.curve box (completeRequestDepth leaf epsilon)
        leaf.cell

/-- Every child of the retained complete subdivision refines its original profile leaf. -/
theorem completeRequestCell_refines_leaf
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    cell.interval.Refines leaf.cell.interval :=
  Subdivision.build_leaf_refines
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      chart.parameterization.curve box (completeRequestDepth leaf epsilon)
        leaf.cell member

/-- Every child of the retained complete subdivision refines the original chart interval. -/
theorem completeRequestCell_refines_chart
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    cell.interval.Refines chart.cell.interval :=
  Data.Rat.Interval.Refinement.intervalRefines_trans
    (completeRequestCell_refines_leaf leaf epsilon member)
    leaf.cell_refines_chart

/-- Every child width meets the positive accuracy used to construct the complete subdivision. -/
theorem completeRequestCell_width_le
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (positive : 0 < epsilon) {cell : Cell}
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    (Bounds.width cell.interval) ≤ epsilon := by
  have geometric :=
    Approximation.Rational.Contraction.geometricDepth_sufficient
      (Bounds.width_nonneg leaf.cell.interval) positive
  exact
    (Subdivision.build_leaf_width_le
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        chart.parameterization.curve box (completeRequestDepth leaf epsilon)
          leaf.cell member).trans (by
            simpa only [completeRequestDepth] using geometric)

set_option genInjectivity false in
/-- A nonzero-count child of the original complete requested subdivision.

The record retains the actual cell, its membership in that subdivision and the nonzero original Sturm count. -/
structure CompleteRequestLeaf (leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis)
    (epsilon : Fraction.Rational) where
  /-- The actual child cell of the original requested subdivision. -/ cell : Cell
  /-- Membership of the retained cell in the original complete subdivision. -/ member : cell ∈
    (completeRequestSubdivision leaf epsilon).leaves
  /-- The original Sturm count of the retained child is nonzero. -/ countNonzero :
    Sturm.Count.Basic.sturmRootCount2
      analysis.profile.factor.polynomial cell.interval.lower
        cell.interval.upper ≠ 0

constructive_injectivity CompleteRequestLeaf

namespace CompleteRequestLeaf

/-- Read the original nonzero-count Sturm state carried by this retained subdivision child. -/
def state {leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
  Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) :
    Sturm.Track.Basic.State
      analysis.profile.factor.polynomial :=
  { cell := entry.cell
    countNonzero := entry.countNonzero }

/-- The retained requested child refines its original profile leaf. -/
theorem refines_leaf {leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis}
    {epsilon : Fraction.Rational} (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) :
    entry.cell.interval.Refines leaf.cell.interval :=
  Curve.Event.Profile.Complete.Basic.completeRequestCell_refines_leaf leaf epsilon entry.member

/-- The retained requested child refines the original chart interval. -/
theorem refines_chart {leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis}
    {epsilon : Fraction.Rational} (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) :
    entry.cell.interval.Refines chart.cell.interval :=
  Curve.Event.Profile.Complete.Basic.completeRequestCell_refines_chart leaf epsilon entry.member

/-- The retained requested child meets the original positive width request. -/
theorem width_le {leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis}
    {epsilon : Fraction.Rational} (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon)
    (positive : 0 < epsilon) : (Bounds.width entry.cell.interval) ≤ epsilon :=
  Curve.Event.Profile.Complete.Basic.completeRequestCell_width_le leaf epsilon positive entry.member
end CompleteRequestLeaf

/-- Retain an original subdivision child exactly when its displayed Sturm count is nonzero. -/
def completeRequestLeaf?
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (cell : Cell)
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    Option (CompleteRequestLeaf leaf epsilon) := by
  if countNonzero :
      Sturm.Count.Basic.sturmRootCount2
        analysis.profile.factor.polynomial cell.interval.lower
          cell.interval.upper ≠ 0 then
    exact some ⟨cell, member, countNonzero⟩
  else
    exact none

/-- Collect every nonzero-count child of the original requested profile subdivision. -/
def completeRequestFamily
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational) :
    List (CompleteRequestLeaf leaf epsilon) :=
  (completeRequestSubdivision leaf epsilon).leaves.attach.filterMap fun entry =>
    completeRequestLeaf? leaf epsilon entry.1 entry.2

/-- Testing a retained nonzero-count child returns that exact original record. -/
theorem completeRequestLeaf?_eq_some
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : CompleteRequestLeaf leaf epsilon) :
    completeRequestLeaf? leaf epsilon entry.cell entry.member = some entry := by
  simp only [completeRequestLeaf?,
    dif_pos entry.countNonzero, -eq_self, -iff_self]
  rfl

/-- Every retained nonzero-count child occurs in the computed requested family. -/
theorem mem_completeRequestFamily
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : CompleteRequestLeaf leaf epsilon) :
    entry ∈ completeRequestFamily leaf epsilon := by
  simp only [completeRequestFamily, -eq_self, -iff_self]
  apply Data.List.FilterMap.mem_filterMap.mpr
  refine ⟨⟨entry.cell, entry.member⟩, Data.List.Attach.mem_attach _ _, ?_⟩
  exact completeRequestLeaf?_eq_some entry

/-- A profile leaf with nonzero total count has a nonempty complete requested family.

The exact subdivision count sum forces at least one retained nonzero-count child. -/
theorem completeRequestFamily_nonempty
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational) :
    completeRequestFamily leaf epsilon ≠ [] := by
  intro familyEmpty
  let event := analysis.profile.factor.polynomial
  let cells := (completeRequestSubdivision leaf epsilon).leaves
  have allCountsZero : ∀ cell ∈ cells,
      Sturm.Count.Basic.cellCount2
        event cell = 0 := by
    intro cell member
    by_cases countNonzero :
        Sturm.Count.Basic.sturmRootCount2 event
          cell.interval.lower cell.interval.upper ≠ 0
    · let entry : CompleteRequestLeaf leaf epsilon :=
        { cell := cell
          member := by simpa only [cells] using member
          countNonzero := by simpa only [event] using countNonzero }
      have retained := mem_completeRequestFamily entry
      rw [familyEmpty] at retained
      exact (List.not_mem_nil retained).elim
    · unfold Sturm.Count.Basic.cellCount2
      exact Decidable.not_not.mp countNonzero
  have sumZeroOfAllZero : ∀ values : List Cell,
      (∀ cell ∈ values,
        Sturm.Count.Basic.cellCount2
          event cell = 0) →
      (values.map
        (Sturm.Count.Basic.cellCount2
          event)).sum = 0 := by
    intro values allZero
    induction values with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        rewrite [List.map_cons, List.sum_cons, allZero head List.mem_cons_self,
          Data.Int.Arithmetic.zero_add]
        exact inductionHypothesis fun cell member =>
          allZero cell (List.mem_cons_of_mem head member)
  have sumZero :
      (cells.map
        (Sturm.Count.Basic.cellCount2
          event)).sum = 0 :=
    sumZeroOfAllZero cells allCountsZero
  have parentCountNonzero :
      Sturm.Count.Basic.cellCount2
        event leaf.cell ≠ 0 := by
    simpa only [event,
      Sturm.Count.Basic.cellCount2,
      leaf.state_cell] using leaf.state.countNonzero
  apply parentCountNonzero
  rw [Subdivision.build_cellEventCount_sum
    event analysis.profile.factor.nonzero chart.parameterization.curve box
      (completeRequestDepth leaf epsilon) leaf.cell]
  simpa only [cells, event, completeRequestSubdivision] using sumZero

/-- Resolve the original Cauchy scan on a retained requested profile child.

The child inherits its original factor, nonzero Sturm count and common width bound, supplying the finite
event-separation guarantee. -/
def completeRequestResolution
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (cell : Cell)
    (member : cell ∈ (completeRequestSubdivision leaf epsilon).leaves) :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      cell.interval := by
  apply
    Sturm.Event.polynomialEventResolutionOfBounds
      analysis.profile.factor.polynomial chart.cell cell
  · exact completeRequestCell_refines_chart leaf epsilon member
  · have childLeaf := completeRequestCell_refines_leaf leaf epsilon member
    have childWidth : (Bounds.width cell.interval) ≤ (Bounds.width
      leaf.cell.interval) :=
      Fraction.Order.Arithmetic.sub_le_sub_direct childLeaf.2 childLeaf.1
    have leafWidthSmall : (Bounds.width leaf.cell.interval) <
        Curve.Event.Partition.Squarefree.squarefreeLeafWidth
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact childWidth.trans_lt
      (leafWidthSmall.trans_le
        ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell).trans
          (Curve.Event.Partition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial chart.parameterization.curve
              box chart.cell)))

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic

end
