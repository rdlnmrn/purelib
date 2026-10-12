module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Subdivision
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Orientation.Basic
import Purelib.RootIsolation.Sturm.Orientation.Event
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (SourcePersistentProfileRequestFamilyProfileEventLeafAlias)

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.RootIsolation.Curve.Event.Profile.Complete.Located
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

/-- Every supplied displayed rational profile zero is retained as a nonzero
child of the complete requested subdivision. -/
theorem completeRequestCell_countNonzero_of_zero
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon :
      Fraction.Rational)
    (cell : Data.Rat.Interval.Proper.Cell)
    (member : cell ∈ (Curve.Event.Profile.Complete.Basic.completeRequestSubdivision leaf epsilon).leaves)
    (parameter : Fraction.Rational) (inside : cell.interval.Contains parameter)
    (zero : analysis.profile.factor.polynomial.eval parameter = 0) :
    Sturm.Count.Basic.sturmRootCount2
      analysis.profile.factor.polynomial cell.interval.lower
        cell.interval.upper ≠ 0 := by
  have childLeaf := Curve.Event.Profile.Complete.Basic.completeRequestCell_refines_leaf leaf epsilon member
  have childWidth : (Bounds.width cell.interval) ≤ (Bounds.width
    leaf.cell.interval) :=
    Fraction.Order.Arithmetic.sub_le_sub_direct childLeaf.2 childLeaf.1
  have leafWidthSmall : (Bounds.width leaf.cell.interval) <
      Curve.Event.Partition.Squarefree.squarefreeLeafWidth
        analysis.profile.factor.polynomial analysis.profile.factor.squarefree
          chart.parameterization.curve box chart.cell := by
    simpa only [leaf.classification_cell] using
      leaf.classification.widthSmall
  have orientationWidth : (Bounds.width cell.interval) <
      Sturm.Orientation.Basic.rootOrientationWidth
        analysis.profile.factor.polynomial
          analysis.profile.factor.squarefree chart.cell.interval :=
    childWidth.trans_lt
      (leafWidthSmall.trans_le
        (Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_orientation
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell))
  exact Sturm.Orientation.Event.sturmRootCount2_ne_zero_of_root
    analysis.profile.factor.polynomial analysis.profile.factor.squarefree
      (Curve.Event.Profile.Complete.Basic.completeRequestCell_refines_chart leaf epsilon member) cell.proper
      orientationWidth (Curve.Event.Profile.Complete.Basic.completeRequestResolution leaf epsilon cell member)
      parameter inside zero

set_option genInjectivity false in
/-- A supplied displayed rational profile zero, located in one retained
member of the complete requested family. -/
structure LocatedCompleteRequestZero
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon
      parameter : Fraction.Rational) where
  /-- The actual nonzero-count child selected from the complete requested subdivision. -/ entry :
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon
  /-- The selected child belongs to the original complete requested family. -/ member : entry ∈
    Curve.Event.Profile.Complete.Basic.completeRequestFamily leaf epsilon
  /-- The selected original child interval contains the supplied rational parameter. -/ contains :
    entry.cell.interval.Contains parameter
  /-- The supplied rational parameter is a zero of the original profile factor. -/ zero :
    analysis.profile.factor.polynomial.eval parameter = 0

constructive_injectivity LocatedCompleteRequestZero

/-- Execute the complete-tree locator and retain the child's directly proved
nonzero count.  This direction starts from a supplied rational zero. -/
def locateCompleteRequestZero
    (leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis) (epsilon
      parameter : Fraction.Rational)
    (inside : leaf.cell.interval.Contains parameter)
    (zero : analysis.profile.factor.polynomial.eval parameter = 0) :
    LocatedCompleteRequestZero leaf epsilon parameter := by
  let found :=
    Curve.Event.Partition.Subdivision.locateBuild
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        chart.parameterization.curve box (Curve.Event.Profile.Complete.Basic.completeRequestDepth leaf epsilon)
          leaf.cell parameter inside
  have countNonzero := completeRequestCell_countNonzero_of_zero leaf epsilon
    found.leaf found.member parameter found.contains zero
  let entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon :=
    { cell := found.leaf
      member := found.member
      countNonzero := countNonzero }
  exact
    { entry := entry
      member := Curve.Event.Profile.Complete.Basic.mem_completeRequestFamily entry
      contains := found.contains
      zero := zero }

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete.Located

end
