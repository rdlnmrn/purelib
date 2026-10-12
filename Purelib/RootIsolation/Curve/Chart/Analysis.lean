module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.Curve.Clearance.Global
public import Purelib.RootIsolation.Curve.Clearance.Residual
import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Curve.Event.Factor
public import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Decomposition
import Purelib.Polynomial.Dense.Rational.Squarefree.Locate
import Purelib.RationalFunctions.Curve.Basic

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Event (Nontrivial)
open Purelib.RootIsolation.Curve.Event.Partition.Squarefree (SquarefreeEventPartition)

public section

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.RootIsolation.Curve.Chart

set_option genInjectivity false in
/-- One squarefree occurrence of the curve-gcd parameter polynomial, paired
with its aligned root/box event partition. -/
structure SquarefreeFactorAnalysis
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree) where
  /-- The original squarefree factor occurrence under analysis. -/ factor : Dense.Rational.Squarefree.Factor
  /-- The factor belongs to the original curve-event decomposition. -/ member : factor ∈
    (Curve.Event.eventDecomposition data
      gcdDegreePositive).factors
  /-- The retained profiles of all original box-condition polynomials on this exact factor. -/ conditionProfiles :
    Dense.Rational.Factorization.ConditionProfiles factor
      (Curve.Box.profiledConditionPolynomials
        chart.parameterization.curve box)
  /-- The aligned squarefree event partition for the retained factor on the original chart cell. -/ partition :
    SquarefreeEventPartition
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell

constructive_injectivity SquarefreeFactorAnalysis

/-- Analyze every retained squarefree occurrence of the original curve-gcd polynomial.

Each attached factor keeps its original membership, complete box-condition profiles and an aligned squarefree event
partition on the same chart cell. -/
@[expose] def analyzeSquarefreeFactors
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree) :
    List (SquarefreeFactorAnalysis p box chart data gcdDegreePositive) :=
  (Curve.Event.eventDecomposition data
    gcdDegreePositive).factors.attach.map fun entry =>
      { factor := entry.1
        member := entry.2
        conditionProfiles :=
          Dense.Rational.Factorization.classifyConditions entry.1
            (Curve.Box.profiledConditionPolynomials
              chart.parameterization.curve box)
        partition :=
          Curve.Event.Partition.Squarefree.classifySquarefreeEvents
            entry.1.polynomial entry.1.nonzero entry.1.squarefree
            chart.parameterization.curve box chart.cell }

set_option genInjectivity false in
/-- One fully condition-profiled squarefree divisor of an original curve-gcd
factor, paired with a fresh aligned event partition for that divisor. -/
structure ConditionProfileAnalysis
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (conditions : List
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial :=
        Curve.Box.profiledConditionPolynomials
          chart.parameterization.curve box) where
  /-- The original condition-profiled squarefree divisor of the retained curve factor. -/ profile :
    Dense.Rational.Factorization.ConditionProfile
    factorAnalysis.factor conditions
  /-- The aligned event partition for this exact profiled divisor on the original chart cell. -/ partition :
    SquarefreeEventPartition
      profile.factor.polynomial profile.factor.nonzero
        profile.factor.squarefree chart.parameterization.curve box chart.cell

constructive_injectivity ConditionProfileAnalysis

/-- Execute aligned event partitions for every equality/apart condition
profile of one original squarefree curve factor. -/
@[expose] def analyzeConditionProfiles
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    List (ConditionProfileAnalysis factorAnalysis) :=
  factorAnalysis.conditionProfiles.profiles.attach.map fun entry =>
    { profile := entry.1
      partition :=
        Curve.Event.Partition.Squarefree.classifySquarefreeEvents
          entry.1.factor.polynomial entry.1.factor.nonzero
            entry.1.factor.squarefree chart.parameterization.curve box
              chart.cell }

set_option genInjectivity false in
/-- Executed finite curve analysis, including a concrete Sturm event
partition on the chart cell in the nonconstant-gcd case. -/
inductive BoundedAnalysis
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form) where
  /-- Both original substituted coordinate polynomials vanish identically on the chart curve. -/ | identicallyZero
      (realZero :
        (Curve.Substitution.realPolynomial p
          chart.parameterization.curve).isZero = true)
      (imaginaryZero :
        (Curve.Substitution.imaginaryPolynomial p
          chart.parameterization.curve).isZero = true)
  /-- The original curve is globally root-free, with a retained residual clearance on the chart interval. -/ | clear
      (certificate : Curve.Clearance.Global.GlobalClear p
        chart.parameterization.curve)
      (residual : Curve.Clearance.Residual.Certificate p
        chart.parameterization.curve chart.cell.interval)
  /-- The nonconstant original curve gcd has its actual squarefree factor analyses and their defining construction
    equality. -/ | events
      (data : Nontrivial p
        chart.parameterization.curve)
      (gcdDegreePositive : 0 <
        (Curve.Substitution.gcdPolynomial p
          chart.parameterization.curve).natDegree)
      (squarefreeFactors :
        List (SquarefreeFactorAnalysis p box chart data gcdDegreePositive))
      (factors_eq : squarefreeFactors =
        analyzeSquarefreeFactors p box chart data gcdDegreePositive)

constructive_injectivity BoundedAnalysis

set_option genInjectivity false in
/-- A displayed curve root located in the aligned partition of one
squarefree parameter factor.  This is the repeated-factor-safe event
interface used by the owner layer. -/
structure LocatedSquarefreeCurveRoot
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (parameter : Fraction.Rational) where
  /-- The original squarefree curve-event factor selected at the displayed root parameter. -/ factor :
    Dense.Rational.Squarefree.Factor
  /-- The selected factor belongs to the original event decomposition. -/ factorMember : factor ∈
    (Curve.Event.eventDecomposition data
      gcdDegreePositive).factors
  /-- The selected original factor vanishes at the displayed parameter. -/ factorZero : factor.polynomial.eval parameter
    = 0
  /-- The retained aligned event partition for this exact selected factor. -/ partition :
    SquarefreeEventPartition
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell
  /-- The retained partition equals the original squarefree event-classification construction. -/ partition_eq :
    partition =
    Curve.Event.Partition.Squarefree.classifySquarefreeEvents
      factor.polynomial factor.nonzero factor.squarefree
        chart.parameterization.curve box chart.cell
  /-- The displayed parameter's actual location in the retained factor partition. -/ location :
    Curve.Event.Partition.Squarefree.LocatedSquarefreeParameter
      partition parameter
  /-- The original curve point satisfies the retained box's condition polynomials. -/ boxConditions : Curve.Box.Holds
    chart.parameterization.curve box parameter

constructive_injectivity LocatedSquarefreeCurveRoot

/-- Execute the finite first-zero-factor scan and locate the result in its
already coefficient-bounded aligned partition. -/
@[expose] def locateSquarefreeCurveRoot
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form)
    (data : Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (parameter : Fraction.Rational)
    (parameterInside : chart.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (root : p.eval (chart.parameterization.curve.point parameter) = 0)
    (inside : box.Contains (chart.parameterization.curve.point parameter)) :
    LocatedSquarefreeCurveRoot p box chart data gcdDegreePositive parameter := by
  let locatedFactor := Curve.Event.locateFactorRoot data
    gcdDegreePositive parameter denominatorNonzero root
  let partition :=
    Curve.Event.Partition.Squarefree.classifySquarefreeEvents
      locatedFactor.factor.polynomial locatedFactor.factor.nonzero
      locatedFactor.factor.squarefree
      chart.parameterization.curve box chart.cell
  exact
    { factor := locatedFactor.factor
      factorMember := locatedFactor.member
      factorZero := locatedFactor.zero
      partition := partition
      partition_eq := rfl
      location := partition.locate parameter parameterInside
      boxConditions :=
        (Curve.Box.holds_iff_contains
          chart.parameterization.curve box parameter denominatorNonzero).2
            inside }

/-- Analyze one bounded chart and execute its event partition immediately. -/
@[expose] def analyzeChart
    (p : CoefficientPolynomial) (box : Box) {form :
      HermitianForm}
    (chart : BoundedChart form) : BoundedAnalysis p box chart := by
  match Curve.Event.analyze p chart.parameterization.curve with
  | .identicallyZero realZero imaginaryZero =>
      exact .identicallyZero realZero imaginaryZero
  | .clear certificate =>
      exact .clear certificate
        (Curve.Clearance.Residual.certificate certificate
          chart.cell.interval)
  | .events data degreePositive =>
      exact .events data degreePositive
        (analyzeSquarefreeFactors p box chart data degreePositive) rfl

/-- Analyze every member of the finite bounded chart family. -/
@[expose] def analyzeCharts
    (p : CoefficientPolynomial) {reference :
      LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {form :
      HermitianForm}
    (source : Geometry.Projective.Hermitian.Chart.CurveSource reference form) (box : Box)
    (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin) :
    List (Sigma fun chart : BoundedChart form => BoundedAnalysis p box
      chart) :=
  (Geometry.Projective.Hermitian.Chart.charts source box denominatorMargin marginPositive).map fun chart =>
    ⟨chart, analyzeChart p box chart⟩
end Purelib.RootIsolation.Curve.Chart

end
