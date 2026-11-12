module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences.Preparations.Values
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial
import Purelib.Integration.Program.Comparison

/-! # Actual polynomial value agreement with a retained positional jet

The polynomial and source floors are independent. Their original paid
programme comparison is composed with the completed jet's exact scalar
readback. A supplied actual jet and its original whole constructor equation
keep the runtime comparison on that same cached programme; reducing the
factory only proves the scalar readback.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Compare one actual retained polynomial value with the same supplied positional jet's value output.

Only the original whole jet factory equation is supplied. The polynomial
bridge and exact completion/source sample readbacks derive the operational
comparison internally. Both complete programme owners and independent
preparation floors remain unchanged; no final closeness is a premise.
-/
def valueEquivalent {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} (spine : PolynomialSpine walk)
    {polynomialFloor : Nat} {coordinate : Fin 2} (retained : PolynomialValue walk spine polynomialFloor coordinate)
    (sourceFloor rootStage : Nat)
    (sources : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      spine.covered sourceFloor (CellEndpoints.Targets.build spine.chain.path index))
    (nonempty : spine.parents ≠ []) (actual : SynchronizedPeriodJet frame)
    (factory : actual = (spine.occurrenceJet sourceFloor rootStage sources nonempty).1) :
    NamedEquivalent retained.2.val.integral.output.name (actual.value coordinate).integral.output.name := by
  have polynomialFactory := (congrArg (fun program => program.integral) retained.2.property).trans
    (PolynomialWork.fromWork_integral spine.chain retained.1
      (Jets.Specification.valueSpecification_denominatorPairs parameter coordinate))
  have first := PreparedParents.polynomial_outputEquivalent (parameter := parameter) (frame := frame)
    (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1)
    (sourceFloor := sourceFloor) (polynomialFloor := polynomialFloor)
    spine.covered spine.chain coordinate retained.1 retained.1.models sources retained.2.val.integral
    polynomialFactory
  have last := Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_eq
    (PreparedParents.certified spine.covered spine.chain sources
      (Jets.Specification.Table.valueIndex coordinate)).integral (actual.value coordinate).integral (by
      intro stage
      have actualReadback := congrArg (fun jet : SynchronizedPeriodJet frame =>
        ((jet.value coordinate).integral.model stage).integralSample) factory
      have constructorReadback := congrArg (fun bundle : (jet : SynchronizedPeriodJet frame) ×
          Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet =>
        ((bundle.1.value coordinate).integral.model stage).integralSample)
        (spine.occurrenceJet_factory sourceFloor rootStage sources nonempty)
      have original := PreparedParents.StageAttempt.OccurrenceCompletion.ofPreparations_value_sample
        (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
        (count := 1) (floor := sourceFloor) spine.covered spine.chain sources rootStage spine.roots nonempty
        coordinate stage
      exact (actualReadback.trans (constructorReadback.trans original)).symm)
  exact first.trans last

/-- Retain one positional jet and both internally derived original polynomial value comparisons.

The original polynomial pair and its old holomorphic input remain supplied
caches. The positional jet constructor executes once in this factory; both
comparisons consume that same actual jet. Programme callbacks remain the
original independent callbacks, without a memoization claim.
-/
def attach {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {polynomialFloor : Nat}
    (values : PolynomialValues walk polynomialFloor) (sourceFloor rootStage : Nat)
    (sources : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path index))
    (nonempty : values.1.parents ≠ []) :
    (actual : (jet : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate jet × Jets.PicardFuchs.PicardFuchsCertificate jet) ×
    NamedEquivalent values.2.1.2.val.integral.output.name (actual.1.value 0).integral.output.name ×
    NamedEquivalent values.2.2.1.2.val.integral.output.name (actual.1.value 1).integral.output.name :=
  let actual := values.1.occurrenceJet sourceFloor rootStage sources nonempty
  let first := values.1.valueEquivalent values.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
  let second := values.1.valueEquivalent values.2.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
  ⟨actual, first, second⟩

/-- The whole value attachment retains one original jet factory and both comparisons on that same actual value. -/
private theorem packaged_attach_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {polynomialFloor : Nat}
    (values : PolynomialValues walk polynomialFloor) (sourceFloor rootStage : Nat)
    (sources : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path index))
    (nonempty : values.1.parents ≠ []) :
    attach values sourceFloor rootStage sources nonempty =
      let actual := values.1.occurrenceJet sourceFloor rootStage sources nonempty
      let first := values.1.valueEquivalent values.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
      let second := values.1.valueEquivalent values.2.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
      ⟨actual, first, second⟩ := by rfl

/-- The whole value attachment retains one original jet factory and both comparisons on that same actual value. -/
theorem attach_factory
    {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {polynomialFloor : Nat}
    (values : PolynomialValues walk polynomialFloor) (sourceFloor rootStage : Nat)
    (sources : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      values.1.covered sourceFloor (CellEndpoints.Targets.build values.1.chain.path index))
    (nonempty : values.1.parents ≠ []) :
    attach values sourceFloor rootStage sources nonempty =
      let actual := values.1.occurrenceJet sourceFloor rootStage sources nonempty
      let first := values.1.valueEquivalent values.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
      let second := values.1.valueEquivalent values.2.2.1 sourceFloor rootStage sources nonempty actual.1 rfl
      ⟨actual, first, second⟩ := packaged_attach_factory values sourceFloor rootStage sources nonempty

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
