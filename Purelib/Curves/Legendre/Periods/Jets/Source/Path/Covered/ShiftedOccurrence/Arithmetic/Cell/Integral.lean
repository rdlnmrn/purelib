module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Cell
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Sample
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Sample.Integral
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor.Integral
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Transport
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Integral Taylor certificates on retained actual child occurrences

The construction uses the same cached child restrictions and signed Alignment.
Per-time queries retain the original source, target and arithmetic owners;
the resulting finite remainder concerns their actual polynomial integrals.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
  (startPoint finishPoint liftedCell ShiftedAcquisition)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {sourceIndex : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length}
    (located : Occurrence next.blocks next.requested.request sourceIndex)

namespace ValueCell

variable {located} (cell : ValueCell located)

/-- The target request view reads the identical original cached polynomial model. -/
private theorem target_model_eq (channel : Fin 6) :
    ((next.requested.request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell channel) =
      ((next.requested.prepared.entry sourceIndex).preparation.cell.models.cell channel) := rfl

/-- The actual original selected source base model pays the same genuinely acquired common request. -/
private theorem source_base_allowance_le (order coordinate : Fin 2) :
    ((source.prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance := by
  exact (source.cell_allowance_lt located.block (Specification.Table.baseIndex order coordinate)).1

/-- The independently acquired selected target base model pays that same original common request. -/
private theorem target_base_allowance_le (order coordinate : Fin 2) :
    ((next.requested.prepared.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance := by
  exact (next.requested.cell_allowance_lt sourceIndex (Specification.Table.baseIndex order coordinate)).1

/-- The actual independent original selected source derivative model pays its genuinely acquired common request. -/
private theorem source_slope_allowance_le (order coordinate : Fin 2) :
    ((source.prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance := by
  exact (source.cell_allowance_lt located.block (Specification.Table.slopeIndex order coordinate)).1

/-- Construct one genuine selected-row integral Taylor certificate on the SAME actual retained child.

The per-time answers are the actual Sample caches from this Cell. Their
three comparisons are only transported, not rebuilt. Both actual model
allowances are paid by the genuinely new common-request acquisitions.
Original centered occurrence laws derive endpoint and sheet coincidence;
the numerical certificate and fixed original box derive the integral bound.
-/
def integral (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) → Sample cell time)
    (order coordinate : Fin 2) : Integral cell order coordinate := by
  let common := spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry located.block)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Data.Rat.Fraction.Order.Basic.min_le_left _ _)
  have valuePaid :
      ((source.prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
          coordinate)).localAllowance ≤
        common.tolerance :=
    source_base_allowance_le (source := source) (next := next)
      (sourceIndex := sourceIndex) (located := located) order coordinate
  have outputPaid :
      ((next.requested.prepared.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
          coordinate)).localAllowance ≤
        common.tolerance :=
    target_base_allowance_le (next := next) (sourceIndex := sourceIndex) order coordinate
  have firstPaid :
      ((source.prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
          coordinate)).localAllowance ≤
        common.tolerance :=
    source_slope_allowance_le (source := source) (next := next)
      (sourceIndex := sourceIndex) (located := located) order coordinate
  let actual := Occurrence.Sample.integralCertificate
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := target) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := sourceFloor) (baseStart := startPoint parent)
      (baseFinish := startPoint parent) (original := chain.path) (stage := source.selected.stage)
      (targets := source.targets) (prepared := source.prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (blocks := next.blocks)
      (whole := next.geometry) (requestIndex := next.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage) (request := next.requested.request)
      (sourceIndex := sourceIndex)
      (located := located) (aligned := cell.aligned) (nonzero := nonzero) (spatial := spatial)
      (restriction := cell.restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid
  refine ⟨actual, ?_, ?_, ?_, ?_⟩
  · exact Occurrence.Sample.integralCertificate_base
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := target) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := sourceFloor) (baseStart := startPoint parent)
      (baseFinish := startPoint parent) (original := chain.path) (stage := source.selected.stage)
      (targets := source.targets) (prepared := source.prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (blocks := next.blocks)
      (whole := next.geometry) (requestIndex := next.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage) (request := next.requested.request)
      (sourceIndex := sourceIndex)
      (located := located) (aligned := cell.aligned) (nonzero := nonzero) (spatial := spatial)
      (restriction := cell.restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid
  · exact (Occurrence.Sample.integralCertificate_output
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := target) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := sourceFloor) (baseStart := startPoint parent)
      (baseFinish := startPoint parent) (original := chain.path) (stage := source.selected.stage)
      (targets := source.targets) (prepared := source.prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (blocks := next.blocks)
      (whole := next.geometry) (requestIndex := next.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage) (request := next.requested.request)
      (sourceIndex := sourceIndex)
      (located := located) (aligned := cell.aligned) (nonzero := nonzero) (spatial := spatial)
      (restriction := cell.restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).trans
        (congrArg CellModel.integralSample
          (target_model_eq (next := next) (sourceIndex := sourceIndex)
            (Specification.Table.baseIndex order coordinate)))
  · exact Occurrence.Sample.integralCertificate_slope
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := target) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := sourceFloor) (baseStart := startPoint parent)
      (baseFinish := startPoint parent) (original := chain.path) (stage := source.selected.stage)
      (targets := source.targets) (prepared := source.prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (blocks := next.blocks)
      (whole := next.geometry) (requestIndex := next.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage) (request := next.requested.request)
      (sourceIndex := sourceIndex)
      (located := located) (aligned := cell.aligned) (nonzero := nonzero) (spatial := spatial)
      (restriction := cell.restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid
  · exact (Occurrence.Sample.integralCertificate_factor
      (parameter := parameter) (increment := increment) (frame := frame) (basis := basis)
      (target := target) (count := count) (firstParent := parent) (remaining := parents)
      (covered := covered) (floor := sourceFloor) (baseStart := startPoint parent)
      (baseFinish := startPoint parent) (original := chain.path) (stage := source.selected.stage)
      (targets := source.targets) (prepared := source.prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (blocks := next.blocks)
      (whole := next.geometry) (requestIndex := next.requested.selected.stage)
      (globalFloor := targetFloor) (rootStage := targetRootStage) (request := next.requested.request)
      (sourceIndex := sourceIndex)
      (located := located) (aligned := cell.aligned) (nonzero := nonzero) (spatial := spatial)
      (restriction := cell.restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).trans
        (congrArg (fun model : CellModel =>
          2 * (4 * (Variation.Point.Step.Joint.rowCeiling
            (source.prepared.entry located.block).preparation.cell.patch increment order coordinate +
              7 / 2 + 7 / 2 + 7 / 2)) * Norm.Basic.normSq model.displacement)
          (target_model_eq (next := next) (sourceIndex := sourceIndex)
            (Specification.Table.baseIndex order coordinate)))

/-- Construct all four actual row integrals from the SAME bounded-time answer family and retained Cell.

The finite selectors read the four certificate/comparison views of every
provided Sample. Separate callback invocations remain independent original
queries; this constructor claims no cross-callback memoization.
-/
def buildIntegrals : IntegralBank cell :=
  let answers := fun time => cell.sampleAt time
  Data.Vector.DependentVector.ofFn (fun order : Fin 2 =>
    Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 => cell.integral answers order coordinate))

end ValueCell

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
