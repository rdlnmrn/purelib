module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests
import Purelib.Data.List.DependentProduct
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.Name

/-! # One global source acquisition and the actual retained six-channel scalar rows -/

namespace TestPurelib.Curves.Legendre.TraceSourceLayers

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Integration.Path.Dyadic
open OwnerMove.PrimitiveTarget

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable {originalSource : Spatial.Source leg.source leg.sourcePrepared}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {count : Nat} {frame : Curves.Legendre.Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}
variable (forms : DependentVector (fun channel : Fin 6 => Waist.Differential.Bounds.Data site parameter
  (Specification.Table.forms parameter channel)))
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}

/-- The exact original global source bank followed by its actual same-depth six-Layer/request banks. -/
def Acquisition
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) : Type 2 :=
  let scalar := initial.layerAt trace.budget.fine.selection.stage
  Σ prepared : OwnerTrace.NumericalSources bounds forms trace bank retained scalar factory caches
      modelFloor scalarFloor pairCurrent target positive sourceAccuracy requestStage,
    OwnerTrace.NumericalLayerRows bounds forms prepared.2.1.val prepared.2.2.1.val.2
      (prepared.inputSpans bounds forms rfl unitSpan)

/-- Compute numerical maxima and one whole source bank before acquiring scalar rows from their stored caches. -/
def acquire
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) :
    Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan :=
  let scalar := initial.layerAt trace.budget.fine.selection.stage
  let prepared := OwnerTrace.prepareSources bounds forms trace bank retained scalar factory caches
    modelFloor scalarFloor pairCurrent target positive sourceAccuracy requestStage
  let layers := prepared.acquireLayers bounds forms rfl unitSpan
  ⟨prepared, layers⟩

/-- All actual cached Source primitives have their own typed scalar-row bound at the count-paid requested allowance. -/
def Accuracy : Prop :=
  ∀ (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (actual : Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length)
    (channel : Fin 6),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    let scalar := (DependentProduct.get times actual.2 edge).1.val
    let primitive := (scalar.1.2.1.val.primitive channel).primitive.value
    normSq (primitive.eval (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 times edge.succ)) -
      primitive.eval (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 times edge.castSucc)) -
      (CoefficientRequests.LayerBank.layer bounds scalar channel).model.integralSample) <
        Rational.Budget.Aggregate.perTerm target times.length / 4

/-- The original Precision estimate proves every actual returned six-channel scalar-row inequality. -/
theorem accurate : Accuracy (originalSource := originalSource) (initial := initial)
    (count := count) (frame := frame) (basis := basis) (sheet := sheet) bounds forms := by
  intro trace bank retained factory caches modelFloor scalarFloor pairCurrent target positive sourceAccuracy
    requestStage unitSpan actual edge channel
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let row := DependentProduct.get times actual.2 edge
  let scalar := row.1.val
  have span := actual.1.inputSpans bounds forms rfl unitSpan edge
  have bound := CoefficientRequests.LayerBank.accurate bounds scalar row.2 ⟨span.1, span.2.1⟩ channel
  have primitive := CoefficientRequests.LayerBank.primitive_value bounds scalar channel
  have transport := congrArg (fun polynomial : Pair.Polynomial.Coefficients => normSq
    (polynomial.eval (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 times edge.succ)) -
      polynomial.eval (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 times edge.castSucc)) -
      (CoefficientRequests.LayerBank.layer bounds scalar channel).model.integralSample)) primitive
  exact transport.symm.trans_lt bound

/-- Each actual returned scalar bank uses the original global Taylor maximum, including a supplied later floor. -/
example
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (actual : Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    CoefficientRequests.Precisions.depth bounds (DependentProduct.get _ actual.2 edge).1.val.2.1.val
      actual.1.2.2.1.val.2 = actual.1.2.2.1.val.2 :=
  OwnerTrace.NumericalSources.layers_depth bounds forms trace bank retained
    (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage actual.1 rfl unitSpan actual.2 edge

/-- Every stored global six-cell row belongs to the identical complete cache in its actual numerical-input tuple. -/
example
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (actual : Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    let sources := actual.1.2.2.2.val
    let input := DependentProduct.get times actual.1.1.val edge
    ∃ inside : edge.val < sources.2.2.2.2.val.length,
      Source.Cell.PreparedParents.CellRow (frame := frame) (basis := basis) (count := 1)
        (parents := input.2.parents) input.2.covered actual.1.2.2.1.val.1 sources.2.1.val
        (sources.2.2.2.2.val[edge.val]'inside) :=
  OwnerTrace.NumericalSources.row_origins bounds forms trace bank retained
    (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage actual.1 edge

/-- The actual supplied whole Source model meets the eager six-channel scalar-row samples at the computed target. -/
example
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (actual : Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan) (channel : Fin 6) :
    OwnerTrace.NumericalSources.IntegralAccuracy bounds forms actual.1 rfl unitSpan actual.2 channel :=
  OwnerTrace.NumericalSources.integral_accurate bounds forms actual.1 rfl unitSpan actual.2 channel

/-- The original whole scalar programme meets the same acquired global Source model on every actual form. -/
example
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (requestStage : Nat)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (actual : Acquisition (initial := initial) bounds forms trace bank retained factory caches modelFloor scalarFloor
      pairCurrent target positive sourceAccuracy requestStage unitSpan) (channel : Fin 6) :
    OwnerTrace.NumericalSources.ProgrammeAccuracy bounds forms actual.1 channel :=
  OwnerTrace.NumericalSources.programme_accurate bounds forms actual.1 rfl unitSpan actual.2 channel

section Programmes

open Purelib.Integration.Path.Primitive.PrimitiveEdge

/-- Construct the actual all-six whole-programme request once from the same supplied trace and parent caches. -/
def compare
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor leftStart rightStart : Nat) :
    OwnerTrace.NumericalSources.ProgrammeRequest (initial := initial) bounds forms trace bank retained
      (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy rfl unitSpan sourceFloor leftStart rightStart :=
  OwnerTrace.NumericalSources.compareProgrammes bounds forms trace bank retained
    (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy rfl unitSpan sourceFloor leftStart rightStart

/-- Every actual later source/scalar pair meets the target using its retained comparison and paid stages. -/
example
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor leftStart rightStart : Nat)
    (request : OwnerTrace.NumericalSources.ProgrammeRequest (initial := initial) bounds forms trace bank retained
      (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy rfl unitSpan sourceFloor leftStart rightStart)
    (channel : Fin 6) (leftLater rightLater : Nat)
    (leftPaid : request.1.stage ≤ leftLater)
    (rightPaid : trace.budget.fine.selection.stage + request.2.1.2.2.1.val.2 ≤ rightLater) :
    let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
      (CellEndpoints.Targets.build caches.centeredChain.path index)
    normSq
      (((Source.Cell.PreparedParents.program caches.covered caches.centeredChain original channel).model
          leftLater).integralSample -
        ((initial.reweight (forms.get channel)).program.model rightLater).integralSample) < target := by
  have indices := request.2.2.2.2.property channel
  exact (request.2.2.2.2.val.get channel).close (indices.1.trans_le leftPaid) (indices.2.trans_le rightPaid)

/-- Retain the actual global raw bank and both original sampler receipts for all six named comparisons. -/
def compareNamed
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor rawLeftStart rawRightStart leftStart rightStart : Nat) :
    OwnerTrace.NumericalSources.NamedProgrammeRequest (initial := initial) bounds forms trace bank retained
      (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy rfl unitSpan sourceFloor rawLeftStart rawRightStart leftStart rightStart :=
  OwnerTrace.NumericalSources.compareNamedProgrammes bounds forms trace bank retained
    (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy rfl unitSpan sourceFloor rawLeftStart rawRightStart leftStart rightStart

/-- Each actual Source/scalar output name has an internally paid operational comparison at independent starts. -/
def equivalent
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (sourceAccuracy : AccuracyRequest)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) (sourceFloor : Nat) (channel : Fin 6) :
    let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
      (CellEndpoints.Targets.build caches.centeredChain.path index)
    Gaussian.Equivalence.NamedEquivalent
      (Source.Cell.PreparedParents.program caches.covered caches.centeredChain original channel).output.name
      (initial.reweight (forms.get channel)).program.output.name :=
  OwnerTrace.NumericalSources.equivalent bounds forms trace bank retained
    (initial.layerAt trace.budget.fine.selection.stage) factory caches modelFloor scalarFloor pairCurrent
    sourceAccuracy rfl unitSpan sourceFloor channel

end Programmes

end TestPurelib.Curves.Legendre.TraceSourceLayers
