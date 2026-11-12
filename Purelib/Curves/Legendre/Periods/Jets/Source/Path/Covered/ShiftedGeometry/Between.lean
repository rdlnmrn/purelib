module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Integral
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block
import Purelib.Calculus.Jet.Quadratic.Weighted
import Purelib.Calculus.Jet.Quadratic.Chord
import Purelib.Data.Vector.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Quantitative readbacks of retained two-target integral certificates

The stored weighted certificates retain both programme models and their
original slope, factor and remainder bounds on the same requested data.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Calculus.Jet
open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Acquisition.Segment
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition
  (BetweenRequested)

namespace BetweenRows

namespace Integral

/-- The global base is the SAME first target original programme-stage model sample. -/
private theorem base_readback_proof
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2) : (actual.certificates order coordinate).base =
    (firstRequested.modelAt (parameter := parameter) (increment := firstOffset)
      (target := firstFrame) (basis := basis) (count := count)
      (Specification.Table.baseIndex order coordinate) firstRequested.selected.stage).integralSample := by
  have original := (congrArg
    (fun certificate : Certificate (lastOffset - firstOffset) => certificate.base)
      (actual.certificate_factory order coordinate)).trans
        (Certificate.weightedSum_base actual.weights (actual.entries order coordinate))
  have entries : sumFin (fun outer => actual.weights outer * (actual.entries order coordinate outer).base) =
      sumFin (fun outer => sumFin (fun inner =>
        ((firstRequested.prepared.entry (firstPositions.entry outer inner).sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate)).integralSample)) :=
    sumFin_congr (fun outer =>
      (congrArg₂ (fun weight value : Canonical => weight * value) (actual.weight_eq outer)
        ((congrArg
          (fun certificate : Certificate (lastOffset - firstOffset) => certificate.base)
          (actual.entry_eq outer order coordinate)).trans
            (((rows.entry outer).row order coordinate).base))).trans (Basic.one_mul _))
  have grouped := firstPositions.sample_eq_groups firstRequested.prepared firstWhole_eq
    (Specification.Table.baseIndex order coordinate)
  have raw := original.trans (entries.trans (grouped.symm.trans
    (firstRequested.request.model_at_sample (Specification.Table.baseIndex order coordinate)).symm))
  exact raw.trans (Requested.modelAt_integralSample
    (parameter := parameter) (increment := firstOffset) (target := firstFrame) (basis := basis) (count := count)
    firstRequested (Specification.Table.baseIndex order coordinate) firstRequested.selected.stage)

-- Preserve the named geometric equality used only by the proof.
set_option linter.unusedVariables false in
/-- Every retained base reads the original first-target integral. -/
@[expose] def BaseReadbackLaw : Prop :=
  ∀ {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).base =
      (firstRequested.modelAt (parameter := parameter) (increment := firstOffset)
        (target := firstFrame) (basis := basis) (count := count)
        (Specification.Table.baseIndex order coordinate) firstRequested.selected.stage).integralSample

/-- The global base is the SAME first target original programme-stage model sample. -/
theorem base : BaseReadbackLaw := @base_readback_proof

/-- The global output is the SAME independent last target original programme-stage model sample. -/
private theorem output_readback_proof
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2) : (actual.certificates order coordinate).output =
    (lastRequested.modelAt (parameter := parameter) (increment := lastOffset)
      (target := lastFrame) (basis := basis) (count := count)
      (Specification.Table.baseIndex order coordinate) lastRequested.selected.stage).integralSample := by
  have original := (congrArg
    (fun certificate : Certificate (lastOffset - firstOffset) => certificate.output)
      (actual.certificate_factory order coordinate)).trans
        (Certificate.weightedSum_output actual.weights (actual.entries order coordinate))
  have entries : sumFin (fun outer => actual.weights outer * (actual.entries order coordinate outer).output) =
      sumFin (fun outer => sumFin (fun inner =>
        ((lastRequested.prepared.entry (lastPositions.entry outer inner).sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate)).integralSample)) :=
    sumFin_congr (fun outer =>
      (congrArg₂ (fun weight value : Canonical => weight * value) (actual.weight_eq outer)
        ((congrArg
          (fun certificate : Certificate (lastOffset - firstOffset) => certificate.output)
          (actual.entry_eq outer order coordinate)).trans
            (((rows.entry outer).row order coordinate).output))).trans (Basic.one_mul _))
  have grouped := lastPositions.sample_eq_groups lastRequested.prepared lastWhole_eq
    (Specification.Table.baseIndex order coordinate)
  have raw := original.trans (entries.trans (grouped.symm.trans
    (lastRequested.request.model_at_sample (Specification.Table.baseIndex order coordinate)).symm))
  exact raw.trans (Requested.modelAt_integralSample
    (parameter := parameter) (increment := lastOffset) (target := lastFrame) (basis := basis) (count := count)
    lastRequested (Specification.Table.baseIndex order coordinate) lastRequested.selected.stage)

-- Preserve the named geometric equality used only by the proof.
set_option linter.unusedVariables false in
/-- Every retained output reads the original last-target integral. -/
@[expose] def OutputReadbackLaw : Prop :=
  ∀ {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).output =
      (lastRequested.modelAt (parameter := parameter) (increment := lastOffset)
        (target := lastFrame) (basis := basis) (count := count)
        (Specification.Table.baseIndex order coordinate) lastRequested.selected.stage).integralSample

/-- The global output is the SAME independent last target original programme-stage model sample. -/
theorem output : OutputReadbackLaw := @output_readback_proof

/-- The global slope is the SAME first target original derivative-channel programme-stage sample. -/
private theorem slope_readback_proof
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2) : (actual.certificates order coordinate).slope =
    (firstRequested.modelAt (parameter := parameter) (increment := firstOffset)
      (target := firstFrame) (basis := basis) (count := count)
      (Specification.Table.slopeIndex order coordinate) firstRequested.selected.stage).integralSample := by
  have original := (congrArg
    (fun certificate : Certificate (lastOffset - firstOffset) => certificate.slope)
      (actual.certificate_factory order coordinate)).trans
        (Certificate.weightedSum_slope actual.weights (actual.entries order coordinate))
  have entries : sumFin (fun outer => actual.weights outer * (actual.entries order coordinate outer).slope) =
      sumFin (fun outer => sumFin (fun inner =>
        ((firstRequested.prepared.entry (firstPositions.entry outer inner).sourceIndex).preparation.cell.models.cell
          (Specification.Table.slopeIndex order coordinate)).integralSample)) :=
    sumFin_congr (fun outer =>
      (congrArg₂ (fun weight value : Canonical => weight * value) (actual.weight_eq outer)
        ((congrArg
          (fun certificate : Certificate (lastOffset - firstOffset) => certificate.slope)
          (actual.entry_eq outer order coordinate)).trans
            (((rows.entry outer).row order coordinate).slope))).trans (Basic.one_mul _))
  have grouped := firstPositions.sample_eq_groups firstRequested.prepared firstWhole_eq
    (Specification.Table.slopeIndex order coordinate)
  have raw := original.trans (entries.trans (grouped.symm.trans
    (firstRequested.request.model_at_sample (Specification.Table.slopeIndex order coordinate)).symm))
  exact raw.trans (Requested.modelAt_integralSample
    (parameter := parameter) (increment := firstOffset) (target := firstFrame) (basis := basis) (count := count)
    firstRequested (Specification.Table.slopeIndex order coordinate) firstRequested.selected.stage)

-- Preserve the named geometric equality used only by the proof.
set_option linter.unusedVariables false in
/-- Every retained slope reads the original first-target derivative integral. -/
@[expose] def SlopeReadbackLaw : Prop :=
  ∀ {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2),
    (actual.certificates order coordinate).slope =
      (firstRequested.modelAt (parameter := parameter) (increment := firstOffset)
        (target := firstFrame) (basis := basis) (count := count)
        (Specification.Table.slopeIndex order coordinate) firstRequested.selected.stage).integralSample

/-- The global slope is the SAME first target original derivative-channel programme-stage sample. -/
theorem slope : SlopeReadbackLaw := @slope_readback_proof

/-- The SAME global factor equals the existing original fixed-cover row factor.

Only original parent count, original patch/count ceilings and original
physical displacements enter ValueBlocks.factor. Both adaptive target mesh
counts, absolute offsets and selected programme stages are absent.
-/
private theorem factor_readback_proof
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows) (order coordinate : Fin 2) :
    (actual.certificates order coordinate).factor = ValueBlocks.factor (covered := covered) order coordinate := by
  have original := (congrArg
    (fun certificate : Certificate (lastOffset - firstOffset) => certificate.factor)
      (actual.certificate_factory order coordinate)).trans
        (Certificate.weightedSum_factor actual.weights (actual.entries order coordinate))
  have terms (outer : Fin (parent :: remaining).length) :
      Norm.Basic.normSq (actual.weights outer) * (actual.entries order coordinate outer).factor =
        ValueBlock.density (covered := covered) outer order coordinate := by
    have weight : Norm.Basic.normSq (actual.weights outer) = 1 :=
      (congrArg Norm.Basic.normSq (actual.weight_eq outer)).trans Norm.Basic.normSq_one
    have factor := (congrArg
      (fun certificate : Certificate (lastOffset - firstOffset) => certificate.factor)
      (actual.entry_eq outer order coordinate)).trans (((rows.entry outer).row order coordinate).factor)
    exact (congrArg₂ (fun weight factor : Rational => weight * factor) weight factor).trans
      (Field.one_mul _)
  exact original.trans (congrArg (fun total : Rational => ((parent :: remaining).length : Rational) * total)
    (sumFin_congr terms))

/-- Every retained factor equals its original fixed-parent sum. -/
@[expose] def FactorReadbackLaw : Prop :=
  ∀ {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows) (order coordinate : Fin 2),
    (actual.certificates order coordinate).factor = ValueBlocks.factor (covered := covered) order coordinate

/-- The SAME global factor equals the existing original fixed-cover row factor.

Only original parent count, original patch/count ceilings and original
physical displacements enter ValueBlocks.factor. Both adaptive target mesh
counts, absolute offsets and selected programme stages are absent.
-/
theorem factor_eq : FactorReadbackLaw := @factor_readback_proof

/-- The two actual selected global programme samples obey the computed original-cover fourth-order bound.

The three sample readbacks retain both independent programme/model owners.
This is the original stored weighted certificate and its fixed factor, with
no Completion, desired integral estimate, period identity or later range
premise. A zero physical displacement and zero factor remain permitted.
-/
private theorem remainder_bound_proof
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2) :
    Canonical.normSq
      ((model lastRequested.request.covered lastRequested.request.chain
        lastRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
        lastRequested.selected.stage).integralSample -
      (model firstRequested.request.covered firstRequested.request.chain
        firstRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
        firstRequested.selected.stage).integralSample -
      (lastOffset - firstOffset) *
        (model firstRequested.request.covered firstRequested.request.chain
          firstRequested.request.attempt.preparationFamily (Specification.Table.slopeIndex order coordinate)
          firstRequested.selected.stage).integralSample) ≤
      ValueBlocks.factor (covered := covered) order coordinate * Canonical.normSq (lastOffset - firstOffset) ^ 2 := by
  have difference := congrArg₂ (fun output base : Canonical => output - base)
    (actual.output lastWhole_eq order coordinate) (actual.base firstWhole_eq order coordinate)
  have residual := congrArg₂ (fun value slope : Canonical => value - (lastOffset - firstOffset) * slope)
    difference (actual.slope firstWhole_eq order coordinate)
  have bounded := (congrArg Canonical.normSq
    (residual.symm.trans (actual.certificates order coordinate).expansion)).trans_le
      (actual.certificates order coordinate).remainder_le
  exact bounded.trans_eq (congrArg (fun factor : Rational => factor * Canonical.normSq (lastOffset - firstOffset) ^ 2)
    (actual.factor_eq order coordinate))

-- Preserve the named integral and geometric witnesses used only by the proof.
set_option linter.unusedVariables false in
/-- Every retained weighted remainder satisfies its original quadratic bound. -/
@[expose] def RemainderBound : Prop :=
  ∀ {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2),
    Canonical.normSq
        ((model lastRequested.request.covered lastRequested.request.chain
          lastRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
          lastRequested.selected.stage).integralSample -
        (model firstRequested.request.covered firstRequested.request.chain
          firstRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
          firstRequested.selected.stage).integralSample -
        (lastOffset - firstOffset) *
          (model firstRequested.request.covered firstRequested.request.chain
            firstRequested.request.attempt.preparationFamily (Specification.Table.slopeIndex order coordinate)
            firstRequested.selected.stage).integralSample) ≤
        ValueBlocks.factor (covered := covered) order coordinate * Canonical.normSq (lastOffset - firstOffset) ^ 2

/-- The two actual selected global programme samples obey the computed original-cover fourth-order bound.

The three sample readbacks retain both independent programme/model owners.
This is the original stored weighted certificate and its fixed factor, with
no Completion, desired integral estimate, period identity or later range
premise. A zero physical displacement and zero factor remain permitted.
-/
theorem remainder_le : RemainderBound := @remainder_bound_proof

/-- The same two absolute-offset members have internally paid first and second parameter-difference slopes.

The two target Frames and root continuations keep the SAME fixed spatial
origin. Both actual global Requests pay the nonzero OFFSET DIFFERENCE's
fourth-order target; an absolute-offset preparation floor is not retagged.
The original stored Taylor certificate and its exact sample/factor laws
derive all four quotient bounds, without a desired comparison as input.
-/
theorem differenceQuotient_le
    {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest}
    {firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths}
    {lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths}
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0} {spatial : AccuracyRequest}
    {firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero))}
    {firstPositions : Position.Family firstBlocks firstRequested.request}
    {lastPositions : Position.Family lastBlocks lastRequested.request}
    {firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference)}
    {lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference)}
    {rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned}
    (actual : Integral rows)
    {oldGeometry : CenteredPathChain (parent :: remaining)
      (start := startPoint parent) (finish := startPoint parent)}
    {oldRoot : Named} {oldRoots : RootChain (parent :: remaining) oldRoot oldRoot}
    (firstWhole_eq : firstWhole =
      ShiftedGeometry.build prepared ranges allocation firstAdmitted firstWidths firstBlocks oldGeometry oldRoots)
    (lastWhole_eq : lastWhole =
      ShiftedGeometry.build prepared ranges allocation lastAdmitted lastWidths lastBlocks oldGeometry oldRoots)
    (order coordinate : Fin 2) :
    Canonical.normSq
      (((model lastRequested.request.covered lastRequested.request.chain
        lastRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
        lastRequested.selected.stage).integralSample -
      (model firstRequested.request.covered firstRequested.request.chain
        firstRequested.request.attempt.preparationFamily (Specification.Table.baseIndex order coordinate)
        firstRequested.selected.stage).integralSample) / (lastOffset - firstOffset) -
        (model firstRequested.request.covered firstRequested.request.chain
          firstRequested.request.attempt.preparationFamily (Specification.Table.slopeIndex order coordinate)
          firstRequested.selected.stage).integralSample) ≤
      ValueBlocks.factor (covered := covered) order coordinate * Canonical.normSq (lastOffset - firstOffset) := by
  have bounded := Quadratic.Basic.Certificate.differenceQuotient_le
    (actual.certificates order coordinate) nonzero
  have difference := congrArg₂ (fun output base : Canonical => output - base)
    (actual.output lastWhole_eq order coordinate) (actual.base firstWhole_eq order coordinate)
  have quotient := congrArg₂ (fun value slope : Canonical =>
    Canonical.normSq (value / (lastOffset - firstOffset) - slope))
    difference (actual.slope firstWhole_eq order coordinate)
  have factor := congrArg (fun factor : Rational => factor * Canonical.normSq (lastOffset - firstOffset))
    (actual.factor_eq order coordinate)
  exact quotient.symm.trans_le (bounded.trans_eq factor)

end Integral

end BetweenRows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
