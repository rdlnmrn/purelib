module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Rows
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block
import Purelib.Calculus.Jet.Quadratic.Weighted
import Purelib.Data.Vector.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Retained weighted integral certificates of original-parent row tables

The same parent certificates and shared weights determine four stored
weighted sums, with whole factory identities for every cached vector.
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

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents covered floor targets)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (firstAdmitted : Norm.Basic.normSq firstOffset ≤ allocation.bound)
    (lastAdmitted : Norm.Basic.normSq lastOffset ≤ allocation.bound)
    (firstWidths lastWidths : Fin (parent :: remaining).length → AccuracyRequest)
    (firstBlocks : Blocks (target := firstFrame) prepared ranges allocation firstAdmitted firstWidths)
    (lastBlocks : Blocks (target := lastFrame) prepared ranges allocation lastAdmitted lastWidths)
    {firstWhole : let first := DependentProduct.get (parent :: remaining) firstBlocks 0
      ShiftedGeometry (target := firstFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {lastWhole : let first := DependentProduct.get (parent :: remaining) lastBlocks 0
      ShiftedGeometry (target := lastFrame) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {firstNonempty : firstWhole.parents ≠ []} {lastNonempty : lastWhole.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (nonzero : lastOffset - firstOffset ≠ 0) (spatial : AccuracyRequest)
    (firstRequested : Requested firstWhole firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (lastRequested : Requested lastWhole lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (firstPositions : Position.Family firstBlocks firstRequested.request)
    (lastPositions : Position.Family lastBlocks lastRequested.request)
    (firstAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) firstBlocks outer).comparison.firstReference))
    (lastAligned : DependentProduct (parent :: remaining) (fun outer =>
      RootComparisons.Alignment
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.paths
        (DependentProduct.get (parent :: remaining) lastBlocks outer).comparison.firstReference))

namespace BetweenRows

variable {prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths firstBlocks lastBlocks}
    {unit nonzero spatial firstRequested lastRequested firstPositions lastPositions firstAligned lastAligned}
    (rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned)

/-- Original parent certificates, shared unit weights and their four exact original weighted sums.

The sampled pairs, restriction banks, Alignments and per-parent integral
rows remain the SAME supplied caches. These existing Sigma/Subtype/vector
containers store only their projection vectors, unit weights and original
weightedSum outputs with their whole factory identities.
-/
@[expose] def Integral :=
  (entries : { value : Data.Vector (Data.Vector
      (Data.Vector (Certificate (lastOffset - firstOffset)) (parent :: remaining).length) 2) 2 //
    value = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Data.Vector.Basic.vectorOfFn (fun outer => ((rows.entry outer).row order coordinate).certificate))) }) ×
  (weights : { value : Data.Vector Canonical (parent :: remaining).length //
    value = Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: remaining).length => (1 : Canonical)) }) ×
  { certificates : Data.Vector (Data.Vector (Certificate (lastOffset - firstOffset)) 2) 2 //
    certificates = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Certificate.weightedSum weights.val (entries.val order coordinate))) }

namespace Integral

/-- Project the retained parent certificates once and store all four original weighted integral sums once. -/
def build : Integral rows :=
  let entries := Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun outer => ((rows.entry outer).row order coordinate).certificate)))
  let weights := Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: remaining).length => (1 : Canonical))
  let certificates := Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Certificate.weightedSum weights (entries order coordinate)))
  ⟨⟨entries, rfl⟩, ⟨weights, rfl⟩, ⟨certificates, rfl⟩⟩

variable {rows} (actual : Integral rows)

/-- Read the SAME four stored original-parent certificate vectors. -/
@[expose] def entries : Data.Vector (Data.Vector
    (Data.Vector (Certificate (lastOffset - firstOffset)) (parent :: remaining).length) 2) 2 :=
  actual.1.val

/-- Read the SAME shared original unit-weight vector. -/
@[expose] def weights : Data.Vector Canonical (parent :: remaining).length := actual.2.1.val

/-- Read the SAME four stored original weighted-sum certificates. -/
@[expose] def certificates :
    Data.Vector (Data.Vector (Certificate (lastOffset - firstOffset)) 2) 2 := actual.2.2.val

/-- The complete parent-projection vector retains its original factory equation on the SAME rows. -/
private theorem entries_factory_proof
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
    (actual : Integral rows) : actual.entries = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun outer => ((rows.entry outer).row order coordinate).certificate))) :=
  actual.1.property

/-- Every retained parent-projection vector equals its original row factory. -/
@[expose] def EntriesFactoryLaw : Prop :=
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
    (actual : Integral rows),
    actual.entries = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Data.Vector.Basic.vectorOfFn (fun outer => ((rows.entry outer).row order coordinate).certificate)))

/-- The complete parent-projection vector retains its original factory equation on the SAME rows. -/
theorem entries_eq : EntriesFactoryLaw := @entries_factory_proof

/-- The complete shared weight vector retains its original exact unit factory. -/
private theorem weights_factory_proof
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
    (actual : Integral rows) : actual.weights =
    Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: remaining).length => (1 : Canonical)) :=
  actual.2.1.property

/-- Every retained shared weight vector equals the original unit vector. -/
@[expose] def WeightsFactoryLaw : Prop :=
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
    (actual : Integral rows),
    actual.weights =
      Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: remaining).length => (1 : Canonical))

/-- The complete shared weight vector retains its original exact unit factory. -/
theorem weights_eq : WeightsFactoryLaw := @weights_factory_proof

/-- All four sums use the SAME earlier retained entry and weight vectors. -/
private theorem certificates_factory_proof
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
    (actual : Integral rows) : actual.certificates = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Certificate.weightedSum actual.weights (actual.entries order coordinate))) :=
  actual.2.2.property

/-- Every retained certificate bank equals its original weighted-sum factory. -/
@[expose] def CertificatesFactoryLaw : Prop :=
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
    (actual : Integral rows),
    actual.certificates = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Certificate.weightedSum actual.weights (actual.entries order coordinate)))

/-- All four sums use the SAME earlier retained entry and weight vectors. -/
theorem certificates_eq : CertificatesFactoryLaw := @certificates_factory_proof

/-- The selected stored entry is the SAME original parent's integral certificate. -/
private theorem entry_factory_proof
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
    (actual : Integral rows) (outer : Fin (parent :: remaining).length) (order coordinate : Fin 2) :
    actual.entries order coordinate outer = ((rows.entry outer).row order coordinate).certificate := by
  have selected := congrArg (fun values : Data.Vector (Data.Vector
      (Data.Vector (Certificate (lastOffset - firstOffset)) (parent :: remaining).length) 2) 2 =>
    values order coordinate outer) actual.entries_eq
  rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply] at selected
  exact selected

/-- Every retained parent certificate reads its original projected row. -/
@[expose] def EntryFactoryLaw : Prop :=
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
    (actual : Integral rows) (outer : Fin (parent :: remaining).length) (order coordinate : Fin 2),
    actual.entries order coordinate outer = ((rows.entry outer).row order coordinate).certificate

/-- The selected stored entry is the SAME original parent's integral certificate. -/
theorem entry_eq : EntryFactoryLaw := @entry_factory_proof

/-- Each retained weight is the identical original unit Gaussian. -/
private theorem weight_factory_proof
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
    (actual : Integral rows) (outer : Fin (parent :: remaining).length) : actual.weights outer = 1 :=
  (congrArg (fun weights : Data.Vector Canonical (parent :: remaining).length => weights outer)
    actual.weights_eq).trans (Data.Vector.Basic.vectorOfFn_apply _ outer)

/-- Every retained shared weight reads the original unit coefficient. -/
@[expose] def WeightFactoryLaw : Prop :=
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
    (actual : Integral rows) (outer : Fin (parent :: remaining).length),
    actual.weights outer = 1

/-- Each retained weight is the identical original unit Gaussian. -/
theorem weight_eq : WeightFactoryLaw := @weight_factory_proof

/-- The selected whole certificate retains the original weighted-sum factory and both SAME stored vectors. -/
private theorem certificate_factory_proof
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
    actual.certificates order coordinate =
      Certificate.weightedSum actual.weights (actual.entries order coordinate) := by
  have selected := congrArg (fun values : Data.Vector
      (Data.Vector (Certificate (lastOffset - firstOffset)) 2) 2 => values order coordinate)
    actual.certificates_eq
  rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply] at selected
  exact selected

/-- Every retained row certificate equals its original weighted sum. -/
@[expose] def CertificateFactoryLaw : Prop :=
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
    actual.certificates order coordinate =
        Certificate.weightedSum actual.weights (actual.entries order coordinate)

/-- The selected whole certificate retains the original weighted-sum factory and both SAME stored vectors. -/
theorem certificate_factory : CertificateFactoryLaw := @certificate_factory_proof

end Integral

end BetweenRows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
