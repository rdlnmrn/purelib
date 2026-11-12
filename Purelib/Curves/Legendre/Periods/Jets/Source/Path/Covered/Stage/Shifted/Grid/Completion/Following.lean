module

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source.Table
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Following Euler windows on the original stored completion table -/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

open CompletionData (RequestedSource)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn)
open Purelib.LinearAlgebra.Gaussian

namespace Table.Completions

variable
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {table : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {old : QueryAgreement source.prepared}
    (retained : Completions table old)
    (index : Fin intervals)

variable (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (initial : Data.Vector Canonical 2) (charge : Rational)

/-- The original following-window bound on one stored completion entry and incoming vector. -/
@[expose] def FollowingBound : Prop :=
  RequestedSource.EulerBound (table.nodes.node index) (retained.entry index)
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial charge

/-- The original following-window result on one stored completion entry and incoming vector. -/
@[expose] def FollowingResult : Type _ :=
  RequestedSource.EulerResult (table.nodes.node index) (retained.entry index)
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial charge

variable {charge} (tolerance : Rational)
    (initialError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        (((table.programmes.entry index).targetProgram
          (next := (table.nodes.node index).next) (Specification.Table.valueIndex coordinate)).model
            (table.nodes.node index).next.requested.selected.stage).integralSample)) initial) ≤ tolerance)

/-- Every stored completion propagates its actual incoming programme discrepancy to the next Euler window.

The quantified statement keeps the original source, node, alignment,
programmes, completion and vector, together with the discrepancy payment.
-/
@[expose] def FollowingBoundLaw : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {table : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {old : QueryAgreement source.prepared}
    (retained : Completions table old)
    (index : Fin intervals)

    (nextDirection : Canonical) (nextMoving : nextDirection ≠ 0)
    (nextSpatial : AccuracyRequest) (nextCurrent nextRefinement : Nat)
    (nextPositive : 0 < nextRefinement)
    (initial : Data.Vector Canonical 2)

    (tolerance : Rational)
    (_initialError : Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
        (((table.programmes.entry index).targetProgram
          (next := (table.nodes.node index).next) (Specification.Table.valueIndex coordinate)).model
            (table.nodes.node index).next.requested.selected.stage).integralSample)) initial) ≤ tolerance),
    retained.FollowingBound index nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial
      (2 * (2 * Approximation.Rational.Geometric.Basic.quarterRadius (errorScale (parent :: parents))
        (table.nodes.node index).next.requested.selected.stage + tolerance))

/-- The stored programmes pay the following-window bound from their actual incoming discrepancy. -/
theorem followingBound : FollowingBoundLaw := by
  unfold FollowingBoundLaw
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage table old retained index nextDirection nextMoving nextSpatial nextCurrent
    nextRefinement nextPositive initial tolerance initialError
  exact RequestedSource.eulerBound (table.nodes.node index) (retained.entry index) (table.programmes.entry index)
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial tolerance initialError

/-- Execute the original following trace using the stored completion, programmes and incoming discrepancy. -/
def followingResult :
    retained.FollowingResult index nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial
      (2 * (2 * Approximation.Rational.Geometric.Basic.quarterRadius (errorScale (parent :: parents))
        (table.nodes.node index).next.requested.selected.stage + tolerance)) :=
  RequestedSource.eulerResult (table.nodes.node index) (retained.entry index) (table.programmes.entry index)
    nextDirection nextMoving nextSpatial nextCurrent nextRefinement nextPositive initial tolerance initialError

end Table.Completions

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
