module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Euler
public import Purelib.Calculus.Linear.Euler.Schedule
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Requested endpoint accuracy on the same retained positive-grid programmes

The original fixed parent factor determines a rational search scale before
fine acquisition. The actual selected fourth-power refinement pays the
original block-Euler endpoint bound on those same cached samples.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (zipWith)
open Purelib.Calculus.Linear
open Purelib.LinearAlgebra.Gaussian
open Purelib.Algebra.Recurrence
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry (ValueBlocks)
open Purelib.Curves.Legendre.Periods.Jets.Variation

/-- The same original two fixed-parent Taylor factors give the directional Euler factor before fine acquisition. -/
@[expose] def taylorFactor
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents)) (direction : Canonical) : Rational :=
  2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
    Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)

/-- Both original fixed-parent factors and actual direction quadrance make the pre-acquisition factor nonnegative. -/
theorem taylorFactor_nonnegative
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents)) (direction : Canonical) :
    0 ≤ taylorFactor covered direction :=
  Order.Arithmetic.mul_nonneg_direct (by decide)
    ((show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.mul_nonneg_direct
          ((show (0 : Rational) = 0 + 0 by ring1).trans_le
            (Order.Arithmetic.add_le_add_direct
              (ValueBlocks.factor_nonnegative (covered := covered) 0 0)
              (ValueBlocks.factor_nonnegative (covered := covered) 0 1)))
          (Order.Arithmetic.sq_nonneg_direct _))
        (Order.Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg direction))))

namespace Table.Trace

/-- The original selected refinement derives the requested whole-grid endpoint accuracy internally.

The source, positive-node table, all completion caches and original trace
are the same owners used by eulerBlocks_le. The original coarse response
and selected fourth-power count bound its returned affine scalar; no good
refinement witness or desired endpoint comparison is assumed.
-/
theorem requestedEndpoint_lt
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    (request : AccuracyRequest)
    (selection : Search.Selection
      (Euler.endpointScale (coarseIntervals frame direction) (taylorFactor covered direction)) 0 request.tolerance)
    {source : Requested covered chain current floor rootStage
      ((connectionRequest frame (coarseIntervals frame direction * 4 ^ selection.stage)
        (fineIntervals_positive frame direction (4 ^ selection.stage) (Nat.pow_pos (by decide))) spatial).minimum
        (Sampling.incrementRequest
          (Sampling.gridIncrement (coarseIntervals frame direction * 4 ^ selection.stage) direction)
          (Sampling.gridIncrement_nonzero (coarseIntervals frame direction * 4 ^ selection.stage)
            (fineIntervals_positive frame direction (4 ^ selection.stage) (Nat.pow_pos (by decide)))
            direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {table : Table (coarseIntervals frame direction * 4 ^ selection.stage)
      (fineIntervals_positive frame direction (4 ^ selection.stage) (Nat.pow_pos (by decide))) direction moving
      (connectionRequest frame (coarseIntervals frame direction * 4 ^ selection.stage)
        (fineIntervals_positive frame direction (4 ^ selection.stage) (Nat.pow_pos (by decide))) spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (old : QueryAgreement source.prepared)
    (completed : Table.Completions table old) :
    let fineCount := coarseIntervals frame direction * 4 ^ selection.stage
    let boundedIndex := fun index : Nat => (⟨min index fineCount,
      Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
    let coefficients := fun index => Connection.alongMatrix
      (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
    Norm.vector (zipWith (fun first last => first - last)
      (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩)
      (Euler.trace coefficients (fun _ => 1 / (fineCount : Rational)) (trace.eulerValues 0) fineCount)) <
        request.tolerance := by
  exact (trace.eulerBlocks_le (refinement := 4 ^ selection.stage)
    (positiveRefinement := Nat.pow_pos (by decide)) old completed).trans_lt
      (Euler.blockBound_lt (coarseIntervals frame direction) (coarseIntervals_positive frame direction)
        (taylorFactor covered direction) (taylorFactor_nonnegative covered direction) request selection)

end Table.Trace

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
