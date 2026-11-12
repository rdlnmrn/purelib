module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Acquire
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

/-! # One ordered old-source and shifted-target acquisition at the same actual accuracy

The old sufficient-stage request exists first. Its SAME source preparations
supply every endpoint Step and retained shifted block. One joined geometry
then precedes ONE new target global request at the identical common accuracy.
Both original allocation owners remain distinct and genuinely paid; earlier
coarse requests and per-acquisition local Targets are never relabelled.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain current floor rootStage accuracy)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)

/-- Complete original shifted block, whole geometry and new target request caches at the SAME old-source accuracy.

The old source request stays the nominal parent. Every factory equation
retains its complete actual output, so the target's callbacks consume the
same original preparations, Steps, shifted acquisitions, trace owners and
joined global geometry; no query or per-parent allocation is repeated.
-/
@[expose] def Shifted (targetCurrent targetFloor targetRootStage : Nat) :=
  (blocks : { value : ShiftedGeometry.Blocks (target := target)
      source.prepared ranges allocation admitted widths //
    value = ShiftedGeometry.Blocks.build source.prepared source.prepared_eq ranges allocation admitted widths }) ×
  (geometry : { value :
      let first := DependentProduct.get (parent :: parents) blocks.val 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name //
    value = ShiftedGeometry.build source.prepared ranges allocation admitted widths blocks.val chain roots }) ×
  ShiftedGeometry.Requested geometry.val
    (by
      rewrite [geometry.property]
      exact ShiftedGeometry.build_parents_ne_nil source.prepared ranges allocation admitted widths
        blocks.val chain roots)
    targetCurrent targetFloor targetRootStage accuracy

/-- Acquire every original shifted block, join the closed geometry and request the target globally at the SAME accuracy.

The supplied old sufficient-stage cache is never rebuilt. Its complete
factory identity feeds the existing endpoint continuations. The materialized
block family and global geometry each execute once before the target's ONE
actual sufficient-stage request; no desired comparison or bound is input.
-/
def shifted (targetCurrent targetFloor targetRootStage : Nat) :
    Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage :=
  let blocks := ShiftedGeometry.Blocks.build (target := target)
    source.prepared source.prepared_eq ranges allocation admitted widths
  let geometry := ShiftedGeometry.build (target := target)
    source.prepared ranges allocation admitted widths blocks chain roots
  let nonempty := ShiftedGeometry.build_parents_ne_nil (target := target)
    source.prepared ranges allocation admitted widths blocks chain roots
  let requested := ShiftedGeometry.Requested.build geometry nonempty
    targetCurrent targetFloor targetRootStage accuracy
  ⟨⟨blocks, rfl⟩, ⟨geometry, rfl⟩, requested⟩

namespace Shifted

variable {source ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (retained : Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)

/-- Read the exact once-materialized original block family on the SAME newly prepared old source. -/
@[expose] def blocks : ShiftedGeometry.Blocks (target := target)
    source.prepared ranges allocation admitted widths := retained.1.val

/-- The whole block family retains its original actual endpoint/acquisition/trace factory. -/
theorem blocks_eq : retained.blocks = ShiftedGeometry.Blocks.build source.prepared source.prepared_eq
    ranges allocation admitted widths := retained.1.property

/-- Read the one joined original shifted geometry before target allocation. -/
@[expose] def geometry :
    let first := DependentProduct.get (parent :: parents) retained.blocks 0
    ShiftedGeometry (target := target) (basis := basis) (count := count)
      (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name :=
  retained.2.1.val

/-- The complete global geometry retains the SAME stored blocks and original old closed chains. -/
theorem geometry_eq : retained.geometry = ShiftedGeometry.build source.prepared ranges allocation admitted widths
    retained.blocks chain roots := retained.2.1.property

/-- Read the actual independently paid target global request, including its own exact Targets, bank and preparations. -/
@[expose] def requested : ShiftedGeometry.Requested retained.geometry
    (by
      rewrite [retained.geometry_eq]
      exact ShiftedGeometry.build_parents_ne_nil source.prepared ranges allocation admitted widths
        retained.blocks chain roots)
    targetCurrent targetFloor targetRootStage accuracy := retained.2.2

/-- Every new shifted-target source cell pays precisely the same actual accuracy as the retained old source request. -/
theorem target_allowance_lt
    (index : Fin (retained.requested.request.shape.val.1 :: retained.requested.request.shape.val.2).length)
    (channel : Fin 6) :
    ((retained.requested.prepared.entry index).preparation.cell.models.cell channel).localAllowance <
      accuracy.tolerance :=
  retained.requested.cell_allowance_lt index channel

end Shifted

/-- Compute the common request, then acquire genuine old sources, shifted geometry and target sources in order.

Both source requests pay exactly the same positive spatial/parameter
minimum before any interior point callback. The old covered geometry,
ParameterRange, common admitted increment and original closed root chain
remain unchanged. Every new source/trace/allocation cache is retained;
no earlier coarse request is relabelled or required to meet a new bound.
-/
def joint (spatial : AccuracyRequest) (nonzero : increment ≠ 0)
    (sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat) :
    (old : Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))) ×
    Shifted (target := target) old ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage :=
  let common := spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)
  let old := build covered chain sourceCurrent sourceFloor sourceRootStage common
  let next := shifted (target := target) old ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage
  ⟨old, next⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
