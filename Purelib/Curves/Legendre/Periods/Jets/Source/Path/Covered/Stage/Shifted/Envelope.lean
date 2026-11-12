module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Envelope

/-! # The actual incoming shifted source family pays its all-later row ceiling

The original Shifted realization already retains its complete block and
geometry factories and actual global Request. Those exact values derive
the ceiling premise for every original incoming covered occurrence. The
same covering spine underlies every later source/programme stage.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

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
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step (Joint)

/-- Every actual incoming target/source occurrence pays the computed original-family row ceiling at all later stages.

The original exact geometry factory supplies the occurrence lookup. This
proof constructs only that original finite geometric map; no source query,
root advancement, preparation, bank, Completion or numerical certificate
is executed or replaced. The conclusion is the actual all-later H premise,
with H computed from the supplied original preparation caches internally.
-/
theorem target_rowCeiling_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    {source : Requested covered chain current floor rootStage accuracy}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)
    (laterIncrement : Canonical) (order coordinate : Fin 2)
    (sourceIndex : Fin (retained.requested.request.shape.val.1 ::
      retained.requested.request.shape.val.2).length) :
    Joint.rowCeiling ((retained.requested.request.covered.entry sourceIndex).val.neighborhood count)
        laterIncrement order coordinate ≤ source.prepared.envelopeCeiling := by
  let stored : ShiftedGeometry.Occurrences retained.blocks retained.requested.request :=
    ShiftedGeometry.occurrences (prepared := source.prepared) (ranges := ranges) (allocation := allocation)
      (admitted := admitted) (widths := widths) (oldGeometry := chain) (oldRoots := roots)
      retained.blocks retained.requested.request retained.geometry_eq
  exact ShiftedGeometry.Request.rowCeiling_le (prepared := source.prepared)
    (request := retained.requested.request) stored retained.geometry_eq laterIncrement order coordinate sourceIndex

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
