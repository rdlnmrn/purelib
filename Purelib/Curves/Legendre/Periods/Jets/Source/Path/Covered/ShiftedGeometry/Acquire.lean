module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Parameter
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
import Purelib.Data.List.DependentProduct

/-! # Materialized shifted blocks from the exact retained old source preparations

The original covered patches, cached ranges and actual old source family are
inputs. Each endpoint Step, shifted acquisition, materialized owner trace and
root comparison is built once in the SAME dependent product before any
interior source/target query callback. No local shifted Targets are allocated.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Blocks

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (ShiftedAcquisition)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Build every genuine shifted block once from this SAME complete original source family and its factory identity.

The original cached endpoint Points are continued without reacquisition.
Each new whole-parent acquisition supplies its actual materialized trace
and original Parents. One root-comparison spine and linked open root chain
consume those SAME caches; the unchanged source and target allocations are
never retagged or inferred from endpoint labels.
-/
def build (prepared : PreparedParents covered floor targets)
    (fromFactory : prepared = prepareCovered covered floor targets)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq increment ≤ allocation.bound)
    (widths : Fin (firstParent :: remaining).length → AccuracyRequest) :
    Blocks (target := target) prepared ranges allocation admitted widths :=
  DependentProduct.ofFn (firstParent :: remaining) (fun index =>
    let first := ranges.firstStep prepared fromFactory index increment
      (admitted.trans allocation.bound_le_bound)
    let last := ranges.lastStep prepared fromFactory index increment
      (admitted.trans allocation.bound_le_bound)
    let shifted := ShiftedAcquisition.build (ranges.entry index) target
      (admitted.trans ((allocation.bound_le_entry index).trans
        (ranges.entry index).stripBound_le_shiftedBound)) first (widths index)
    let actual := shifted.acquired.traced.trace.get
    let comparison := ShiftedAcquisition.RootComparison.build
      (retained := shifted) (strip := admitted.trans (allocation.bound_le_entry index))
      (actual := actual) (actual_eq := rfl)
    ShiftedAcquisition.Linked.ofRetained first last shifted actual rfl comparison)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Blocks

end
