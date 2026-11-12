module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

/-! # Shifted endpoint agreement on adjacent original prepared parents

The original centered chain supplies exact physical incidence. The actual
RootChain supplies signed query agreement before the parameter changes.
The two retained PreparedParent caches supply their original independent
endpoint Points, and their existing Steps retain independent contour
payments. These original certificates derive the shifted seam comparison
without identifying roots by coordinates or sheet labels.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent next : CenteredEdge (Fibre.frameCurve frame) basis}
    {firstPatch : PreparedPatch parent} {nextPatch : PreparedPatch next} {count floor : Nat}
    {firstCovered : (firstPatch.neighborhood count).box.Contains (parent.edge.point 1)}
    {nextCovered : (nextPatch.neighborhood count).box.Contains (next.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (firstPrepared : PreparedParent firstPatch count floor firstCovered targets)
    (nextPrepared : PreparedParent nextPatch count floor nextCovered targets)
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {start finish : LiftedPoint 2}
    (geometry : CenteredPathChain (parent :: next :: remaining) (start := start) (finish := finish))
    {incoming returning : Named} (roots : RootChain (parent :: next :: remaining) incoming returning)

/-- Derive shifted same-point agreement from the actual adjacent original source caches and root chain.

The old source comparison composes firstPrepared.lastQueryEquivalent,
RootChain.nextEquivalent and nextPrepared.firstQueryEquivalent. Exact
physical incidence comes from the identical original geometric spine.
The existing retained Steps then use their own contour payments and
refinements through equivalent_of_source_eq. No preparation, query or
parameter advancement is executed by this operation.
-/
def shiftedNextEquivalent
    (lastStep : Variation.Point.Step firstPrepared.lastSample increment)
    (nextStep : Variation.Point.Step nextPrepared.firstSample increment) :
    NamedEquivalent lastStep.root.value.name nextStep.root.value.name := by
  have headStart : ∀ {left right : LiftedPoint 2},
      CenteredPathChain (next :: remaining) (start := left) (finish := right) → startPoint next = left := by
    intro left right retained
    cases retained
    rfl
  have incidence : finishPoint parent = startPoint next := by
    cases geometry with
    | cons _ tail => exact (headStart tail).symm
  have point_eq := congrArg (fun point : LiftedPoint 2 => point.coordinate) incidence
  have sources := firstPrepared.lastQueryEquivalent.symm.trans
    (roots.nextEquivalent.trans nextPrepared.firstQueryEquivalent)
  exact lastStep.equivalent_of_source_eq nextStep point_eq sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
