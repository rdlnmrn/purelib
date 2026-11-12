module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Alignment
import Purelib.Geometry.Rational.Box.Refinement

/-! # Actual interior query alignment of a retained shifted Legendre acquisition

The original RootComparison retains one seed Budget, one first reference and
the SAME materialized shifted acquisition comparison cache. Its original
Step and seed-box refinement derive the starting relation. The actual finite
alignment is constructed once before query callbacks, with every original
moving Owner and stationary handoff preserved.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)

/-- Derive the complete alignment on the SAME original shifted comparison cache from its actual seed/Step certificates.

The actual first reference and its original box equation are retained.
The existing startEquivalent derives the initial signed relation; every
later relation is constructed from the materialized trace. This operation
accepts no desired interior-query or finishing relation.
-/
def align : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference :=
  comparison.paths.align comparison.firstReference
    (by
      rewrite [comparison.firstReference_box]
      exact Geometry.Rational.Box.refines_refl _)
    comparison.startEquivalent

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
