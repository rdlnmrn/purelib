module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Child
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
public import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Ordered integral Taylor sums on two actual absolute-time acquisitions

The two global preparations, actual occurrence maps and original Alignments
stay distinct. One retained common-pair vector and three existing polynomial
restriction banks feed stored common-child certificates. Original dyadic
restriction reassembly and nonnegative widths give one fixed-parent density,
independent of both acquired mesh counts and both absolute parameter times.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

/-- Read the SAME globally allocated whole preparation at an actual raw dyadic Mesh occurrence.

The existing raw-to-centered index and supplied original global occurrence
map are retained. The exact result type preserves the original parent,
covered patch, global Targets, floor, endpoint and query owners. This is
only the original PreparedParents.entry projection; no factory executes.
-/
@[expose] def dyadicPrepared
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    {targetParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {targetCover : CoveredParents count targetParents} {targetFloor : Nat}
    {targetStart targetFinish : LiftedPoint 2} {targetPath : LiftedPath 2 targetStart targetFinish}
    {targetStage : Nat} {targetTargets : CellEndpoints.Targets targetPath targetStage}
    (prepared : PreparedParents targetCover targetFloor targetTargets)
    (positions : Fin retained.parents.covered.parents.length → Fin targetParents.length)
    (index : Fin retained.acquired.mesh.edges.length) :
    PreparedParent (targetCover.entry (positions (retained.dyadicIndex index))).1 count targetFloor
      (targetCover.entry (positions (retained.dyadicIndex index))).2 targetTargets :=
  prepared.entry (positions (retained.dyadicIndex index))

/-- The six original fine restriction products of one retained acquisition at its actual global occurrences.

The existing dependent vector and RefinementRestrictions preserve every
original model, whole target allocation and ordered raw-mesh coordinate.
This exact type alias introduces no model or restriction data.
-/
@[expose] def DyadicRestrictionBanks
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    {targetParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {targetCover : CoveredParents count targetParents} {targetFloor : Nat}
    {targetStart targetFinish : LiftedPoint 2} {targetPath : LiftedPath 2 targetStart targetFinish}
    {targetStage : Nat} {targetTargets : CellEndpoints.Targets targetPath targetStage}
    (prepared : PreparedParents targetCover targetFloor targetTargets)
    (positions : Fin retained.parents.covered.parents.length → Fin targetParents.length)
    (additional : Nat) :=
  Data.Vector.DependentVector (fun channel : Fin 6 =>
    RefinementRestrictions retained.acquired.mesh.depth additional
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (retained.dyadicCells prepared positions channel))

/-- Materialize six original restriction products once before selecting a derivative row or bounded query.

Each actual coarse model retains its original Cached polynomial restriction
factory through RefinementRestrictions. No source, mesh, target allocation,
root continuation or arithmetic observation is reconstructed.
-/
def dyadicRestrictionBanks
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    {targetParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {targetCover : CoveredParents count targetParents} {targetFloor : Nat}
    {targetStart targetFinish : LiftedPoint 2} {targetPath : LiftedPath 2 targetStart targetFinish}
    {targetStage : Nat} {targetTargets : CellEndpoints.Targets targetPath targetStage}
    (prepared : PreparedParents targetCover targetFloor targetTargets)
    (positions : Fin retained.parents.covered.parents.length → Fin targetParents.length)
    (additional : Nat) : DyadicRestrictionBanks retained prepared positions additional :=
  Data.Vector.DependentVector.ofFn (fun channel : Fin 6 =>
    RefinementRestrictions.build retained.acquired.mesh.depth additional
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (retained.dyadicCells prepared positions channel))

/-- Read the original width at a common dyadic coordinate of two actual retained mesh depths. -/
@[expose] def betweenWidth (firstDepth lastDepth : Nat)
    (index : Fin (dyadicEdges (firstDepth + lastDepth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length) : Rational :=
  let edge := (dyadicEdges (firstDepth + lastDepth)
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[index.val]'index.isLt
  edge.right.parameter - edge.left.parameter

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (sourcePrepared : PreparedParent patch count floor covered targets)
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    (firstLinked : Linked sourcePrepared range firstFrame firstAdmitted firstStrip firstWidth)
    (lastLinked : Linked sourcePrepared range lastFrame lastAdmitted lastStrip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    {firstNewParents : List (CenteredEdge (Fibre.frameCurve firstFrame) basis)}
    {lastNewParents : List (CenteredEdge (Fibre.frameCurve lastFrame) basis)}
    {firstNewCover : CoveredParents count firstNewParents} {lastNewCover : CoveredParents count lastNewParents}
    {firstNewFloor lastNewFloor : Nat} {firstNewStart firstNewFinish lastNewStart lastNewFinish : LiftedPoint 2}
    {firstNewOriginal : LiftedPath 2 firstNewStart firstNewFinish}
    {lastNewOriginal : LiftedPath 2 lastNewStart lastNewFinish}
    {firstNewStage lastNewStage : Nat}
    {firstNewTargets : CellEndpoints.Targets firstNewOriginal firstNewStage}
    {lastNewTargets : CellEndpoints.Targets lastNewOriginal lastNewStage}
    (firstPrepared : PreparedParents firstNewCover firstNewFloor firstNewTargets)
    (lastPrepared : PreparedParents lastNewCover lastNewFloor lastNewTargets)
    (firstPositions : Fin firstLinked.shifted.parents.covered.parents.length → Fin firstNewParents.length)
    (lastPositions : Fin lastLinked.shifted.parents.covered.parents.length → Fin lastNewParents.length)
    (firstEntry_eq : ∀ index, firstNewParents[(firstPositions index).val]'(firstPositions index).isLt =
      firstLinked.shifted.childAt index)
    (lastEntry_eq : ∀ index, lastNewParents[(lastPositions index).val]'(lastPositions index).isLt =
      lastLinked.shifted.childAt index)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    (firstBudget : firstNewTargets.localBound ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (lastBudget : lastNewTargets.localBound ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (pairs : Data.Vector.DependentVector (fun index => RefinementPair
      firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index))

/-- One exact original common-child query family at its retained actual pair and both global preparation owners. -/
@[expose] def BetweenFamilyAt
    (index : Fin (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length) :=
  let found := pairs.get index
  { family : BetweenDyadicSamples sourcePrepared firstLinked lastLinked firstAligned lastAligned
    (firstLinked.shifted.dyadicPrepared firstPrepared firstPositions (refinementOccurrence.coarseIndex found.1))
    (lastLinked.shifted.dyadicPrepared lastPrepared lastPositions (refinementOccurrence.coarseIndex found.2))
    index found
    (firstEntry_eq (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.1)))
    (lastEntry_eq (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.2))) unit nonzero spatial
    (fun channel =>
      ((firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
        (refinementOccurrence.coarseIndex found.1)).cell_allowance channel).trans_le firstBudget)
    (fun channel =>
      ((lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
        (refinementOccurrence.coarseIndex found.2)).cell_allowance channel).trans_le lastBudget) //
    family = betweenDyadicSamples sourcePrepared firstLinked lastLinked firstAligned lastAligned
    (firstLinked.shifted.dyadicPrepared firstPrepared firstPositions (refinementOccurrence.coarseIndex found.1))
    (lastLinked.shifted.dyadicPrepared lastPrepared lastPositions (refinementOccurrence.coarseIndex found.2))
    index found
    (firstEntry_eq (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.1)))
    (lastEntry_eq (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.2))) unit nonzero spatial
    (fun channel =>
      ((firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
        (refinementOccurrence.coarseIndex found.1)).cell_allowance channel).trans_le firstBudget)
    (fun channel =>
      ((lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
        (refinementOccurrence.coarseIndex found.2)).cell_allowance channel).trans_le lastBudget) }

/-- The stored original query family at every SAME ordered common refined occurrence. -/
@[expose] def BetweenFamilies := Data.Vector.DependentVector (fun index =>
  BetweenFamilyAt sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
    firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial firstBudget lastBudget pairs index)

/-- Store one original Sample-family closure per common occurrence before any integral row is selected.

Each bounded query invocation genuinely constructs its own original work;
there is no claim of an infinite precache. The same stored family can feed
all four rows, retaining the ten-comparison sharing within each Sample.
Both Alignments are supplied original caches, not rerun per child or row.
-/
def betweenFamilies : BetweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstPositions lastPositions firstEntry_eq lastEntry_eq unit nonzero spatial
      firstBudget lastBudget pairs :=
  Data.Vector.DependentVector.ofFn (fun index =>
    let found := pairs.get index
    let family := betweenDyadicSamples sourcePrepared firstLinked lastLinked firstAligned lastAligned
      (firstLinked.shifted.dyadicPrepared firstPrepared firstPositions (refinementOccurrence.coarseIndex found.1))
      (lastLinked.shifted.dyadicPrepared lastPrepared lastPositions (refinementOccurrence.coarseIndex found.2))
      index found
      (firstEntry_eq (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.1)))
      (lastEntry_eq (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex found.2))) unit nonzero spatial
      (fun channel =>
        ((firstLinked.shifted.dyadicPrepared firstPrepared firstPositions
          (refinementOccurrence.coarseIndex found.1)).cell_allowance channel).trans_le firstBudget)
      (fun channel =>
        ((lastLinked.shifted.dyadicPrepared lastPrepared lastPositions
          (refinementOccurrence.coarseIndex found.2)).cell_allowance channel).trans_le lastBudget)
    ⟨family, rfl⟩)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
