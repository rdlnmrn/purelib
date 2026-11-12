module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Requested
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Position.Cells
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
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

/-! # Two actual absolute-target integral rows in original global programme order

The original Position products identify each actual global target word
with its retained local child occurrences. The already stored per-parent
BetweenRequested rows provide the same pair/restriction/Sample/integral
caches. Original finite weighted summation reads those parent certificates
without another query or polynomial restriction. All four rows retain
both independent target Requests and the original fixed-parent factors.
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

/-- The SAME stored four integral rows at every original parent and its exact two global occurrence families.

The original products retain both target frames and complete Requests.
Each entry is the existing BetweenRequested cache, including its original
common pair vector, two six-channel restriction products, shared Sample
families and four integral rows with all whole factory certificates.
-/
@[expose] def BetweenRows := DependentProduct (parent :: remaining) (fun outer =>
  BetweenRequested (prepared.entry outer)
    (DependentProduct.get (parent :: remaining) firstBlocks outer)
    (DependentProduct.get (parent :: remaining) lastBlocks outer)
    (DependentProduct.get (parent :: remaining) firstAligned outer)
    (DependentProduct.get (parent :: remaining) lastAligned outer)
    unit nonzero spatial firstRequested lastRequested
    (fun inner => (firstPositions.entry outer inner).sourceIndex)
    (fun inner => (lastPositions.entry outer inner).sourceIndex)
    (fun inner => (firstPositions.entry outer inner).property.1)
    (fun inner => (lastPositions.entry outer inner).property.1))

namespace BetweenRows

/-- Construct each original parent's existing requested-row cache once in the original parent order.

Both Position and Alignment products precede this producer. It invokes only
the existing BetweenRequested builder once per parent; no source, target,
mesh, global Target allocation, Alignment or completion is executed again.
-/
def build : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
    firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
    firstPositions lastPositions firstAligned lastAligned :=
  DependentProduct.ofFn (parent :: remaining) (fun outer =>
    BetweenRequested.build (prepared.entry outer)
      (DependentProduct.get (parent :: remaining) firstBlocks outer)
      (DependentProduct.get (parent :: remaining) lastBlocks outer)
      (DependentProduct.get (parent :: remaining) firstAligned outer)
      (DependentProduct.get (parent :: remaining) lastAligned outer)
      unit nonzero spatial firstRequested lastRequested
      (fun inner => (firstPositions.entry outer inner).sourceIndex)
      (fun inner => (lastPositions.entry outer inner).sourceIndex)
      (fun inner => (firstPositions.entry outer inner).property.1)
      (fun inner => (lastPositions.entry outer inner).property.1))

variable {prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths firstBlocks lastBlocks}
    {unit nonzero spatial firstRequested lastRequested firstPositions lastPositions firstAligned lastAligned}
    (rows : BetweenRows prepared ranges allocation firstAdmitted lastAdmitted firstWidths lastWidths
      firstBlocks lastBlocks unit nonzero spatial firstRequested lastRequested
      firstPositions lastPositions firstAligned lastAligned)

/-- Read one SAME stored original parent's complete actual two-target row cache. -/
@[expose] def entry (outer : Fin (parent :: remaining).length) :
    BetweenRequested (prepared.entry outer)
      (DependentProduct.get (parent :: remaining) firstBlocks outer)
      (DependentProduct.get (parent :: remaining) lastBlocks outer)
      (DependentProduct.get (parent :: remaining) firstAligned outer)
      (DependentProduct.get (parent :: remaining) lastAligned outer)
      unit nonzero spatial firstRequested lastRequested
      (fun inner => (firstPositions.entry outer inner).sourceIndex)
      (fun inner => (lastPositions.entry outer inner).sourceIndex)
      (fun inner => (firstPositions.entry outer inner).property.1)
      (fun inner => (lastPositions.entry outer inner).property.1) :=
  DependentProduct.get (parent :: remaining) rows outer

end BetweenRows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
