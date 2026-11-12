module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sum
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Four actual two-target integral rows on retained global requested preparations

Both actual Requests pay the common local increment before query callbacks.
Their complete existing preparations and original occurrence maps supply all
model payments. One new common pair vector, six restriction banks on each
side and one shared Sample-family vector precede the four stored integral
rows. No source, target, alignment, continuation or checking is repeated.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (ShiftedGeometry)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

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
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    {firstPoint lastPoint : LiftedPoint 2} {firstRoot lastRoot : Named}
    {firstGeometry : ShiftedGeometry (parameter := parameter) (increment := firstOffset)
      (target := firstFrame) (basis := basis) (count := count) firstPoint firstPoint firstRoot firstRoot}
    {lastGeometry : ShiftedGeometry (parameter := parameter) (increment := lastOffset)
      (target := lastFrame) (basis := basis) (count := count) lastPoint lastPoint lastRoot lastRoot}
    {firstNonempty : firstGeometry.parents ≠ []} {lastNonempty : lastGeometry.parents ≠ []}
    {firstCurrent firstFloor firstRootStage lastCurrent lastFloor lastRootStage : Nat}
    (firstRequested : ShiftedGeometry.Requested firstGeometry firstNonempty firstCurrent firstFloor firstRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (lastRequested : ShiftedGeometry.Requested lastGeometry lastNonempty lastCurrent lastFloor lastRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)))
    (firstPositions : Fin firstLinked.shifted.parents.covered.parents.length →
      Fin (firstRequested.request.shape.val.1 :: firstRequested.request.shape.val.2).length)
    (lastPositions : Fin lastLinked.shifted.parents.covered.parents.length →
      Fin (lastRequested.request.shape.val.1 :: lastRequested.request.shape.val.2).length)
    (firstEntry_eq : ∀ index,
      (firstRequested.request.shape.val.1 ::
        firstRequested.request.shape.val.2)[(firstPositions index).val]'(firstPositions index).isLt =
        firstLinked.shifted.childAt index)
    (lastEntry_eq : ∀ index,
      (lastRequested.request.shape.val.1 ::
        lastRequested.request.shape.val.2)[(lastPositions index).val]'(lastPositions index).isLt =
        lastLinked.shifted.childAt index)

/-- Both original target Requests' common pairs, restriction banks, shared Sample families and all four integral rows.

The existing Sigma/Subtype and dependent-vector containers retain whole
factory identities on genuinely new auxiliary data. Original source/target
requests, geometry, positions and Alignments stay nominal inputs. The two
actual request allocation laws supply all numerical payments internally.
-/
@[expose] def BetweenRequested :=
  (pairs : { value : Data.Vector.DependentVector (fun index => RefinementPair
      firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index) //
    value = refinementPairs firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint }) ×
  (firstBanks : { value :
    DyadicRestrictionBanks firstLinked.shifted firstRequested.prepared firstPositions
      lastLinked.shifted.acquired.mesh.depth //
    value = dyadicRestrictionBanks firstLinked.shifted firstRequested.prepared firstPositions
      lastLinked.shifted.acquired.mesh.depth }) ×
  (lastBanks : { value :
    DyadicRestrictionBanks lastLinked.shifted lastRequested.prepared lastPositions
      firstLinked.shifted.acquired.mesh.depth //
    value = dyadicRestrictionBanks lastLinked.shifted lastRequested.prepared lastPositions
      firstLinked.shifted.acquired.mesh.depth }) ×
  (families : { value : BetweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le pairs.val //
    value = betweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le pairs.val }) ×
  Data.Vector.DependentVector (fun order : Fin 2 =>
    Data.Vector.DependentVector (fun coordinate : Fin 2 =>
      { value : BetweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le
        pairs.val families.val order coordinate
        (firstBanks.val.get (Specification.Table.baseIndex order coordinate))
        (lastBanks.val.get (Specification.Table.baseIndex order coordinate))
        (firstBanks.val.get (Specification.Table.slopeIndex order coordinate)) //
        value = BetweenIntegral.build sourcePrepared firstLinked lastLinked firstAligned lastAligned
          firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
          unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le
          pairs.val families.val order coordinate
          (firstBanks.val.get (Specification.Table.baseIndex order coordinate))
          (lastBanks.val.get (Specification.Table.baseIndex order coordinate))
          (firstBanks.val.get (Specification.Table.slopeIndex order coordinate)) }))

namespace BetweenRequested

/-- Materialize all actual auxiliary caches once and store four integral rows on the SAME original two requests.

The two shared Alignments and complete global preparations are supplied
unchanged. Only original pair/restriction/Sample/integral constructors run.
No final model allowance, integral identity, Taylor remainder, target
Completion, period relation or later Range bound is an input.
-/
def build : BetweenRequested sourcePrepared firstLinked lastLinked firstAligned lastAligned
    unit nonzero spatial firstRequested lastRequested firstPositions lastPositions firstEntry_eq lastEntry_eq :=
  let pairs := refinementPairs firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  let firstBanks :=
    dyadicRestrictionBanks firstLinked.shifted firstRequested.prepared firstPositions
      lastLinked.shifted.acquired.mesh.depth
  let lastBanks :=
    dyadicRestrictionBanks lastLinked.shifted lastRequested.prepared lastPositions
      firstLinked.shifted.acquired.mesh.depth
  let families := betweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le pairs
  let rows := Data.Vector.DependentVector.ofFn (fun order : Fin 2 =>
    Data.Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
      let row := BetweenIntegral.build sourcePrepared firstLinked lastLinked firstAligned lastAligned
        firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
        unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le
          pairs families order coordinate
        (firstBanks.get (Specification.Table.baseIndex order coordinate))
        (lastBanks.get (Specification.Table.baseIndex order coordinate))
        (firstBanks.get (Specification.Table.slopeIndex order coordinate))
      ⟨row, rfl⟩))
  ⟨⟨pairs, rfl⟩, ⟨firstBanks, rfl⟩, ⟨lastBanks, rfl⟩, ⟨families, rfl⟩, rows⟩

variable {sourcePrepared firstLinked lastLinked firstAligned lastAligned unit nonzero spatial}
    {firstRequested lastRequested firstPositions lastPositions firstEntry_eq lastEntry_eq}
    (retained : BetweenRequested sourcePrepared firstLinked lastLinked firstAligned lastAligned
    unit nonzero spatial firstRequested lastRequested firstPositions lastPositions firstEntry_eq lastEntry_eq)

/-- Read the SAME stored common refinement-pair vector with its complete original indices. -/
@[expose] def pairs : Data.Vector.DependentVector (fun index => RefinementPair
    firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index) := retained.1.val

/-- Read the SAME six first-side restriction banks without any canonical restriction replay. -/
@[expose] def firstBanks :
    DyadicRestrictionBanks firstLinked.shifted firstRequested.prepared firstPositions
      lastLinked.shifted.acquired.mesh.depth :=
  retained.2.1.val

/-- Read the SAME six last-side restriction banks with their independent target/model/allocation owners. -/
@[expose] def lastBanks :
    DyadicRestrictionBanks lastLinked.shifted lastRequested.prepared lastPositions
      firstLinked.shifted.acquired.mesh.depth :=
  retained.2.2.1.val

/-- Read the SAME shared bounded Sample-family vector before selecting an integral row. -/
@[expose] def families : BetweenFamilies sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
    unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le retained.pairs :=
  retained.2.2.2.1.val

/-- Read one SAME stored integral row with its three exact original cached restriction banks. -/
@[expose] def row (order coordinate : Fin 2) :
    BetweenIntegral sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstRequested.prepared lastRequested.prepared firstPositions lastPositions firstEntry_eq lastEntry_eq
      unit nonzero spatial firstRequested.localBound_lt.le lastRequested.localBound_lt.le
      retained.pairs retained.families order coordinate
      (retained.firstBanks.get (Specification.Table.baseIndex order coordinate))
      (retained.lastBanks.get (Specification.Table.baseIndex order coordinate))
      (retained.firstBanks.get (Specification.Table.slopeIndex order coordinate)) :=
  ((retained.2.2.2.2.get order).get coordinate).val

end BetweenRequested

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
