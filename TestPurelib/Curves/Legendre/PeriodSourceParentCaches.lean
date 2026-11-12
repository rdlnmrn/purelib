module

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Six source programmes from an actual retained parent cache

The original parent list supplies the executable geometric chain; its
prepared-path provenance is used only in erased proofs. The source
preparations are the original open-path producers, without a successful
chain or programme-comparison premise from the consumer.
-/

namespace TestPurelib.Curves.Legendre.PeriodSourceParentCaches

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments (ParentCaches)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Paths

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {ambient : Box} {start finish : Canonical}
    {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {prepared : CoveredTracedPath path owner} {sheet : Fin 2}

/-- Construct an original selected source programme from the actual stored parent cache and its original open endpoints.

The chain consumes the retained parent list. Each requested source stage is
prepared internally on that same coverage with the unchanged floor and
original target allocation; no endpoint acquisition is replayed to recover
the geometric chain.
-/
def fromParentCache (cache : ParentCache prepared basis sheet) (floor : Nat) (channel : Fin 6) :
    RefinementProgram :=
  let chain := cache.centeredChain
  PreparedParents.program cache.covered chain
    (fun index => prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path index)) channel

/-- The complete programme equals the original producer on any original chain for those same cached parents. -/
example (cache : ParentCache prepared basis sheet) (floor : Nat) (channel : Fin 6)
    (original : CenteredPathChain cache.parents
      (start := (⟨start, sheet⟩ : LiftedPoint 2)) (finish := ⟨finish, sheet⟩)) :
    fromParentCache cache floor channel =
      PreparedParents.program cache.covered original
        (fun index => prepareCovered cache.covered floor (CellEndpoints.Targets.build original.path index)) channel :=
  congrArg (fun chain => PreparedParents.program cache.covered chain
    (fun index => prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path index)) channel)
    (CenteredPathChain.eq cache.centeredChain original)

/-- Finite cuts read the complete original cells of every actual programme stage in their unchanged channel order. -/
example (cache : ParentCache prepared basis sheet) (floor : Nat) (channel : Fin 6) (index steps : Nat) :
    let chain := cache.centeredChain
    let retained := prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path index)
    let divided := PreparedParents.splitAt steps cache.covered retained
    ((fromParentCache cache floor channel).model index).cells =
      PreparedParents.cells divided.1 channel ++ PreparedParents.cells divided.2 channel := by
  intro chain retained divided
  change ((PreparedParents.program cache.covered chain
    (fun request => prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path request))
    channel).model index).cells = _
  rewrite [PreparedParents.program_model]
  change (PreparedParents.sources cache.covered retained chain).cells channel = _
  exact (PreparedParents.sources_cells cache.covered retained chain channel).trans
    (PreparedParents.cells_splitAt steps cache.covered retained channel)

/-- Actual saved segment views preserve the complete cells of every requested source programme stage.

The retained whole parent cache supplies the original segment provenance.
One source preparation is cut into the corresponding exact segment caches;
the readback preserves every original source occurrence and channel.
-/
example (cache : ParentCache prepared basis sheet) (floor : Nat) (channel : Fin 6) (index : Nat) :
    let pieces := PreparedPathDecomposition.CoveredTracedPath.segments prepared
    let same := cache.parents_eq.trans
      (PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents_eq basis sheet pieces).symm
    let caches := ParentCaches.build basis sheet pieces cache.parents same cache.covered
    let chain := cache.centeredChain
    let retained := prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path index)
    let views := PreparedParents.segmentSources pieces cache.parents same cache.covered retained
    ((fromParentCache cache floor channel).model index).cells =
      (PreparedParents.segmentCells pieces caches views channel).flatten := by
  intro pieces same caches chain retained views
  change ((PreparedParents.program cache.covered chain
    (fun request => prepareCovered cache.covered floor (CellEndpoints.Targets.build chain.path request))
    channel).model index).cells = _
  rewrite [PreparedParents.program_model]
  change (PreparedParents.sources cache.covered retained chain).cells channel = _
  exact (PreparedParents.sources_cells cache.covered retained chain channel).trans
    (PreparedParents.segmentSources_cells pieces cache.parents same cache.covered retained channel).symm

end TestPurelib.Curves.Legendre.PeriodSourceParentCaches
