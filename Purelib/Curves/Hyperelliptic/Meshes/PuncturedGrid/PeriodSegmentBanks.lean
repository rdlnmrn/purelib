module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathDifferentialRecasting
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedCoveredParentLists

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid

public section

/-!
# Segment banks of the actual common-grid period programs

One bank decomposes the retained preparation for every standard differential.
The exact concatenated parent list is the recast initial list used by the
existing program, not a new integration path with the same endpoints.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid
  curve.polynomial ambient}
  {base : Purelib.Data.Gaussian.Basic.Canonical} {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    (curve.polynomial.eval base)} {source : Differential genus}

set_option genInjectivity false in
/-- A cached segment decomposition of the original prepared period walk.

The retained pieces share its exact prepared path, and cached segment and parent counts are certified against that
decomposition. -/
structure SegmentBank (period : PreparedGridPeriodPrograms.PeriodWalk grid base owner source) where
  /-- The covered segment pieces of the exact retained period preparation. -/ pieces : PreparedPath.CoveredSegments
    period.closed.traced.prepared
  /-- The cached number of retained segment pieces. -/ count : Nat
  /-- The cached segment count equals the decomposition count. -/ count_eq : count = pieces.count
  /-- The cached total number of original integration parents. -/ parentCount : Nat
  /-- The cached parent count equals the retained piece-parent count. -/ parentCount_eq : parentCount =
    CoveredSegments.parentCount pieces

constructive_injectivity SegmentBank

namespace SegmentBank

variable {period : PeriodWalk grid base owner source}

/-- Decompose the original covered period preparation and retain both segment and parent counts. -/
@[expose] def build (period : PreparedGridPeriodPrograms.PeriodWalk grid base owner source) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period :=
  let covered : PreparedClearPathModels.CoveredTracedPath period.closed.walk.path owner := ⟨period.closed.traced,
    period.closed.cover⟩
  let pieces := CoveredTracedPath.segments covered
  ⟨pieces, pieces.count, rfl, CoveredSegments.parentCount pieces, rfl⟩

/-- The retained segment-bank count equals the original grid walk edge count. -/
theorem count_eq_edges (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period) :
  bank.count = period.closed.walk.edgeCount := by
  rw [bank.count_eq, bank.pieces.count_eq, period.closed.walk.path_segmentCount]

/-- Each piece retains its actual original parent occurrences for every differential, including when the source and
target differentials differ. -/
theorem parents_eq (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period) (target :
  Differentials.Basic.Differential genus) :
    CoveredSegments.parents target 0 bank.pieces = period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge target) := by
  rw [CoveredSegments.parents_eq, period.initial_eq, RootClosedWalk.initial_parents,
    PreparedPathDifferentialRecasting.ofPreparedPath_recast]

/-- The retained parent-bank count equals the original initial period-state parent length. -/
theorem parentCount_eq_initial (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period)
  : bank.parentCount = period.initial.state.parents.length := by
  have count := CoveredSegments.parents_length source 0 bank.pieces
  rw [bank.parents_eq source, Purelib.Data.List.Map.length_map] at count
  exact bank.parentCount_eq.trans count.symm

/-- Split the actual cached integration parents and primitive patches. Recasting changes the numerator centers only, not
the retained root owners. -/
@[expose] def parentCaches (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period)
  (target : Differentials.Basic.Differential genus) :
    CoveredSegments.ParentCaches target 0 bank.pieces :=
  ParentCaches.build target 0 bank.pieces
    (period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge target)) (bank.parents_eq target).symm
    (CoveredParents.recast target period.covered)

/-- Flattening the retained per-piece parent caches gives exactly the original recast initial parents. -/
theorem parentCaches_parents (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period)
  (target : Differentials.Basic.Differential genus) :
    ParentCaches.parents (bank.parentCaches target) = period.initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge target) :=
  (ParentCaches.parents_eq (bank.parentCaches target)).trans (bank.parents_eq target)

/-- The very cells sampled by the original initial period program are the concatenated piece cells. This asserts no
equality with separately prepared programs and needs no independent owner-agreement premise. -/
theorem initial_cells (bank : Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank period)
  (differential : Fin genus) :
    ((period.program differential).integral.model 0).cells =
      (CoveredSegments.parents (PeriodMatrix.standardDifferential differential) 0 bank.pieces).map
        CenteredEdge.model := by
  rw [period.program_initial_cells, bank.parents_eq]

end SegmentBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
