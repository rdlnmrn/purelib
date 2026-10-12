module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Riemann.Paths.PreparedTourSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedTourSources

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels

open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements

@[expose] public section

/-!
# Original source tours at every standard period stage

These certificates refer to the very tours used by the standard period
program, and carry their four original path groupings into every actual
scheduler stage.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SourceAncestry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Paths.PreparedTourSources (TourSources)
open Purelib.Riemann.Paths.PreparedTourSources.TourSources (refine)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index : Fin genus} (row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index)

/-- The actual initial A parent bank retains its original tour's four source-path groupings. -/
theorem a_initial_sources : PreparedTourSources.TourSources row.period.tours.aTour row.period.aInitial.state.parents :=
  by
  rw [row.period.aInitial_eq, OwnerClosedCyclePair.aInitial_state]
  exact TourSources.initial _ _

/-- The actual initial B parent bank retains its original tour's four source-path groupings. -/
theorem b_initial_sources : PreparedTourSources.TourSources row.period.tours.bTour row.period.bInitial.state.parents :=
  by
  rw [row.period.bInitial_eq, OwnerClosedCyclePair.bInitial_state]
  exact TourSources.initial _ _

/-- Every actual A scheduler stage retains the same original tour-source ancestry. -/
theorem a_stage_sources (stage : Nat) : PreparedTourSources.TourSources row.period.tours.aTour (row.period.aState
  stage).state.parents :=
  TourSources.refine (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SourceAncestry.a_initial_sources row)
    (RootClosedState.statesDirected
      row.period.aInitial (PreparedRefinementProgramCore.standardDifferentials genus) stage)

/-- Every actual B scheduler stage retains the same original tour-source ancestry. -/
theorem b_stage_sources (stage : Nat) : PreparedTourSources.TourSources row.period.tours.bTour (row.period.bState
  stage).state.parents :=
  TourSources.refine (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SourceAncestry.b_initial_sources row)
    (RootClosedState.statesDirected
      row.period.bInitial (PreparedRefinementProgramCore.standardDifferentials genus) stage)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SourceAncestry
