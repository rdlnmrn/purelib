module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
public import Purelib.Approximation.Budget.SynchronizedSamples
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Budget.SynchronizedSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh

open Purelib.Data.Rat

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

public section

/-!
# Shared common-stage readings of the actual cut-period programs

The earlier stages come from the original heterogeneous primitive requests.
Their finite maximum is selected once, then each component stream is read
once. All weighted rows can consume the same bank with exact sample readbacks.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.WeightedPeriods (Coordinate)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Approximation.Budget.SynchronizedSamples (StageRequest Samples)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.CutCycleChains (ClosedCutCycle)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgramBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Budget Requested)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
local notation "Vector" => Data.Vector
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests (ContactBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested (Sewn)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {count : Nat}
  {cycles : Vector (ClosedCutCycle
    lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels))) count}
  {bank : CutCycleProgramBank lifted source cycles}
    {differential : Fin genus}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars}
  {family : PrimitiveFamily bank.programs domains
    differential}
  {targets : Vector Coordinate count} {surfaceFloor : Nat} {budget :
    Budget family targets
    surfaceFloor}
  {minimumStages : Vector Nat count}

set_option genInjectivity false in
/-- One common-stage sample bank on the original heterogeneous cut-period requests.

The cached earlier stages come from the actual retained requests, and each original component stream is read once at
their shared maximum. -/
structure CommonSamples (components : ChainPeriods.ComponentSamples bank differential) (requested :
  PrimitiveFamily.Requested budget minimumStages) (floor : Nat) where
  /-- The cached original component request stages in cut-cycle order. -/ stages : Vector Nat count
  /-- Each cached earlier stage is exactly the corresponding retained period sample stage. -/ stages_eq : ∀ index,
    stages index = (requested.periods.get index).sample.stage
  /-- The actual common-stage samples of the original component streams above all retained stages and the caller floor.
  -/
  common : SynchronizedSamples.Samples components.streams stages floor

constructive_injectivity CommonSamples

namespace CommonSamples

variable {components : ComponentSamples bank
  differential} {requested :
  Requested budget minimumStages}
  {floor : Nat}

/-- Cache the original heterogeneous request stages and sample every actual component stream once at their shared
sufficient stage. -/
@[expose] def build (components : ChainPeriods.ComponentSamples bank differential) (requested :
  PrimitiveFamily.Requested budget minimumStages) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples components requested floor :=
  let stages := Data.Vector.Basic.vectorOfFn fun index => (requested.periods.get index).sample.stage
  ⟨stages, Data.Vector.Basic.vectorOfFn_apply _, Samples.build components.streams stages floor⟩

/-- Each retained earlier sample stage meets its original per-component minimum. -/
theorem requested_le (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples
  components requested floor) (index : Fin count) : minimumStages index ≤ sample.stages index := by
  rw [sample.stages_eq]
  exact (requested.periods.get index).sample.stage_ge

/-- Every actual common sample is exactly the original cut-period program's integral sample at the retained common
stage. -/
theorem values_eq_programs (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples
  components requested floor) (index : Fin count) :
    sample.common.values index = (((bank.programs index).program differential).integral.model
      sample.common.stage).integralSample := by
  rw [sample.common.values_eq, components.samples_eq]

/-- Every retained earlier stream reading is exactly the original cut-period sample at its actual request stage. -/
theorem earlier_eq_programs (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples
  components requested floor) (index : Fin count) :
    (components.streams index).sample (sample.stages index) =
      (((bank.programs index).program differential).integral.model (requested.periods.get
        index).sample.stage).integralSample := by
  rw [components.samples_eq, sample.stages_eq]

end CommonSamples

section SuppliedSegments

variable (segments : Purelib.Data.Vector.DependentVector (fun index =>
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (bank.programs index).period))
  {pairing : ProjectedEdgePairing
    lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary}
  {prepared : BoundaryContactPreparations
    lifted.cutPolygon.patch pairing
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) domains}
  {lengthBound : Nat} {pathTarget boundaryTarget : Coordinate}
  {contact : ContactBudget family prepared
    lengthBound pathTarget boundaryTarget targets surfaceFloor}
  {components : ComponentSamples bank differential}
    {movementTarget : Coordinate} {floors : Vector Nat count}
  {movement : StageRequest components.streams movementTarget floors}
  {requested : Requested
    contact.periods movement.stages} {floor : Nat}

/-- No analytic comparison is assumed here: it comes from the original segment requests and the single sewn surface. The
supplied source banks and their positive ownership are finite geometry prepared before accuracy. -/
theorem CommonSamples.path_accurate (common :
  CommonSamples components requested floor)
    (banks_eq : ∀ index, family.banks.get index = FaceBank.ofSegments (bank.programs index) (segments.get index))
    (surface : Requested.Sewn requested lifted.cutPolygon.patch)
    (sources : Data.Vector.DependentVector (fun index => SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      (bank.programs index).cycle.path.cutEdges))
    (positive : ∀ index, (sources.get index).Positive)
    (routedPositive : ∀ index, RouteSpine.Positive (bank.programs index).routed.spine)
    (length_le : ∀ index, (bank.programs index).cycle.path.cutEdges.length ≤ lengthBound) (index : Fin count) :
    Data.Gaussian.Norm.Basic.normSq ((surface.surface.sewn.values (bank.programs index).cycle.finish -
      surface.surface.sewn.values (bank.programs index).cycle.start) -
      common.common.values index) < 2 * (2 * (pathTarget + targets index) + movementTarget) := by
  apply common.common.comparison movement common.requested_le
    (fun index => surface.surface.sewn.values (bank.programs index).cycle.finish - surface.surface.sewn.values
      (bank.programs index).cycle.start)
    (fun index => 2 * (pathTarget + targets index)) ?_ index
  intro next
  rw [common.earlier_eq_programs]
  have original := FamilyTriangles.original_accurate_of_bank_eq (segments.get next) (banks_eq next)
    (requested.periods.get next) (surface.atCycle next).triangles
  rw [surface.atCycle_triangles] at original
  have aligned := RouteSpine.sources_eq (bank.programs next).routed.spine (routedPositive next) (sources.get
    next).sources (positive next)
    ((sources.get next).sources_project.trans (bank.programs next).cycle.path.projection_eq.symm)
  have originalBound : Data.Gaussian.Norm.Basic.normSq ((CachedSample.pathSample surface.surface (sources.get
    next)).value -
      (((bank.programs next).program differential).integral.model (requested.periods.get
        next).sample.stage).integralSample) ≤ targets next := by
    rw [(CachedSample.pathSample surface.surface (sources.get next)).value_eq_sources, ← aligned,
      RouteSpine.source_increments]
    exact original.le
  have compared := (CachedSample.pathSample surface.surface (sources.get next)).compare_bound (bank.programs
    next).cycle.path.endpoints originalBound
  exact compared.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (contact.path_bound surface (sources.get next) (length_le next)).le le_rfl) (by decide))

end SuppliedSegments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
