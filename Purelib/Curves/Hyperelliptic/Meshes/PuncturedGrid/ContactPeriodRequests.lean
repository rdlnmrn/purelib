module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContactErrors
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
import Purelib.Topology.Surface.Boundary.BoundaryDefectReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
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
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryContactSources
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh

open Purelib.Data.List

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryContactErrors

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPathRequests

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

open Purelib.Topology.Surface.Word

public section

/-!
# Automatic contact accuracy for one shared period-family surface

The geometry-selected path and exposed-boundary tolerances determine one
contact budget. Its common threshold is included in the period family's
index before any numerical face bank is sampled. Both the cut-jump/period
comparison and exposed-pair mismatch use the very same sewn surface.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (Coordinate)
open Purelib.Topology.Surface.Boundary.BoundaryContactErrors (BoundaryContactRequest)
open Purelib.Topology.Surface.Sewing.SewnPathRequests (PathRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (PathSources)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts (BoundaryContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies (PrimitiveFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily (Budget Requested ofSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested (Sewn)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {count : Nat}
  {programs : Data.Vector
    (CutCycleProgram lifted source) count}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Fin genus}
  {family : PrimitiveFamily programs domains
    differential} {patch : SewnPatch lifted.mesh.triangulation.faces}
  {pairing : ProjectedEdgePairing patch.cut.vertexLabels
    patch.cut.boundary}

set_option genInjectivity false in
/-- Geometry preparation is reusable across positive requests. Both the contact scalar caches and the cycle scalar
caches precede one shared sample. -/
structure ContactBudget (family : PeriodFamilies.PrimitiveFamily programs domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations patch pairing (PeriodMatrix.standardDifferential
      differential) domains)
    (lengthBound : Nat) (pathTarget boundaryTarget : PreparedPrimitiveChargeBounds.Coordinate) (targets :
      Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (floor : Nat) where
  /-- The retained sewn-path accuracy request using the original assembly and length bound. -/ path :
    SewnPathRequests.PathRequest patch.assembly lengthBound pathTarget
  /-- The original complete boundary-defect target is strictly positive. -/ boundary_positive : 0 < boundaryTarget
  /-- The cached number of actual original exposed cut pairs. -/ pairCount : Nat
  /-- The cache is exactly the original retained pairing's pair count. -/ pairCount_eq : pairCount =
    pairing.pairs.length
  /-- The cached per-pair allowance paying the complete original boundary target. -/ perPair :
    PreparedPrimitiveChargeBounds.Coordinate
  /-- The allowance is exactly the aggregate allocation using the original target and retained pair count. -/ perPair_eq
    : perPair = Aggregate.perTerm boundaryTarget pairCount
  /-- The retained exposed-boundary contact request at the cached per-pair allowance. -/ boundary :
    BoundaryContactErrors.BoundaryContactRequest patch.assembly perPair
  /-- The cached common local contact tolerance. -/ tolerance : PreparedPrimitiveChargeBounds.Coordinate
  /-- The tolerance is exactly the minimum of the original path and exposed-boundary tolerances. -/ tolerance_eq :
    tolerance = min path.tolerance boundary.tolerance
  /-- The actual contact request on the retained prepared geometry and common local tolerance. -/ contacts :
    ContactPreparations.Request prepared.prepared tolerance floor
  /-- The original period-family scalar budgets with the retained contact stage as their floor. -/ periods :
    PrimitiveFamily.Budget family targets contacts.index

constructive_injectivity ContactBudget

namespace ContactBudget

variable {prepared : BoundaryContactPreparations
  patch pairing (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential differential) domains}
  {lengthBound : Nat} {pathTarget boundaryTarget : Coordinate}
    {targets : Data.Vector Coordinate count}
    {floor : Nat}

/-- Cache path and exposed-pair budgets from the original sewing profile, then include their shared contact index before
selecting period-family numerics. -/
@[expose] def build (family : PeriodFamilies.PrimitiveFamily programs domains differential)
    (prepared : BoundaryContacts.BoundaryContactPreparations patch pairing (PeriodMatrix.standardDifferential
      differential) domains)
    (lengthBound : Nat) (pathTarget : PreparedPrimitiveChargeBounds.Coordinate) (pathPositive : 0 < pathTarget)
    (boundaryTarget : PreparedPrimitiveChargeBounds.Coordinate) (boundaryPositive : 0 < boundaryTarget)
    (targets : Data.Vector PreparedPrimitiveChargeBounds.Coordinate count) (positive : ∀ index, 0 < targets
      index) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family prepared lengthBound pathTarget
      boundaryTarget targets floor :=
  let path := PathRequest.ofProfile prepared.profile prepared.profile_eq lengthBound pathTarget pathPositive
  let pairCount := prepared.pairCount
  let perPair := Aggregate.perTerm boundaryTarget pairCount
  let boundary := BoundaryContactRequest.ofProfile prepared.profile prepared.profile_eq perPair
    (Aggregate.perTerm_positive boundaryPositive pairCount)
  let tolerance := min path.tolerance boundary.tolerance
  let contacts := ContactPreparations.Request.build prepared.prepared tolerance
    (Data.Rat.Fraction.Order.Basic.lt_min path.tolerance_positive boundary.tolerance_positive) floor
  ⟨path, boundaryPositive, pairCount, prepared.pairCount_eq, perPair, rfl, boundary, tolerance, rfl, contacts,
    Budget.build family targets positive contacts.index⟩

/-- The actual shared sewn surface satisfies the retained path-contact tolerance. -/
theorem localAccuracy (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family
  prepared lengthBound pathTarget boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) : SewnPrimitiveRequests.LocalAccuracy budget.path.tolerance
      sample.surface.sewn.readings :=
  prepared.localAccuracy budget.contacts (by
      rw [budget.tolerance_eq];
      exact Data.Rat.Fraction.Order.Basic.min_le_left _ _)
    budget.periods.surface_later sample.triangles sample.surface.sewn.readings

/-- Every actual retained cut path within the original length bound satisfies the paid path target on the same shared
sewn surface. -/
theorem path_bound (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family
  prepared lengthBound pathTarget boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) {edges : List (Stokes.OrientedEdge patch.cut.count)}
    (sources : SewnPrimitiveFaces.PathSources patch.cut edges) (length_le : edges.length ≤ lengthBound) :
    (CachedSample.pathSample sample.surface sources).bound < pathTarget :=
  budget.path.cached_accurate sample.surface (budget.localAccuracy sample) sources length_le

/-- Actual exposed cut-pair increments are small after every inherited sewing correction. Their two endpoints are not
identified or discarded. -/
theorem boundary_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family
  prepared lengthBound pathTarget boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (entry : Fin pairing.pairs.length) :
    BoundaryContactSources.mismatch
      (prepared.boundary.entries.get entry) sample.surface.sewn.values < budget.perPair :=
  prepared.boundary_accurate budget.boundary budget.contacts (by
      rw [budget.tolerance_eq];
      exact Data.Rat.Fraction.Order.Basic.min_le_right _ _)
    budget.periods.surface_later sample.triangles sample.surface.sewn.readings entry

/-- The bound is for the actual cached defect used by the full boundary decomposition, not a separately evaluated
surrogate contact. -/
theorem defect_accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family
  prepared lengthBound pathTarget boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (boundary : ProjectedEdgePairing.PrimitiveSample pairing
      sample.surface.energyValues)
    (entry : ProjectedEdgePair.Sample (labels := patch.cut.vertexLabels) sample.surface.energyValues) (member : entry ∈
      boundary.samples) :
    Data.Gaussian.Norm.Basic.normSq entry.defect.right < budget.perPair := by
  rw [BoundaryDefectReadings.defect_right_normSq entry
    sample.surface.sewn.values (fun vertex => by rw [sample.surface.energyValues_eq]; rfl)]
  have pairMember : entry.pair ∈ pairing.pairs := by
    rw [← boundary.pairs_eq]
    exact Map.mem_map_of_mem member
  rcases List.mem_iff_getElem.mp pairMember with ⟨position, bound, equal⟩
  have accurate := budget.boundary_accurate sample ⟨position, bound⟩
  unfold BoundaryContactSources.mismatch at accurate
  simpa only [equal] using accurate

/-- Both finite pair-count factors are paid. This controls the sum of the actual endpoint-jump defects; weighted area
defects and physical boundary areas remain distinct terms of the global Stokes identity. -/
theorem endpoint_defect_sum_accurate (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests.ContactBudget family prepared lengthBound pathTarget
  boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested patch) (boundary : ProjectedEdgePairing.PrimitiveSample pairing
      sample.surface.energyValues) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (boundary.samples.map (fun
      entry => entry.defect.right))) < boundaryTarget := by
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ budget.boundary_positive
  intro value member
  rcases Map.mem_map.mp member with ⟨entry, member, equal⟩
  rw [← equal]
  have lengthEq : boundary.samples.length = budget.pairCount := by
    have lengths := congrArg List.length boundary.pairs_eq
    rw [Data.List.Map.length_map] at lengths
    exact lengths.trans budget.pairCount_eq.symm
  rw [Data.List.Map.length_map, lengthEq, ← budget.perPair_eq]
  exact (budget.defect_accurate sample boundary entry member).le

end ContactBudget

/-- The original period programs and one actual sewn surface are compared with the full contact and path amplification
paid automatically. -/
theorem ofSegments_path_program_contact_accurate
    (segments : Data.Vector.DependentVector (fun index => PeriodSegmentBanks.SegmentBank (programs index).period))
    {pairing : ProjectedEdgePairs.ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    {prepared : BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch pairing
      (PeriodMatrix.standardDifferential differential) domains}
    {lengthBound : Nat} {pathTarget boundaryTarget : PreparedPrimitiveChargeBounds.Coordinate} {targets :
      Data.Vector PreparedPrimitiveChargeBounds.Coordinate count} {floor : Nat}
    (budget : ContactBudget (PrimitiveFamily.ofSegments
      segments domains differential) prepared lengthBound pathTarget boundaryTarget targets floor)
    {minimumStages : Data.Vector Nat count} {requested : PrimitiveFamily.Requested budget.periods
      minimumStages}
    (sample : Requested.Sewn requested lifted.cutPolygon.patch) (index : Fin count)
    (routedPositive : RouteSpine.Positive
      (programs index).routed.spine)
    (sources : SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut (programs index).cycle.path.cutEdges)
      (positive : sources.Positive)
    (length_le : (programs index).cycle.path.cutEdges.length ≤ lengthBound) :
    Data.Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values (programs index).cycle.finish -
      sample.surface.sewn.values (programs index).cycle.start) -
      (((programs index).program differential).integral.model (requested.periods.get
        index).sample.stage).integralSample) <
        2 * (pathTarget + targets index) :=
  FamilyTriangles.ofSegments_path_program_accurate
    segments sample index routedPositive sources positive budget.path (budget.localAccuracy sample) length_le

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPeriodRequests
