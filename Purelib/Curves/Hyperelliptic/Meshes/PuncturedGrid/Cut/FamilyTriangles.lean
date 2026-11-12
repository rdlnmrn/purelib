module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison
public import Purelib.Topology.Surface.Sewing.SewnPathRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
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
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Sewing

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

public section

/-!
# One sewn surface shared by an entire requested period family

All per-cycle views reuse the same materialized triangle values and the same
sewn surface. Equality transports change erased dependent indices only; they
do not build another polynomial, triangle bank, or sewing. The resulting
analytic comparisons refer to each original period program's actual sample.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus} {count :
    Nat}
  {programs : Data.Vector (CyclePrograms.CutCycleProgram lifted
    source) count}
  {domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Fin genus}

/-- Transport the same triangle readings across the retained domain, index and numerical-bank identities. -/
@[expose] public def atNumerics
    {firstDomains lastDomains : Face.DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars}
    {firstIndex lastIndex : Nat}
    {first : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) firstIndex firstDomains}
    {last : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) lastIndex lastDomains}
    (domainsEq : firstDomains = lastDomains) (indexEq : firstIndex = lastIndex) (numericsEq : HEq first last)
    (triangles : TrianglePrimitiveReadings.TriangleReadings first lifted.mesh) :
      TrianglePrimitiveReadings.TriangleReadings last lifted.mesh := by
  cases domainsEq
  cases indexEq
  cases eq_of_heq numericsEq
  exact triangles

/-- Transporting the original numerical-bank identities preserves the exact triangle-value vector. -/
public theorem atNumerics_values {firstDomains lastDomains :
  Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {firstIndex lastIndex : Nat}
    {first : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) firstIndex firstDomains}
    {last : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) lastIndex lastDomains}
    (domainsEq : firstDomains = lastDomains) (indexEq : firstIndex = lastIndex) (numericsEq : HEq first last)
    (triangles : TrianglePrimitiveReadings.TriangleReadings first lifted.mesh) :
    (FamilyTriangles.atNumerics domainsEq indexEq numericsEq triangles).values =
      triangles.values := by
  cases domainsEq
  cases indexEq
  cases eq_of_heq numericsEq
  rfl

/-- Transport the same cached sewn sample across the supplied equality of original triangle values. -/
@[expose] public def atValues {patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces}
    {first last : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} (equal :
      first = last)
    (surface : SewnPrimitiveSamples.CachedSample patch first) :
      SewnPrimitiveSamples.CachedSample patch last := by
  cases equal
  exact surface

/-- Transporting the original triangle-value equality preserves the exact sewn values. -/
public theorem atValues_values {patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces}
    {first last : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} (equal :
      first = last)
    (surface : SewnPrimitiveSamples.CachedSample patch first) :
      (FamilyTriangles.atValues equal surface).sewn.values = surface.sewn.values
      := by
  cases equal
  rfl

variable {family : PeriodFamilies.PrimitiveFamily programs domains differential}
  {targets : Data.Vector Readings.PreparedPrimitiveChargeBounds.Coordinate count}
  {surfaceFloor : Nat} {budget : PeriodFamilies.PrimitiveFamily.Budget family
    targets surfaceFloor} {minimumStages : Data.Vector Nat count}

namespace Requested

set_option genInjectivity false in
/-- One materialized triangle bank and cached sewn sample shared by the entire requested period family. -/
structure Sewn (requested : PeriodFamilies.PrimitiveFamily.Requested budget
  minimumStages) (patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces) where
  /-- The original triangle readings on the family's common numerical bank. -/ triangles :
    TrianglePrimitiveReadings.TriangleReadings requested.numerics lifted.mesh
  /-- The single cached sewn sample on those exact original readings. -/ surface :
    SewnPrimitiveSamples.CachedSample patch triangles.values

constructive_injectivity Sewn

/-- Sew the supplied original triangle bank once for the retained requested family. -/
@[expose] def sewWith (requested : PeriodFamilies.PrimitiveFamily.Requested
  budget minimumStages) (patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces)
    (triangles : TrianglePrimitiveReadings.TriangleReadings requested.numerics
      lifted.mesh) : Sewn requested patch :=
  ⟨triangles, SewnPrimitiveSamples.CachedSample.build patch triangles.values⟩

/-- Materialize the common original triangle readings once and retain their single sewn sample. -/
@[expose] def sew (requested : PeriodFamilies.PrimitiveFamily.Requested budget
  minimumStages) (patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces) :
  Sewn requested patch :=
  Requested.sewWith requested patch
    (TrianglePrimitiveReadings.TriangleReadings.build requested.numerics lifted.mesh)

namespace Sewn

variable {requested : PeriodFamilies.PrimitiveFamily.Requested budget
  minimumStages} {patch : SewingTree.SewnPatch lifted.mesh.triangulation.faces}

/-- A per-cycle view contains the original shared caches, not a new sewing. -/
@[expose] def atCycle (sample : Sewn requested patch)
  (index : Fin count) :
    TriangleComparison.RequestedPeriod.Sewn (requested.periods.get index) patch
      :=
  let triangles := FamilyTriangles.atNumerics (family.domains_eq
    index).symm (requested.indices_eq index).symm
    (requested.numerics_eq index).symm sample.triangles
  let equal := FamilyTriangles.atNumerics_values (family.domains_eq
    index).symm (requested.indices_eq index).symm
    (requested.numerics_eq index).symm sample.triangles
  ⟨triangles, FamilyTriangles.atValues (congrArg (fun values :
    Data.Vector (PrimitiveSewing.PrimitiveValues 3) lifted.mesh.triangles.length =>
    fun source => values source) equal.symm) sample.surface⟩

/-- The per-cycle view retains the exact original common triangle values. -/
theorem atCycle_triangles (sample : Sewn requested
  patch) (index : Fin count) :
    (sample.atCycle index).triangles.values = sample.triangles.values :=
      FamilyTriangles.atNumerics_values _ _ _ _

/-- The per-cycle view retains the exact original common sewn values. -/
theorem atCycle_surface_values (sample : Sewn requested
  patch) (index : Fin count) :
    (sample.atCycle index).surface.sewn.values = sample.surface.sewn.values :=
      FamilyTriangles.atValues_values _ _

/-- Every actual program sample compares with the single triangle bank
used by the surface, including heterogeneous and repeated cycle requests. -/
theorem program_accurate (sample : Sewn requested
  patch) (index : Fin count) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum
      ((TriangleComparison.AssignedSegments.sourceEdges (family.banks.get
      index).assigned).map
      (fun source => source.increment sample.triangles.values)) -
        (((programs index).program differential).integral.model (requested.periods.get
          index).sample.stage).integralSample) < targets index := by
  have accurate := (sample.atCycle index).program_accurate
  rw [sample.atCycle_triangles] at accurate
  exact accurate

end Sewn
end Requested

/-- A cached bank's semantic segment readback suffices; the family need
not be reconstructed by `ofSegments` at every accuracy request. -/
theorem original_accurate_of_bank_eq {prepared : CyclePrograms.CutCycleProgram
  lifted source}
    {bank : FaceBanks.FaceBank prepared} (segments :
      PeriodSegmentBanks.SegmentBank prepared.period)
    (equal : bank = FaceBanks.FaceBank.ofSegments prepared segments)
    {comparison : PeriodPrimitiveComparison.PrimitiveBank bank differential}
      {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat}
    (result : PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison
      target minimumStage)
    (triangles : TrianglePrimitiveReadings.TriangleReadings result.locals.numerics
      lifted.mesh) :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum (prepared.routed.spine.values (fun _
      route => route.sourceEdge.increment triangles.values)) -
      ((prepared.program differential).integral.model result.sample.stage).integralSample) < target := by
  subst bank
  exact DetourComparison.original_triangles_accurate result triangles

section SuppliedSegments

variable (segments : Vector.DependentVector (fun index =>
  PeriodSegmentBanks.SegmentBank (programs index).period))
  {budget : PeriodFamilies.PrimitiveFamily.Budget
    (PeriodFamilies.PrimitiveFamily.ofSegments segments domains differential)
    targets surfaceFloor}
  {requested : PeriodFamilies.PrimitiveFamily.Requested budget minimumStages}

/-- Generated segment preparations retain original-route increments even
when diagonal detours change the integration word's length. Every cycle is
compared with the very same materialized triangle values. -/
theorem ofSegments_original_program_accurate {patch : SewingTree.SewnPatch
  lifted.mesh.triangulation.faces}
    (sample : Requested.Sewn requested patch) (index : Fin count)
      :
    Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum ((programs index).routed.spine.values
      (fun _ route => route.sourceEdge.increment sample.triangles.values)) -
        (((programs index).program differential).integral.model (requested.periods.get
          index).sample.stage).integralSample) < targets index := by
  have accurate := FamilyTriangles.original_accurate_of_bank_eq (segments.get
    index)
    (PeriodFamilies.PrimitiveFamily.ofSegments_bank segments domains differential
      index) (requested.periods.get index) (sample.atCycle index).triangles
  rw [sample.atCycle_triangles] at accurate
  exact accurate

/-- The whole finite family compares actual cut jumps of one sewn surface
with the original period samples. Sewing allowances remain explicit; this
does not silently identify those jumps with periods or discard seam errors. -/
theorem ofSegments_path_program_bound (sample : Requested.Sewn
  requested lifted.cutPolygon.patch) (index : Fin count)
    (routedPositive : TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
      (programs index).routed.spine)
    (sources : SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      (programs index).cycle.path.cutEdges) (positive : sources.Positive) :
    Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values (programs index).cycle.finish -
      sample.surface.sewn.values (programs index).cycle.start) -
      (((programs index).program differential).integral.model (requested.periods.get
        index).sample.stage).integralSample) ≤
        2 * ((SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
          sources).bound + targets index) := by
  have aligned := TriangleSourceUniqueness.LiftedMesh.RouteSpine.sources_eq (programs
    index).routed.spine routedPositive sources.sources positive
    (sources.sources_project.trans (programs index).cycle.path.projection_eq.symm)
  apply (SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
    sources).compare_bound (programs index).cycle.path.endpoints
  rw [(SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
    sources).value_eq_sources, ← aligned,
    TriangleSourceUniqueness.LiftedMesh.RouteSpine.source_increments]
  exact (FamilyTriangles.ofSegments_original_program_accurate segments sample
    index).le

/-- Geometry-selected contact accuracy now pays the actual path allowance
in the whole-family period comparison. The independent analytic period
target and the full sewn-path target are both retained in the conclusion. -/
theorem ofSegments_path_program_accurate (sample : Requested.Sewn
  requested lifted.cutPolygon.patch) (index : Fin count)
    (routedPositive : TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
      (programs index).routed.spine)
    (sources : SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      (programs index).cycle.path.cutEdges) (positive : sources.Positive)
    {lengthBound : Nat} {pathTarget : Readings.PreparedPrimitiveChargeBounds.Coordinate}
    (request : SewnPathRequests.PathRequest lifted.cutPolygon.patch.assembly lengthBound
      pathTarget)
    (locallyAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance
      sample.surface.sewn.readings)
    (length_le : (programs index).cycle.path.cutEdges.length ≤ lengthBound) :
    Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values (programs index).cycle.finish -
      sample.surface.sewn.values (programs index).cycle.start) -
      (((programs index).program differential).integral.model (requested.periods.get
        index).sample.stage).integralSample) <
        2 * (pathTarget + targets index) :=
  open Purelib.Data.Rat in (Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.ofSegments_path_program_bound
    segments sample index routedPositive sources positive).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_right_direct
        (request.cached_accurate sample.surface locallyAccurate sources length_le) (targets index)))

end SuppliedSegments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
