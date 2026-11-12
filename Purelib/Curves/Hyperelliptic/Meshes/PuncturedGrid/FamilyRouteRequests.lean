module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-! Original component route words receive their own chart requests before
the shared numerical bank. No replacement detour word is substituted. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus} {count :
    Nat}
  {programs : Data.Vector (Cut.CyclePrograms.CutCycleProgram lifted
    source) count}
  {domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Fin genus}
  {family : Cut.PeriodFamilies.PrimitiveFamily programs domains differential}
  {targets : Data.Vector Fraction.Rational count} {floor : Nat}

/-- Each retained component period budget has a positive original target. -/
theorem target_positive (budget : Cut.PeriodFamilies.PrimitiveFamily.Budget family
  targets floor) (entry : Fin count) : 0 < targets entry := by
  let allocation := (budget.requests.get entry).allocation
  have equal : allocation.periodTarget * 4 = targets entry := by
    rw [allocation.periodTarget_eq]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact (Fraction.Order.Arithmetic.mul_pos_direct allocation.periodTarget_positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq equal

set_option genInjectivity false in
/-- Canonical chart requests for every retained component route word.

The dependent request vector follows the original finite component family and
its paid targets. Its cached common index suffices for every original component request. -/
structure RouteRequests (budget : Cut.PeriodFamilies.PrimitiveFamily.Budget family
  targets floor) where
  /-- The retained requests on the original component route spines and standard differential. -/ entries :
    Vector.DependentVector (fun entry : Fin count =>
    RouteChartRequests.RouteChartRequest (programs entry).routed.spine
      (Periods.PeriodMatrix.standardDifferential differential) domains (targets entry))
  /-- The cached common sufficient route comparison stage. -/ index : Nat
  /-- The cached stage is exactly the maximum of the retained component request stages. -/ index_eq : index =
    entries.maximum (fun _ request => request.index)

constructive_injectivity RouteRequests

namespace RouteRequests

variable {budget : Cut.PeriodFamilies.PrimitiveFamily.Budget family targets floor}

/-- Retain a canonical chart comparison for each original component route word and cache their maximum sufficient stage.
-/
@[expose] def build (budget : Cut.PeriodFamilies.PrimitiveFamily.Budget family
  targets floor) : RouteRequests budget :=
  let entries := Vector.DependentVector.ofFn (fun entry =>
    RouteChartRequests.RouteChartRequest.build
    (programs entry).routed.spine (Periods.PeriodMatrix.standardDifferential differential) domains (targets entry)
      (FamilyRouteRequests.target_positive budget entry))
  ⟨entries, entries.maximum (fun _ request => request.index), rfl⟩

/-- Each original component's canonical word valuation meets its retained target against the actual source-route
increment sum. -/
theorem accurate (requests : RouteRequests budget) {stage : Nat}
  (later : requests.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (entry
      : Fin count) :
    Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (programs
      entry).cycle.path.surfaceEdges -
      Gaussian.Norm.Sum.Basic.gaussianSum ((programs entry).routed.spine.values fun _ route =>
        route.sourceEdge.increment readings.values)) < targets entry :=
  (requests.entries.get entry).accurate
    ((requests.entries.get_le_maximum (fun _ request => request.index) entry).trans (requests.index_eq ▸ later))
      readings

end RouteRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests

end
