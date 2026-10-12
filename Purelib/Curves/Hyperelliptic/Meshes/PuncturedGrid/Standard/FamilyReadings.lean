module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
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
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
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
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! Standard periods, an actual cut-program family, and its sewn surface
share one numerical primitive bank and one triangle vector. Prepared family
budgets contribute their floor before the standard bank is evaluated. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}
  {programs : Data.Vector (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted
    source) count}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily programs domains differential}
    {targets : Data.Vector Fraction.Rational count} {floor : Nat}

set_option genInjectivity false in
/-- One shared numerical reading bank for the original standard periods and retained cut-program family.

The family requests and sewn surface keep the standard bank's actual numerical data and triangle vector, with both
geometric and period stages certified. -/
structure FamilyReadings (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted
  integral index) (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets
  floor)
    (minimumStages : Data.Vector Nat count) (minimum : Nat) (target : Fraction.Rational) (extraPoints :
      List Gaussian.Basic.Canonical) where
  /-- The retained original standard-period readings. -/ standard :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential minimum
    target domains extraPoints
  /-- The common numerical stage is sufficient for the original family budget. -/ later : budget.index ≤
    standard.original.shared.numericalIndex
  /-- The original routed family chart requests. -/ charts :
    Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests budget
  /-- The shared numerical stage is sufficient for all retained chart requests. -/ charts_later : charts.index ≤
    standard.original.shared.numericalIndex
  /-- The cached component period stages. -/ stages : Data.Vector Nat count
  /-- Each component stage is the maximum of its supplied minimum and the original standard comparison stage. -/
    stages_eq : ∀ entry, stages entry = max (minimumStages entry) standard.original.comparison.stage
  /-- The original family request evaluated with those retained stages. -/ requested :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Requested
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests.atIndex budget standard.original.shared.numericalIndex
    later) stages
  /-- The family consumes exactly the standard readings' numerical bank. -/ numerics_eq : requested.numerics =
    standard.original.shared.numerics
  /-- The original family's sewn surface on the retained cut patch. -/ surface :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested.Sewn requested lifted.cutPolygon.patch
  /-- The sewn surface uses exactly the standard readings' triangle values. -/ triangles_eq : surface.triangles.values =
    standard.triangles.values

constructive_injectivity FamilyReadings

namespace FamilyReadings

variable {budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets floor}
  {minimumStages : Data.Vector Nat count}
  {minimum : Nat} {target : Fraction.Rational} {extraPoints : List Gaussian.Basic.Canonical}

/-- The family and its sewn surface consume the standard readings of the
supplied bank; all geometric requests were prepared before its stage. -/
@[expose] def readWith (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted
  integral index) (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets
  floor)
    (minimumStages : Data.Vector Nat count) (minimum : Nat) (target : Fraction.Rational)
    (extraPoints : List Gaussian.Basic.Canonical) (charts :
      Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests budget)
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.Preparation row
      differential minimum target domains extraPoints
      (max budget.index charts.index))
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
    (numericalLater : preparation.index ≤ stage) :
      FamilyReadings row budget minimumStages minimum target
      extraPoints := by
  let acquired := preparation.readWith numerics numericalLater
  let standard := acquired.val
  have floorLater : max budget.index charts.index ≤ standard.original.shared.numericalIndex :=
    acquired.property.2.2 ▸ standard.numericalFloor_le
  have later : budget.index ≤ standard.original.shared.numericalIndex := (Data.Nat.Order.le_max_left _ _).trans
    floorLater
  let raised := Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests.atIndex budget
    standard.original.shared.numericalIndex later
  let stages := Data.Vector.Basic.vectorOfFn (fun entry => max (minimumStages entry) standard.original.comparison.stage)
  let requested := raised.requestWith standard.original.shared.numerics stages
  let surface := Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.Requested.sewWith requested
    lifted.cutPolygon.patch standard.triangles
  exact ⟨standard, later, charts, (Data.Nat.Order.le_max_right _ _).trans floorLater, stages,
    Data.Vector.Basic.vectorOfFn_apply _, requested, rfl, surface, rfl⟩

/-- Shared-bank acquisition retains the supplied numerical bank, its stage and the maximum original family/chart floor.
-/
theorem readWith_shared (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted
  integral index) (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets
  floor)
    (minimumStages : Data.Vector Nat count) (minimum : Nat) (target : Fraction.Rational)
    (extraPoints : List Gaussian.Basic.Canonical) (charts :
      Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests budget)
    (preparation : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.Preparation row
      differential minimum target domains extraPoints
      (max budget.index charts.index))
    {stage : Nat} (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
    (numericalLater : preparation.index ≤ stage) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.SharedAt
      (readWith row budget minimumStages
        minimum target extraPoints charts preparation numerics numericalLater).standard
      numerics (max budget.index charts.index) :=
  (preparation.readWith numerics numericalLater).property

/-- Default acquisition uses the same prepare/read path as shared-bank clients. -/
@[expose] def build (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted integral
  index) (budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets floor)
    (minimumStages : Data.Vector Nat count) (minimum : Nat) (target : Fraction.Rational) (positive : 0 <
      target)
    (extraPoints : List Gaussian := []) : FamilyReadings row
      budget minimumStages minimum target extraPoints :=
  let charts := Hyperelliptic.Meshes.PuncturedGrid.FamilyRouteRequests.RouteRequests.build budget
  let preparation := Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings.prepare row
    differential minimum target positive domains extraPoints
    (max budget.index charts.index)
  readWith row budget minimumStages minimum
    target extraPoints charts preparation
    (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
      (Periods.PeriodMatrix.standardDifferential differential) preparation.index domains) le_rfl

/-- Every actual component sample stage is at least the original standard comparison stage. -/
theorem component_stage_later (readings : FamilyReadings row
  budget minimumStages minimum target extraPoints)
    (entry : Fin count) : readings.standard.original.comparison.stage ≤ (readings.requested.periods.get
      entry).sample.stage :=
  ((Data.Nat.Order.le_max_right _ _).trans_eq (readings.stages_eq entry).symm).trans
    (readings.requested.periods.get entry).sample.stage_ge

/-- Every actual component sample respects its supplied component minimum stage. -/
theorem requested_stage_later (readings : FamilyReadings row
  budget minimumStages minimum target extraPoints)
    (entry : Fin count) : minimumStages entry ≤ (readings.requested.periods.get entry).sample.stage :=
  ((Data.Nat.Order.le_max_left _ _).trans_eq (readings.stages_eq entry).symm).trans
    (readings.requested.periods.get entry).sample.stage_ge

/-- Each actual component program is compared with the triangle values used
by the standard periods, not a separately acquired bank at the same index. -/
theorem component_accurate (readings : FamilyReadings row
  budget minimumStages minimum target extraPoints)
    (entry : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges (family.banks.get
      entry).assigned).map
      (fun source => source.increment readings.standard.triangles.values)) -
      (((programs entry).program differential).integral.model (readings.requested.periods.get
        entry).sample.stage).integralSample) < targets entry := by
  have accurate := readings.surface.program_accurate entry
  rw [readings.triangles_eq] at accurate
  exact accurate

/-- The original component cycle word and its retained routed source increments satisfy the paid chart comparison on the
shared canonical readings. -/
theorem component_chart_accurate (readings : FamilyReadings
  row budget minimumStages minimum target extraPoints)
    (entry : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          readings.standard.triangles.values) (programs entry).cycle.path.surfaceEdges -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((programs entry).routed.spine.values fun _ route =>
        route.sourceEdge.increment readings.standard.triangles.values)) < targets entry :=
  readings.charts.accurate readings.charts_later readings.standard.triangles entry

/-- Two Gaussian comparisons at the same local target compose with a factor-four whole bound. -/
private theorem compose_component {value original sample : Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (chart : Data.Gaussian.Norm.Basic.normSq (value - original) < target) (period :
      Data.Gaussian.Norm.Basic.normSq (original - sample) < target) :
    Data.Gaussian.Norm.Basic.normSq (value - sample) < 4 * target := by
  rw [show value - sample = (value - original) + (original - sample) by ring1]
  exact ((Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct chart period))).trans_eq (by ring1)

/-- Original routed component words, including their diagonals, approximate
actual component samples on the shared canonical cochain. The displayed
factor pays both independently requested errors. -/
theorem cochain_component_accurate
    (segments : Data.Vector.DependentVector (fun entry =>
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (programs entry).period))
    {budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.ofSegments segments domains differential)
      targets floor}
    (readings : FamilyReadings row budget minimumStages
      minimum target extraPoints) (entry : Fin count) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          readings.standard.triangles.values) (programs entry).cycle.path.surfaceEdges -
      (((programs entry).program differential).integral.model (readings.requested.periods.get
        entry).sample.stage).integralSample) < 4 * targets entry := by
  have original := Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyTriangles.ofSegments_original_program_accurate segments
    readings.surface entry
  rw [readings.triangles_eq] at original
  exact compose_component
    (readings.component_chart_accurate entry) original

end FamilyReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
