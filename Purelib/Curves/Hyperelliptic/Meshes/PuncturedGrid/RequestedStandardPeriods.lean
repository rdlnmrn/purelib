module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarSums
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-!
# Automatic requested accuracy for the original standard periods

Geometric counts and scalar budgets are selected before the original A/B
request polynomials. The same retained domains then supply shared numerical
values with certified error below the requested tolerance on the whole tail.
-/

section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
open Purelib.Data.Rat
open Purelib.Riemann.Integration
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank (stepsBound)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank (FaceScalarBudgets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow (PrimitiveComparison)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover (CoveredPeriodStage)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (IndicesAbove)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments (GridFragments)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Rational} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods

set_option genInjectivity false in
/-- Geometry, original request polynomials, and their scalar certificates are prepared before the final numerical bank.
Later contact floors reuse this data without rerunning the original covered-stage preparation. -/
structure RequestedPreparation (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus)
    (minimum : Nat) (target : Fraction.Rational) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars) : Type 2 where
  /-- The cached finite bound on all original grid and analytic fragments. -/ pieces : Nat
  /-- The retained face scalar budgets for the original differential, fragment count and quarter target. -/ scalars :
    BranchCellBank.FaceScalarBudgets (PeriodMatrix.standardDifferential differential) pieces (target / 4) domains
  /-- The original A/B covered-period comparison prepared with the quarter target. -/ comparison :
    IntersectionRow.PrimitiveComparison row differential minimum (target / 4)
  /-- The actual shared-grid splitting of the original A/B primitive requests. -/ fragments :
    PeriodFragments.GridFragments comparison
  /-- The actual fragment sheet assignments on the original retained face domains. -/ assignments :
    GridFragments.SheetAssignments fragments domains
  /-- Every original A request polynomial is prepared above the retained common scalar stage. -/ a_indices :
    PreparedControlledPrimitiveRequests.IndicesAbove (FaceScalarBudgets.index scalars) comparison.a.request.requests
  /-- Every original B request polynomial is prepared above that same scalar stage. -/ b_indices :
    PreparedControlledPrimitiveRequests.IndicesAbove (FaceScalarBudgets.index scalars) comparison.b.request.requests
  /-- The actual A splitting and analytic step count are bounded by the retained fragment allowance. -/ a_count :
    fragments.a.splits.count * (2 * FaceDomainBank.stepsBound domains + 5) ≤ pieces
  /-- The actual B splitting and analytic step count are bounded by the retained fragment allowance. -/ b_count :
    fragments.b.splits.count * (2 * FaceDomainBank.stepsBound domains + 5) ≤ pieces

constructive_injectivity RequestedPreparation

set_option genInjectivity false in
/-- A total requested comparison of both original standard programs. All counts, selected indices, shared values and
verified error bounds are retained. -/
structure RequestedSharedReadings (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin
  genus)
    (minimum : Nat) (target : Fraction.Rational) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars)
    (extraPoints : List Data.Gaussian.Basic.Canonical) extends
      RequestedPreparation row differential minimum
      target domains where
  /-- The shared original A/B numerical readings on the retained domains, extra points and scalar floor. -/ shared :
    SharedPeriods.SharedReadings assignments (Aggregate.perTerm (target / 4) pieces / 64) extraPoints
    (FaceScalarBudgets.index scalars)
  /-- The retained A reading error is strictly below the original quarter target. -/ a_small : shared.a.bound < target /
    4
  /-- The retained B reading error is strictly below the original quarter target. -/ b_small : shared.b.bound < target /
    4

constructive_injectivity RequestedSharedReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation

/-- Every local request obtained from the retained original cover is above the supplied stage floor. -/
theorem ofCover_indices {source : Differentials.Basic.Differential genus}
    {root : PreparedRefinementRootChains.Named}
    {initial : PreparedRefinementRootEndpoints.RootClosedState curve source root}
    {targets : List (Differentials.Basic.Differential genus)} {count minimum : Nat}
    (cover : PreparedPeriodPrimitiveCover.CoveredPeriodStage initial targets count minimum) (differential :
      Differentials.Basic.Differential genus)
    (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    PreparedControlledPrimitiveRequests.IndicesAbove floor (CoveredPeriodRequest.ofCover cover differential target
      positive floor).request.requests := by
  let requested := CoveredPeriodRequest.ofCover cover differential target positive floor
  have equal : requested.request.minimumIndex = floor := ControlledSumRequest.acquire_minimumIndex ..
  exact equal ▸ requested.request.indices_ge

/-- Domain preparation and original coverage determine the sufficient finite scalar index. Neither original polynomial
bank is prepared twice. -/
@[expose] def build (row : TourIntersection.IntersectionRow lifted integral index) (differential : Fin genus) (minimum :
  Nat)
    (target : Fraction.Rational) (positive : 0 < target) (domains : DomainBanks.FaceDomainBank lifted.frames
      base.faces.regulars) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation row differential minimum
      target domains := by
  let aCover := CoveredPeriodStage.acquire row.period.aInitial (PreparedRefinementProgramCore.standardDifferentials
    genus) genus minimum
  let bCover := CoveredPeriodStage.acquire row.period.bInitial (PreparedRefinementProgramCore.standardDifferentials
    genus) genus minimum
  let parents := aCover.retained.current.state.parents.length + bCover.retained.current.state.parents.length
  let gridCount := base.bank.grid.vertical.length + base.bank.grid.horizontal.length + 1
  let analyticCount := 2 * FaceDomainBank.stepsBound domains + 5
  let pieces := parents * gridCount * analyticCount
  have smallPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let scalars := FaceScalarBudgets.build (PeriodMatrix.standardDifferential differential) pieces (target / 4)
    smallPositive domains
  let floor := FaceScalarBudgets.index scalars
  let a := CoveredPeriodRequest.ofCover aCover (PeriodMatrix.standardDifferential differential) (target / 4)
    smallPositive floor
  let b := CoveredPeriodRequest.ofCover bCover (PeriodMatrix.standardDifferential differential) (target / 4)
    smallPositive floor
  let comparison : IntersectionRow.PrimitiveComparison row differential minimum (target / 4) := ⟨a, b, max a.stage
    b.stage, rfl⟩
  let fragments := GridFragments.build comparison
  let assignments := fragments.assign domains
  have aIndices : PreparedControlledPrimitiveRequests.IndicesAbove floor comparison.a.request.requests :=
    ofCover_indices ..
  have bIndices : PreparedControlledPrimitiveRequests.IndicesAbove floor comparison.b.request.requests :=
    ofCover_indices ..
  have aCount : fragments.a.splits.count * analyticCount ≤ pieces := by
    have splitBound := fragments.a.splits.count_le
    simp only [fragments.axes.vertical_eq, fragments.axes.horizontal_eq, Map.length_map, -eq_self, -iff_self]
      at splitBound
    have parentCount : (comparison.a.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))).length ≤ parents :=
          by
      rw [Map.length_map]
      exact Nat.le_add_right _ _
    simp only [Map.length_map, -eq_self, -iff_self] at parentCount
    exact Nat.mul_le_mul_right analyticCount (splitBound.trans (Nat.mul_le_mul_right gridCount parentCount))
  have bCount : fragments.b.splits.count * analyticCount ≤ pieces := by
    have splitBound := fragments.b.splits.count_le
    simp only [fragments.axes.vertical_eq, fragments.axes.horizontal_eq, Map.length_map, -eq_self, -iff_self]
      at splitBound
    have parentCount : (comparison.b.cover.retained.current.state.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential differential))).length ≤ parents :=
          by
      rw [Map.length_map]
      exact Nat.le_add_left _ _
    simp only [Map.length_map, -eq_self, -iff_self] at parentCount
    exact Nat.mul_le_mul_right analyticCount (splitBound.trans (Nat.mul_le_mul_right gridCount parentCount))
  exact ⟨pieces, scalars, comparison, fragments, assignments, aIndices, bIndices, aCount, bCount⟩

/-- Read both actual period programs from the bank already used by the surface and observation consumers. The threshold
is computed by `build`. -/
@[expose] def readWith (prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation row differential minimum
  target domains)
    (positive : 0 < target) (extraPoints : List Data.Gaussian.Basic.Canonical) {stage : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains)
    (later : FaceScalarBudgets.index prepared.scalars ≤ stage) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedSharedReadings row differential minimum
      target domains extraPoints := by
  let points := (SheetEntries.points prepared.assignments.a ++ SheetEntries.points prepared.assignments.b) ++
    extraPoints
  let budgets := FaceScalarBudgets.meshes points prepared.scalars
  let meshes := FaceSharedMeshes.build budgets numerics
    ((FaceScalarBudgets.meshes_index prepared.scalars points).le.trans later)
  let shared : SharedPeriods.SharedReadings prepared.assignments
      (Aggregate.perTerm (target / 4) prepared.pieces / 64) extraPoints
      (FaceScalarBudgets.index prepared.scalars) :=
    ⟨points, rfl, budgets, stage, stage, by
      rewrite [FaceScalarBudgets.meshes_index]
      exact Nat.le_antisymm (Data.Nat.Order.le_max_left _ _)
        (Data.Nat.Order.max_le (Nat.le_refl _) (Data.Nat.Order.max_le later later)),
      numerics, meshes,
      SharedSum.build meshes prepared.assignments.a
        (fun _ member => List.mem_append_left _ (List.mem_append_left _ member)),
      SharedSum.build meshes prepared.assignments.b
        (fun _ member => List.mem_append_left _ (List.mem_append_right _ member))⟩
  have smallPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  exact ⟨prepared, shared,
    shared.a.bound_lt smallPositive later prepared.a_indices prepared.a_count,
    shared.b.bound_lt smallPositive later prepared.b_indices prepared.b_count⟩

/-- Reading with the supplied numerical bank preserves its exact original stage. -/
theorem readWith_index (prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation row differential minimum
  target domains)
    (positive : 0 < target) (extraPoints : List Data.Gaussian.Basic.Canonical) {stage : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains)
    (later : FaceScalarBudgets.index prepared.scalars ≤ stage) :
    (prepared.readWith positive extraPoints numerics later).shared.numericalIndex = stage := rfl

/-- Reading both retained periods reuses exactly the supplied original numerical bank. -/
theorem readWith_numerics (prepared :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation row differential minimum
  target domains)
    (positive : 0 < target) (extraPoints : List Data.Gaussian.Basic.Canonical) {stage : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) stage domains)
    (later : FaceScalarBudgets.index prepared.scalars ≤ stage) :
    HEq (prepared.readWith positive extraPoints numerics later).shared.numerics numerics := HEq.rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedPreparation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedSharedReadings

/-- A quarter-target local error pays the original two-part aggregate comparison target. -/
private theorem pay {error target : Fraction.Rational} (small : error < target / 4) : 2 * error + 2 * (target / 4) <
  target := by
  have bound := Fraction.Order.Arithmetic.add_lt_add_right_direct
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) small) (2 *
      (target / 4))
  exact bound.trans_eq (by
    rw [show 2 * (target / 4) + 2 * (target / 4) = (target / 4) * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- The retained shared A reading approximates the original standard A period throughout its requested stage tail. -/
theorem a_accurate {extraPoints : List Data.Gaussian.Basic.Canonical}
    (requested : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedSharedReadings row
      differential minimum target domains extraPoints)
    (stage : Nat) (later : requested.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (requested.shared.a.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target :=
  (requested.shared.a_accurate stage later).trans
    (pay requested.a_small)

/-- The retained shared B reading approximates the original standard B period throughout its requested stage tail. -/
theorem b_accurate {extraPoints : List Data.Gaussian.Basic.Canonical}
    (requested : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedSharedReadings row
      differential minimum target domains extraPoints)
    (stage : Nat) (later : requested.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (requested.shared.b.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target :=
  (requested.shared.b_accurate stage later).trans
    (pay requested.b_small)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods.RequestedSharedReadings

end
