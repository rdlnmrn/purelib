module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
public import Purelib.Approximation.Budget.RequestedLengthBudget
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib

open Purelib.Approximation.Budget

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences

open Purelib.Integration.Path

open Purelib.Topology.Polygon

public section

/-! Select physical-side query and owner budgets before sampling either bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds (PreOwnerBounds PreOwnerQueries)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence
    other target minimum}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

set_option genInjectivity false in
/-- The coarse side count includes every retained piece and intervening junction. Its coefficients do not depend on the
later primitive samples. -/
structure PhysicalOwnerBudget (plan : PairedSourceReferences.PairedSourcePlan occurrence other target minimum)
    (count : Nat) (requested : InverseRootPolynomial.Coordinate) where
  /-- The retained pre-acquisition density and source-slope bounds of the original paired plan. -/ bounds :
    FamilyBounds.PreOwnerBounds plan
  /-- The original fragment area budget paid at the count-weighted complete-family target. -/ area :
    PairedFragmentBlocks.FragmentAreaBudget bounds.density
    (JoinedFragmentFamily.familyLocalTarget (count + count + 1) plan.parents.slope requested)
  /-- The retained complete cell-query bank for the exact selected area tolerance. -/ queries :
    FamilyBounds.PreOwnerQueries occurrence other area.tolerance

constructive_injectivity PhysicalOwnerBudget

namespace PhysicalOwnerBudget
variable {count : Nat} {requested : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Prepare the complete physical-side density, count-weighted area tolerance and cell-query requirements before
numerical acquisition. -/
@[expose] def build (plan : PairedSourceReferences.PairedSourcePlan occurrence other target minimum)
    (count : Nat) (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested :=
  let bounds := PreOwnerBounds.build plan
  let area := JoinedFragmentFamily.familyAreaBudget (count + count + 1) plan.parents.slope
    bounds.density requested plan.parents.slope_nonnegative bounds.density_nonnegative positive
  ⟨bounds, area, PreOwnerQueries.build occurrence other area.tolerance⟩

/-- The common floor paying both the original source minimum and retained query bank. -/
@[expose] def sourceMinimum (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested) :
  Nat :=
  max minimum budget.queries.sourceMinimum

/-- Retain the original paired source plan at the common paid source floor. -/
@[expose] def refinedPlan (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested) :
    PairedSourceReferences.PairedSourcePlan occurrence other target budget.sourceMinimum :=
  FamilyBounds.withMinimum plan budget.sourceMinimum

/-- Transport the original cached pre-owner bounds to the refined source floor. -/
@[expose] def refinedBounds (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested) :
  FamilyBounds.PreOwnerBounds budget.refinedPlan :=
  budget.bounds.withMinimum budget.sourceMinimum

/-- Reuse the computed tolerance and only transport its scalar certificates. -/
@[expose] def refinedArea (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested) :
    PairedFragmentBlocks.FragmentAreaBudget budget.refinedBounds.density
      (JoinedFragmentFamily.familyLocalTarget (count + count + 1) budget.refinedPlan.parents.slope requested) := by
  let same := congrArg (fun slope => JoinedFragmentFamily.familyLocalTarget
    (count + count + 1) slope requested)
    (FamilyBounds.withMinimum_slope plan budget.sourceMinimum).symm
  exact ⟨budget.area.density_nonnegative, budget.area.tolerance,
    budget.area.tolerance_eq.trans (congrArg (fun value => Weighted.allowance value
      (320 * (4 * budget.bounds.density + 3) + 80 * budget.bounds.density)) same),
    budget.area.tolerance_positive, budget.area.paid.trans_eq same⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget in
set_option genInjectivity false in
/-- Each finite trace depth gets owner requests using the already selected query cap. Unit length allowances also cover
stationary owner junctions. -/
structure Owners (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget
  plan count requested) (edges : Nat) where
  /-- The requested unit-length budget for the retained physical trace's actual edge count. -/ piece :
    RequestedLengthBudget.Requested edges 1 budget.area.tolerance
  /-- The requested unit-length budget for one original stationary owner junction. -/ junction :
    RequestedLengthBudget.Requested 1 1 budget.area.tolerance
  /-- The retained paired owner request for the original physical-piece tolerance. -/ owners :
    PairedOwnerRequest.OwnerRequest occurrence other piece.budget.tolerance
  /-- The retained paired owner request for the original junction tolerance. -/ junctionOwners :
    PairedOwnerRequest.OwnerRequest occurrence other junction.budget.tolerance
  /-- The common face stage paying original query, piece-owner and junction-owner requests. -/ index : Nat
  /-- The common face stage is exactly the maximum of its three retained requirements. -/ index_eq : index = max
    budget.queries.faceIndex (max owners.index junctionOwners.index)

constructive_injectivity Owners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget in
/-- Prepare piece and junction owner requests at the original selected tolerance and cache their common paid face stage.
-/
@[expose] def owners (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested)
  (edges : Nat) : budget.Owners edges :=
  let piece := RequestedLengthBudget.requested edges 1 budget.area.tolerance (by decide) budget.area.tolerance_positive
  let junction := RequestedLengthBudget.requested 1 1 budget.area.tolerance (by decide) budget.area.tolerance_positive
  let owners := OwnerRequest.build occurrence other piece.budget.tolerance piece.budget.tolerance_positive
  let junctionOwners := OwnerRequest.build occurrence other junction.budget.tolerance junction.budget.tolerance_positive
  ⟨piece, junction, owners, junctionOwners,
    max budget.queries.faceIndex (max owners.index junctionOwners.index), rfl⟩

set_option genInjectivity false in
/-- Cache the refined plan before evaluating sources. Its certificates retain both the original cap and the original
query-index ownership. -/
structure Prepared (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget
  plan count requested) where
  /-- The cached original paired source plan at the common paid source floor. -/ plan :
    PairedSourceReferences.PairedSourcePlan occurrence other target budget.sourceMinimum
  /-- The cached source plan is exactly the original budget's floor refinement. -/ plan_eq : plan = budget.refinedPlan
  /-- The retained pre-acquisition density and source-slope bounds of the original paired plan. -/ bounds :
    FamilyBounds.PreOwnerBounds plan
  /-- The original fragment area budget paid at the count-weighted complete-family target. -/ area :
    PairedFragmentBlocks.FragmentAreaBudget bounds.density
    (JoinedFragmentFamily.familyLocalTarget (count + count + 1) plan.parents.slope requested)
  /-- The transported area budget retains the original computed tolerance. -/ tolerance_eq : area.tolerance =
    budget.area.tolerance
  /-- The retained complete cell-query bank for the exact selected area tolerance. -/ queries :
    FamilyBounds.PreOwnerQueries occurrence other area.tolerance
  /-- The retained query bank's source floor is paid by the common source minimum. -/ sourcePaid : queries.sourceMinimum
    ≤ budget.sourceMinimum
  /-- Transporting the source floor preserves the original query face stage. -/ face_eq : queries.faceIndex =
    budget.queries.faceIndex

constructive_injectivity Prepared

/-- Cache the refined original plan and transport its exact area and query certificates without recomputing tolerance.
-/
@[expose] def prepare (budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested) :
  budget.Prepared := by
  refine {
    plan := budget.refinedPlan
    plan_eq := rfl
    bounds := budget.refinedBounds
    area := budget.refinedArea
    tolerance_eq := ?_
    queries := ?_
    sourcePaid := ?_
    face_eq := ?_ }
  · dsimp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget.refinedArea]
  · dsimp only [Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget.refinedArea]
    exact budget.queries
  · exact Data.Nat.Order.le_max_right _ _
  · rfl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget in
/-- Pay a retained family from the preselected query floor and cap. -/
theorem Prepared.error_lt {budget :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget plan count requested}
  (prepared : budget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    {data : PairedFragmentValues.FirstData occurrence index} {otherData : PairedFragmentValues.SecondData occurrence
      other index}
    {Vertex : Type} {values : Vertex → Stokes.PrimitivePoint}
    {traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex}
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    (positive : 0 < requested) (facePaid : budget.queries.faceIndex ≤ index)
    (allowances : ∀ fragment ∈ family.fragments, fragment.allowance ≤ 1)
    (owners : ∀ fragment ∈ family.fragments, fragment.budget.tolerance ≤ budget.area.tolerance) :
    family.error < requested :=
  JoinedFragmentFamily.error_lt_of_queries family
    prepared.bounds positive prepared.area prepared.queries
    prepared.sourcePaid (prepared.face_eq.trans_le facePaid) allowances
    (fun fragment member => (owners fragment member).trans_eq prepared.tolerance_eq.symm)

namespace Owners
variable {budget : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest.PhysicalOwnerBudget
  plan count requested} {edges : Nat}

/-- The selected face stage pays the original cell-query bank. -/
theorem face_le (selected : budget.Owners edges) : budget.queries.faceIndex ≤ selected.index :=
  selected.index_eq ▸ Data.Nat.Order.le_max_left _ _

/-- The selected face stage pays the original piece-owner requests. -/
theorem owners_le (selected : budget.Owners edges) : selected.owners.index ≤ selected.index :=
  selected.index_eq ▸ (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The selected face stage pays the original junction-owner requests. -/
theorem junctionOwners_le (selected : budget.Owners edges) : selected.junctionOwners.index ≤ selected.index :=
  selected.index_eq ▸ (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

end Owners

end PhysicalOwnerBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
