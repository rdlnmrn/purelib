module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-!
# Shared face-mesh readings of the original standard A/B periods

Both original request spines use one retained point bank and one numerical
index. Their certified sums target the original standard period programs at
every later stage, with the complete computed mesh-comparison errors exposed.
-/

section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments
open Purelib.Data.Rat
open Purelib.Riemann.Integration
open Purelib.Riemann.Periods

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow (PrimitiveComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments (GridFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodFragments.GridFragments (SheetAssignments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Rational} {comparison :
    PrimitiveComparison row
    differential minimum target}
  {fragments : GridFragments comparison}
    {domains : FaceDomainBank lifted.frames
    base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods

set_option genInjectivity false in
/-- Both original tours share the same domains, numerical bank and point meshes. Additional surface/observation points
remain in that same bank. -/
structure SharedReadings (assignments : GridFragments.SheetAssignments fragments domains) (tolerance :
  Fraction.Rational)
    (extraPoints : List Data.Gaussian.Basic.Canonical) (floor : Nat) where
  /-- The cached complete point list shared by both original fragment banks and supplied extra observations. -/ points :
    List Data.Gaussian.Basic.Canonical
  /-- The point cache is exactly the original A and B fragment point lists followed by the supplied extra points. -/
    points_eq : points =
    (SheetEntries.points assignments.a ++
      SheetEntries.points assignments.b) ++ extraPoints
  /-- The retained complete face-mesh requests on those exact points and original domains. -/ budgets :
    CommonMeshes.FaceMeshBudgets (PeriodMatrix.standardDifferential differential) points tolerance domains
  /-- The additional retained numerical stage floor. -/ extraFloor : Nat
  /-- The cached common numerical stage for both original tours and all shared point meshes. -/ numericalIndex : Nat
  /-- The common stage is exactly the maximum of the retained additional floor, caller floor and face-mesh request. -/
    numericalIndex_eq : numericalIndex = max extraFloor (max floor (FaceMeshBudgets.index budgets))
  /-- The actual shared differential primitive bank at that retained stage. -/ numerics :
    PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) numericalIndex domains
  /-- The complete retained face meshes consuming that same actual primitive bank. -/ meshes :
    CommonMeshes.FaceSharedMeshes budgets numerics
  /-- The actual original A fragment sum on these retained shared meshes. -/ a : SheetEntries.SharedSum meshes
    assignments.a
  /-- The actual original B fragment sum on those same retained shared meshes. -/ b : SheetEntries.SharedSum meshes
    assignments.b

constructive_injectivity SharedReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods

variable {assignments :
  SheetAssignments fragments
  domains} {tolerance : Rational} {extraPoints : List Purelib.Data.Gaussian.Basic.Canonical}
  {floor : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings

/-- The retained common numerical stage meets the original caller floor. -/
theorem numericalIndex_ge (shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings
  assignments tolerance extraPoints floor) : floor ≤ shared.numericalIndex := by
  rw [shared.numericalIndex_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The retained common numerical stage meets its additional stored floor. -/
theorem extraFloor_le (shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings
  assignments tolerance extraPoints floor) : shared.extraFloor ≤ shared.numericalIndex := by
  rw [shared.numericalIndex_eq]
  exact Data.Nat.Order.le_max_left _ _

/-- The explicit residual includes every analytic-piece count and both outer fragment-count factors. No smallness claim
is inferred from closure. -/
theorem a_accurate (shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings assignments
  tolerance extraPoints floor)
    (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (shared.a.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) <
        2 * shared.a.bound + 2 * target := by
  have mesh := shared.a.accurate
  rw [← comparison.a.request.increments_eq, ← comparison.a.request.primitiveSum_eq] at mesh
  have period := comparison.a_accurate stage later
  have identity : shared.a.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample =
      (shared.a.value - comparison.a.request.primitiveSum) + (comparison.a.request.primitiveSum -
        (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
          stage).integralSample) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_right_direct mesh _).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct period _))).trans_eq (by ring1))

/-- The actual shared B fragment sum estimates the original standard B period with its complete computed mesh residual
and requested tail error. -/
theorem b_accurate (shared : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings assignments
  tolerance extraPoints floor)
    (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (shared.b.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) <
        2 * shared.b.bound + 2 * target := by
  have mesh := shared.b.accurate
  rw [← comparison.b.request.increments_eq, ← comparison.b.request.primitiveSum_eq] at mesh
  have period := comparison.b_accurate stage later
  have identity : shared.b.value -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample =
      (shared.b.value - comparison.b.request.primitiveSum) + (comparison.b.request.primitiveSum -
        (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
          stage).integralSample) := by ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_right_direct mesh _).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct period _))).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods.SharedReadings

end
