module
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-!
# Interior-point contact estimates in the actual shared face meshes

The endpoint lookups use the retained point bank and primitive values.
Both meshes consume the same common-path comparison, so differences of
chart transitions are controlled even when neither endpoint is a corner.
-/

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests.EnteredPath

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : InverseModels.BranchCellBank.FaceModels frames face}
  {start finish : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval
    start)} {ambient : Rational.Box}
  {path : Geometry.ClearPath curve.polynomial ambient start finish} {prepared :
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path owner}
  {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2}

/-- Read endpoint containment from the retained mesh owners. No new path
containment certificate is requested from the caller. -/
theorem endpoints_inside (entered : EnteredPaths.EnteredPath models prepared
  differential parentSheet) :
    face.cell.box.Contains start ∧ face.cell.box.Contains finish := by
  have first := (entered.domain.patch.cell_refines
    (entered.mesh.mesh.surface.owners entered.first).column (entered.mesh.mesh.surface.owners
      entered.first).row).contains
    (entered.mesh.mesh.surface.owner_inside entered.first)
  have last := (entered.domain.patch.cell_refines
    (entered.mesh.mesh.surface.owners entered.last).column (entered.mesh.mesh.surface.owners entered.last).row).contains
    (entered.mesh.mesh.surface.owner_inside entered.last)
  exact ⟨entered.first_eq ▸ first, entered.last_eq ▸ last⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests.EnteredPath

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests.ContactBudget

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start finish : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval
    start)} {ambient : Rational.Box}
  {path : Geometry.ClearPath curve.polynomial ambient start finish} {prepared :
    Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path owner}
  {differential : Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {first : EnteredPaths.EnteredPath firstModels prepared differential
    parentSheet}
  {last : EnteredPaths.EnteredPath lastModels prepared differential parentSheet}
    {target : Normalization.InverseRootPolynomial.Coordinate} {index : Nat}
  {leftData : PrimitiveData.DomainPrimitives first.domain differential index}
    {rightData : PrimitiveData.DomainPrimitives last.domain differential index}
  {leftPoints rightPoints : List Gaussian.Basic.Canonical} {leftTolerance rightTolerance :
    Normalization.InverseRootPolynomial.Coordinate}
  {leftBudget : CommonMeshes.DomainMeshBudget first.domain differential
    leftPoints leftTolerance}
  {rightBudget : CommonMeshes.DomainMeshBudget last.domain differential
    rightPoints rightTolerance}

/-- The two independent fine meshes read their actual cached owners and
values at both arbitrary contained endpoints. -/
theorem domain_mesh_accurate (budget : ContactRequests.ContactBudget first last
  target) (later : budget.index ≤ index)
    (left : CommonMeshes.DomainMeshReadings leftBudget leftData) (right :
      CommonMeshes.DomainMeshReadings rightBudget rightData)
    (leftStart : start ∈ leftPoints) (leftFinish : finish ∈ leftPoints)
    (rightStart : start ∈ rightPoints) (rightFinish : finish ∈ rightPoints) :
    Gaussian.Norm.Basic.normSq (((SharedValues.atPoint
      left.readings) finish - (SharedValues.atPoint left.readings) start)
      -
      ((SharedValues.atPoint right.readings) finish -
        (SharedValues.atPoint right.readings) start)) < target := by
  let firstCell := EnteredPaths.PeriodDomain.locate first.domain start
    (EnteredPath.endpoints_inside first).1
  let lastCell := EnteredPaths.PeriodDomain.locate first.domain finish
    (EnteredPath.endpoints_inside first).2
  let leftFirst := leftBudget.mesh.lookup start leftStart firstCell.column firstCell.row
    (Integration.PreparedParentSplitting.Geometry.allCells_mem first.domain.geometry _ _) firstCell.inside
  let leftLast := leftBudget.mesh.lookup finish leftFinish lastCell.column lastCell.row
    (Integration.PreparedParentSplitting.Geometry.allCells_mem first.domain.geometry _ _) lastCell.inside
  let firstOther := EnteredPaths.PeriodDomain.locate last.domain start
    (EnteredPath.endpoints_inside last).1
  let lastOther := EnteredPaths.PeriodDomain.locate last.domain finish
    (EnteredPath.endpoints_inside last).2
  let rightFirst := rightBudget.mesh.lookup start rightStart firstOther.column firstOther.row
    (Integration.PreparedParentSplitting.Geometry.allCells_mem last.domain.geometry _ _) firstOther.inside
  let rightLast := rightBudget.mesh.lookup finish rightFinish lastOther.column lastOther.row
    (Integration.PreparedParentSplitting.Geometry.allCells_mem last.domain.geometry _ _) lastOther.inside
  have leftFirstEq : leftBudget.mesh.surface.mesh.coordinate leftFirst.index = start := leftFirst.coordinate_eq
  have leftLastEq : leftBudget.mesh.surface.mesh.coordinate leftLast.index = finish := leftLast.coordinate_eq
  have rightFirstEq : rightBudget.mesh.surface.mesh.coordinate rightFirst.index = start := rightFirst.coordinate_eq
  have rightLastEq : rightBudget.mesh.surface.mesh.coordinate rightLast.index = finish := rightLast.coordinate_eq
  have estimate := ContactRequests.ContactBudget.points_accurate budget later
    leftData rightData
    left.readings.pointReadings right.readings.pointReadings
    leftFirst.index leftLast.index rightFirst.index rightLast.index
    leftFirst.coordinate_eq leftLast.coordinate_eq rightFirst.coordinate_eq rightLast.coordinate_eq
  change Gaussian.Norm.Basic.normSq ((left.readings.values leftLast.index - left.readings.values
    leftFirst.index) -
    (right.readings.values rightLast.index - right.readings.values rightFirst.index)) < target at estimate
  rw [← SharedValues.atPoint_coordinate left.readings leftFirst.index, ←
    SharedValues.atPoint_coordinate left.readings leftLast.index,
    ← SharedValues.atPoint_coordinate right.readings rightFirst.index, ←
      SharedValues.atPoint_coordinate right.readings rightLast.index,
    leftFirstEq, leftLastEq, rightFirstEq, rightLastEq] at estimate
  exact estimate

/-- A change in the difference of chart primitives is small along the
common prepared path. Individual chart constants need not be small. -/
theorem transition_accurate (budget : ContactRequests.ContactBudget first last
  target) (later : budget.index ≤ index)
    (left : CommonMeshes.DomainMeshReadings leftBudget leftData) (right :
      CommonMeshes.DomainMeshReadings rightBudget rightData)
    (leftStart : start ∈ leftPoints) (leftFinish : finish ∈ leftPoints)
    (rightStart : start ∈ rightPoints) (rightFinish : finish ∈ rightPoints) :
    Gaussian.Norm.Basic.normSq (((SharedValues.atPoint
      left.readings) finish - (SharedValues.atPoint right.readings)
      finish) -
      ((SharedValues.atPoint left.readings) start -
        (SharedValues.atPoint right.readings) start)) < target := by
  have equal : ((SharedValues.atPoint left.readings) finish -
    (SharedValues.atPoint right.readings) finish) -
      ((SharedValues.atPoint left.readings) start -
        (SharedValues.atPoint right.readings) start) =
      ((SharedValues.atPoint left.readings) finish -
        (SharedValues.atPoint left.readings) start) -
        ((SharedValues.atPoint right.readings) finish -
          (SharedValues.atPoint right.readings) start) := by ring1
  rw [equal]
  exact ContactBudget.domain_mesh_accurate budget later left
    right leftStart leftFinish rightStart rightFinish

/-- Transport the estimate to the original retained domains using their
sheet and cache-equality certificates; no numerical data are rebuilt. -/
theorem transition_accurate_of_domains (budget : ContactRequests.ContactBudget
  first last target) (later : budget.index ≤ index)
    {leftSheet rightSheet : Fin 2}
    (leftDomain : Periods.PeriodDomain firstModels leftSheet) (rightDomain :
      Periods.PeriodDomain lastModels rightSheet)
    (leftSheetEq : first.entry.sheet = leftSheet) (rightSheetEq : last.entry.sheet = rightSheet)
    (leftDomainEq : HEq first.domain leftDomain) (rightDomainEq : HEq last.domain rightDomain)
    {leftActualData : PrimitiveData.DomainPrimitives leftDomain differential
      index} {rightActualData : PrimitiveData.DomainPrimitives rightDomain
      differential index}
    {leftActualBudget : CommonMeshes.DomainMeshBudget leftDomain differential
      leftPoints leftTolerance}
    {rightActualBudget : CommonMeshes.DomainMeshBudget rightDomain differential
      rightPoints rightTolerance}
    (left : CommonMeshes.DomainMeshReadings leftActualBudget leftActualData)
      (right : CommonMeshes.DomainMeshReadings rightActualBudget
      rightActualData)
    (leftStart : start ∈ leftPoints) (leftFinish : finish ∈ leftPoints)
    (rightStart : start ∈ rightPoints) (rightFinish : finish ∈ rightPoints) :
    Gaussian.Norm.Basic.normSq (((SharedValues.atPoint
      left.readings) finish - (SharedValues.atPoint right.readings)
      finish) -
      ((SharedValues.atPoint left.readings) start -
        (SharedValues.atPoint right.readings) start)) < target := by
  cases leftSheetEq
  cases rightSheetEq
  cases eq_of_heq leftDomainEq
  cases eq_of_heq rightDomainEq
  exact ContactBudget.transition_accurate budget later left
    right leftStart leftFinish rightStart rightFinish

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshContactRequests.ContactBudget
