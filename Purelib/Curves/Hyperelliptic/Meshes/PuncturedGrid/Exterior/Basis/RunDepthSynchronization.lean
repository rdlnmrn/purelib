module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRunSchedule
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Riemann

public section

/-! Choose a common physical and reference depth from retained run requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization

open Purelib.Data

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

namespace CommonBasisPreparation

open Purelib.Data.Rat.Fraction.Compatibility

namespace ParentRunSchedules
variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {capacities : Fin prepared.occurrences.length → Nat} {requested : Normalization.InverseRootPolynomial.Coordinate}
    {minimum : Nat}
  (schedules :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunSourceSynchronization.CommonBasisPreparation.ParentRunSchedules
    retained inputs capacities requested minimum)

set_option genInjectivity false in
/-- The same finite depth may be used as the physical coarse depth and the
prepared common-cover floor. Requests retain their individual finer bounds. -/
structure DepthStage (floor : Nat) where
  /-- The common physical and prepared-reference depth. -/ depth : Nat
  /-- The depth is exactly the maximum of the supplied floor and all retained schedule depths. -/ depth_eq : depth = max
    floor (schedules.maximum (fun _ schedule => schedule.depth))

constructive_injectivity DepthStage

namespace DepthStage

/-- Compute the common depth paying the supplied floor and every original occurrence schedule. -/
@[expose] def build (floor : Nat) :
  ParentRunSchedules.DepthStage
  schedules floor :=
  ⟨max floor (schedules.maximum (fun _ schedule => schedule.depth)), rfl⟩

variable {schedules} {floor : Nat} (selected :
  ParentRunSchedules.DepthStage
  schedules floor)

/-- The prescribed depth floor is bounded by the selected common depth. -/
theorem floor_le : floor ≤ selected.depth :=
  (Nat.Order.le_max_left ..).trans_eq selected.depth_eq.symm

/-- Each original occurrence schedule depth is bounded by the selected common depth. -/
theorem depth_le (outer : Fin prepared.occurrences.length) : (schedules.get outer).depth ≤ selected.depth :=
  (schedules.get_le_maximum (fun _ schedule => schedule.depth) outer).trans
    ((Nat.Order.le_max_right ..).trans_eq selected.depth_eq.symm)

/-- Every retained parent refinement depth is bounded by the selected common depth. -/
theorem refinement_le (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    ((schedules.get outer).requests.get position).refinement.depth ≤ selected.depth :=
  ((schedules.get outer).refinement_le position).trans (selected.depth_le outer)

/-- A physical mesh at or beyond the common depth satisfies every retained parent request width. -/
theorem width_le (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    {physicalDepth : Nat} (later : selected.depth ≤ physicalDepth) :
    (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^physicalDepth ≤ ((schedules.get outer).requests.get
      position).refinement.width :=
  (schedules.get outer).width_le position ((selected.depth_le outer).trans later)

end DepthStage
end ParentRunSchedules
end CommonBasisPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunDepthSynchronization
