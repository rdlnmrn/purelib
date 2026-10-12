module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.NewtonRawJoiningSchedule
import Purelib.Riemann.Topology.NewtonRawSewingSchedule
import Purelib.Riemann.Topology.NewtonRawSurfaceSchedule
public import Purelib.Riemann.RootContinuation.NewtonRawBoundarySchedule
public import Purelib.Riemann.Periods.NewtonRawPeriodSchedule
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Assemble the regular raw-energy requests once, retaining every geometric
owner and the common numerical threshold before sampling coefficients. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest

open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank)
  (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (radius : Fraction.Rational)
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

set_option genInjectivity false in
/-- The complete original regular raw-energy schedules over one retained Newton grid.

Sewing, surface, joining, boundary and period requests retain their actual owners and one sufficient numerical
threshold. -/
structure RegularRawRequest (newSheet : Fin 2) (floor : Nat) where
  /-- The actual retained Newton energy grid and protected observations. -/ grid :
    RootContinuation.NewtonRawEnergyGrid.RawEnergyGrid observations preparation radius
  /-- The original sewing schedule on the retained grid and supplied floor. -/ sewing :
    Topology.NewtonRawSewingSchedule.SewingSchedule grid floor
  /-- The original regular-surface schedule sharing that exact grid and cap bounds. -/ surface :
    Topology.NewtonRawSurfaceSchedule.SurfaceSchedule grid regular floor floor
  /-- The original joining schedule relating the retained surface and sewing owners. -/ joining :
    RootContinuation.NewtonRawJoiningSchedule.RawJoiningSchedule (paired := paired) surface sewing floor
  /-- The original boundary schedule using the retained surface, sewing and joining requests. -/ boundary :
    RootContinuation.NewtonRawBoundarySchedule.RawBoundarySchedule surface sewing joining floor
  /-- The actual original prepared-period schedule on the selected sheet and retained sewing owner. -/ period :
    Periods.NewtonRawPeriodSchedule.RawPeriodSchedule prepared sewing newSheet floor floor
  /-- The common sufficient numerical threshold of the retained period and boundary schedules. -/ index : Nat
  /-- The stored threshold equals the maximum original cut-period and boundary stages. -/ index_eq : index = max
    period.cut.index boundary.index
  /-- The original cut-period schedule is ready by the retained threshold. -/ period_le : period.cut.index ≤ index
  /-- The original boundary schedule is ready by the retained threshold. -/ boundary_le : boundary.index ≤ index

constructive_injectivity RegularRawRequest

namespace RegularRawRequest

/-- Prepare all original regular raw-energy schedules once and retain the maximum period and boundary stage. -/
@[expose] def build (grid : RootContinuation.NewtonRawEnergyGrid.RawEnergyGrid observations preparation radius)
    (newSheet : Fin 2) (floor : Nat) :
    Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations preparation radius regular
      newSheet floor :=
  let sewing := Topology.NewtonRawSewingSchedule.SewingSchedule.build grid floor
  let surface := Topology.NewtonRawSurfaceSchedule.SurfaceSchedule.build grid regular floor floor
  let joining := RootContinuation.NewtonRawJoiningSchedule.RawJoiningSchedule.build surface sewing floor
  let boundary := RootContinuation.NewtonRawBoundarySchedule.RawBoundarySchedule.build surface sewing joining floor
  let period := Periods.NewtonRawPeriodSchedule.RawPeriodSchedule.build prepared sewing newSheet floor floor
  ⟨grid, sewing, surface, joining, boundary, period, max period.cut.index boundary.index, rfl,
    Data.Nat.Order.le_max_left _ _, Data.Nat.Order.le_max_right _ _⟩

variable {prepared observations preparation radius regular} {newSheet : Fin 2} {floor : Nat}

/-- The supplied original floor is at most the retained common numerical stage. -/
theorem floor_le (request : Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations
  preparation radius regular newSheet floor) :
    floor ≤ request.index := request.period.cut.minimum_le.trans request.period_le

end RegularRawRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
