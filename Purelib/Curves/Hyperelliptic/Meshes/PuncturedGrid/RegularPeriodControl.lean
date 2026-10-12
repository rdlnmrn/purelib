module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularEnergyCompletion
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples.AllSurfacePreparation.Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBoundaryControl.AllSurfacePreparation

open Purelib.Data.List

open Purelib.Data.Rat

@[expose] public section

/-!
# Regular exterior controls on the original numerical period programs

The shared surface/cap request pays the source-program transport as well as
its physical boundary comparison. The returned period samples belong to the
original exterior programs and are small separately on each component. The
cap energy and the explicit surface-area correction come from the same bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (RegularBoundaryControl)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodSamples (ComponentPeriodTail
  ComponentPeriodSamples)
open Purelib.Riemann.Normalization
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- A shared regular exterior boundary acquisition with small numerical periods on every original component.

The same retained surface and cap bank supplies the energy correction and all period transports, which remain small at
every later paid stage. -/
structure RegularPeriodControl (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (target loss : InverseRootPolynomial.Coordinate) (floor minimumStage : Nat) where
  /-- The actual original regular boundary control at one sixteenth of the requested period target. -/ boundary :
    RegularBoundaryControl prepared (target / 16) loss floor
  /-- The original component period samples transported from that exact retained boundary acquisition. -/ periods :
    PeriodSamples.ComponentPeriodSamples boundary.acquired.sample boundary.acquired.shared boundary.acquired.plan.fine
    boundary.request.readingIndex boundary.request.localTarget boundary.request.budget.areaTarget floor
    boundary.components.groups (target / 16) minimumStage
  /-- Every actual retained component period sample has squared norm below the original target. -/ small : ∀ value ∈
    periods.values, Data.Gaussian.Norm.Basic.normSq value.period.sample < target
  /-- Every later original numerical period reading remains below the same target. -/ small_later : ∀ value ∈
    periods.values, ∀ stage, periods.stage ≤ stage →
    Data.Gaussian.Norm.Basic.normSq (((value.group.component.program.period.program
      differential.index).integral.model stage).integralSample) < target

constructive_injectivity RegularPeriodControl

namespace RegularPeriodControl

/-- Ten copies of one sixteenth of a positive rational target remain strictly below that target. -/
private theorem allowance_paid {target : InverseRootPolynomial.Coordinate} (positive : 0 < target) : 10 * (target / 16)
  < target := by
  have partPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 16)
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
      decide : (10 : InverseRootPolynomial.Coordinate) < 16) partPositive
  exact scaled.trans_eq ((by ring1 : 16 * (target / 16) = target / 16 * 16).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- The retained boundary and period-tail allowances bound the actual original component period reading at every paid
stage. -/
public theorem small_at {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {target loss :
  InverseRootPolynomial.Coordinate}
    {floor minimumStage : Nat} (positive : 0 < target)
    (boundary : RegularBoundaryControl prepared (target / 16) loss floor)
    (value : PeriodSamples.ComponentPeriodTail boundary.acquired.sample boundary.acquired.shared
      boundary.acquired.plan.fine
      boundary.request.readingIndex boundary.request.localTarget boundary.request.budget.areaTarget floor (target / 16)
        minimumStage)
    (groupMember : value.group ∈ boundary.components.groups)
    (stage : Nat) (later : value.tail.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (((value.group.component.program.period.program
      differential.index).integral.model stage).integralSample) < target := by
  let reading := ((value.group.component.program.period.program differential.index).integral.model stage).integralSample
  have sourceSmall := boundary.component_integrals_small value.group groupMember
  have countPaid := boundary.acquired.evaluated.source.component_error_paid boundary.components value.group groupMember
  have transport : Data.Gaussian.Norm.Basic.normSq (value.group.surface.total - reading) < 4 * (target / 16) :=
    (value.accurate stage later).trans ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_right_direct countPaid (target / 16))).trans_eq (by ring1))
  have reversed : Data.Gaussian.Norm.Basic.normSq (reading - value.group.surface.total) < 4 * (target / 16) :=
    by
    rw [show reading - value.group.surface.total = -(value.group.surface.total - reading) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact transport
  have normBound := Data.Gaussian.Norm.Bounds.normSq_add_le_two (reading - value.group.surface.total)
    value.group.surface.total
  rw [show reading - value.group.surface.total + value.group.surface.total = reading by ring1] at normBound
  exact normBound.trans_lt
    (((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct reversed sourceSmall)).trans_eq (by ring1)).trans
        (allowance_paid positive))

/-- Acquire the original regular boundary and all component period tails at one shared paid stage, retaining their
uniform later-stage bounds. -/
def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (target loss : InverseRootPolynomial.Coordinate) (positive : 0 < target) (lossPositive : 0 < loss)
    (floor minimumStage : Nat) : RegularPeriodControl
      prepared target loss floor minimumStage := by
  have localPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 16)
  let boundary := RegularBoundaryControl.build prepared degree (target / 16) loss localPositive lossPositive floor
  let periods := Evaluation.periodSamples
    boundary.acquired.evaluated.source boundary.components minimumStage
  have allLater : ∀ value ∈ periods.values, ∀ stage, periods.stage ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (((value.group.component.program.period.program
        differential.index).integral.model stage).integralSample) < target := by
    intro value member stage later
    have mapped : value.group ∈ periods.values.map (fun entry => entry.group) :=
      Map.mem_map.mpr ⟨value, member, rfl⟩
    have groupMember : value.group ∈ boundary.components.groups :=
      (congrArg (fun groups => value.group ∈ groups) periods.groups_eq).mp mapped
    exact small_at positive
      boundary value.toComponentPeriodTail groupMember stage (value.tail_stage_le.trans later)
  refine ⟨boundary, periods, ?_, allLater⟩
  intro value member
  rw [value.program_sample]
  exact allLater value member periods.stage le_rfl

end RegularPeriodControl
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
