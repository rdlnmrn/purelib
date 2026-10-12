module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.RadialTriangles

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# Requested odd energy for the complete acquired exterior path

The actual connected chart acquisition supplies every parent and reading.
One shared bound cache and common radial depth produce its full signed
energy. Original cell and parent counts are paid by the existing requests.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide (ConnectedRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts (ChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests (EnergyPreparations EnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy (EnergyConnection)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular parents}
    {totalTarget areaTarget target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared totalTarget
    areaTarget minimum}
  {charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest request target}
  {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {plan :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan charts sample}

set_option genInjectivity false in
/-- A common coefficient cache and retained parent fan requests for the complete acquired exterior path.

The original parent count pays the shared positive energy allowance before any common-depth fan is evaluated. -/
structure EnergyPreparation (evaluated : Plan.Evaluation plan depth readingIndex) (energyTarget :
  InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The cached energy allowance per actual original parent. -/ allowance : InverseRootPolynomial.Coordinate
  /-- The allowance is the target divided by the original parent count plus one. -/ allowance_eq : allowance =
    energyTarget / ((parents.length : InverseRootPolynomial.Coordinate) + 1)
  /-- The retained common parent allowance is strictly positive. -/ allowance_positive : 0 < allowance
  /-- The original parent count times the allowance is strictly below the whole energy target. -/ allowance_paid :
    (parents.length : InverseRootPolynomial.Coordinate) * allowance < energyTarget
  /-- The shared original cap-polynomial coefficient bounds on the radial domain. -/ bounds : Cap.EnergyBounds
    sample RootRadialGeometry.domain
  /-- The actual original parent fan requests on the acquired chart replacements. -/ preparations :
    SideEnergyRequests.EnergyPreparations allowance energyFloor evaluated.original.separated.parents
    evaluated.replacements
  /-- The cached maximum of the original parent fan depths. -/ minimum : Nat
  /-- The common depth threshold is the actual retained preparation maximum. -/ minimum_eq : minimum =
    preparations.maximum evaluated.original.separated.parents evaluated.replacements

constructive_injectivity EnergyPreparation

set_option genInjectivity false in
/-- The complete retained odd-energy evaluation at one common radial depth.

Every original parent fan shares the cached parameters; the connected summary retains all actual potential and
inter-parent corrections. -/
structure RequestedEnergy (evaluated : Plan.Evaluation plan depth readingIndex) (energyTarget :
  InverseRootPolynomial.Coordinate) (energyFloor : Nat)
    extends Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation evaluated energyTarget
      energyFloor where
  /-- The actual common radial depth used for all original parent fans. -/ depth : Nat
  /-- The common radial depth pays the original preparation maximum. -/ depth_later : minimum ≤ depth
  /-- The retained radial parameter mesh at that exact common depth. -/ parameters : RadialTriangles.Parameters depth
  /-- The actual original parent energy evaluations at the retained common depth. -/ parents :
    SideEnergyRequests.EnergyData allowance energyFloor depth evaluated.original.separated.parents
    evaluated.replacements
  /-- The cached complete connected energy summary starting at the original source value. -/ connected :
    SideEnergy.EnergyConnection evaluated.original.separated.parents evaluated.replacements parents
    evaluated.original.firstValue

constructive_injectivity RequestedEnergy

namespace Evaluation

/-- Prepare every parent from a supplied shared bound cache before any fan is generated. -/
@[expose] def prepareEnergy (evaluated : Plan.Evaluation plan depth readingIndex)
    (bounds : Cap.EnergyBounds sample RootRadialGeometry.domain)
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation evaluated energyTarget energyFloor
      := by
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ (parents.length : InverseRootPolynomial.Coordinate)
    := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : 0 < (parents.length : InverseRootPolynomial.Coordinate) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct countNonnegative (by decide)
  let allowance := energyTarget / ((parents.length : InverseRootPolynomial.Coordinate) + 1)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have allowancePaid : (parents.length : InverseRootPolynomial.Coordinate) * allowance < energyTarget := by
    have countLt : (parents.length : InverseRootPolynomial.Coordinate) < (parents.length :
      InverseRootPolynomial.Coordinate) + 1 := by
      exact (show (parents.length : InverseRootPolynomial.Coordinate) = (parents.length :
        InverseRootPolynomial.Coordinate) + 0 by ring1).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 1) _)
    have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct countLt allowancePositive
    exact bound.trans_eq (by
        rw [Fraction.Field.mul_comm];
        exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  let preparations := SideEnergyRequests.prepareEnergy bounds allowance allowancePositive energyFloor
    evaluated.original.separated.parents evaluated.replacements
  exact ⟨allowance, rfl, allowancePositive, allowancePaid, bounds, preparations,
    preparations.maximum evaluated.original.separated.parents evaluated.replacements, rfl⟩

end Evaluation

namespace EnergyPreparation

variable {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan.Evaluation
  plan depth readingIndex} {energyTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor
  energyDepth : Nat}

/-- Evaluate once at the common depth chosen after all component preparations. -/
@[expose] def evaluate (preparation : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation
  evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : ∀ parent ∈ parents, 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) (later : preparation.minimum ≤ energyDepth) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated energyTarget energyFloor :=
  let energies := EnergyPreparations.evaluate branch parameters
    evaluated.original.separated.parents evaluated.replacements preparation.preparations oriented
    (preparation.minimum_eq ▸ later)
  let connected := EnergyConnection.build evaluated.original.separated.parents evaluated.replacements energies
    evaluated.original.firstValue
  ⟨preparation, energyDepth, later, parameters, energies, connected⟩

end EnergyPreparation

/-- Standalone acquisition uses the same shared-preparation implementation. -/
@[expose] def Evaluation.energy (evaluated : Plan.Evaluation plan depth readingIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : ∀ parent ∈ parents, 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated energyTarget energyFloor :=
  let bounds := Cap.EnergyBounds.build sample RootRadialGeometry.domain
  let preparation := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.Evaluation.prepareEnergy evaluated
    bounds energyTarget positive energyFloor
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation.evaluate preparation branch oriented
    (Parameters.build preparation.minimum) le_rfl

namespace RequestedEnergy

variable {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan.Evaluation
  plan depth readingIndex} {energyTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor
  : Nat}

/-- The retained complete energy has signed lower bound strictly above the negative original target. -/
theorem lower (energy : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated
  energyTarget energyFloor) : -energyTarget < energy.connected.energy.im / 4 :=
  (Fraction.Order.Arithmetic.neg_lt_neg_direct energy.allowance_paid).trans_le energy.connected.lower

/-- Parent and cell counts are both paid independently of the final mesh. The remaining boundary is the explicit sum of
shifted potentials and actual inter-parent connector areas. -/
theorem boundary_close (energy : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated
  energyTarget energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy - (-evaluated.connected.summary.area -
      BoundaryRibbon.area evaluated.original.firstValue evaluated.connected.summary.total + energy.connected.boundary))
        <
        256 * (4 * target + ((totalTarget / 4) / 4) / 4) := by
  have chartPaid : (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * charts.parentTarget < target := by
    rw [charts.parentTarget_eq]
    simpa only [pow_two, Fraction.Field.mul_assoc] using Aggregate.count_mul_perTerm_lt charts.positive parents.length
  have chartScaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4) chartPaid
  have joinPaid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct request.separated.total_paid
    (Fraction.Order.Field.inv_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 4))
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 256)
    (Fraction.Order.Arithmetic.add_lt_add_direct chartScaled joinPaid)
  have scaled : (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * (256 * (4 * charts.parentTarget +
    request.separated.parentTarget / 4)) <
      256 * (4 * target + ((totalTarget / 4) / 4) / 4) := by
    refine (show _ = 256 * (4 * ((parents.length : InverseRootPolynomial.Coordinate) ^ 2 * charts.parentTarget) +
      ((parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate) *
        request.separated.parentTarget)) * (4 : InverseRootPolynomial.Coordinate)⁻¹) by
        simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; ring1).trans_lt ?_
    exact paid.trans_eq (by simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; rfl)
  exact (EnergyConnection.boundary_error energy.connected evaluated.connected).trans_lt scaled

/-- The reference area is the original source comparison of this same complete exterior acquisition; no period program
or owner is replaced. -/
theorem source_boundary_close (energy : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy
  evaluated energyTarget energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy - (-evaluated.original.separated.left.area -
      BoundaryRibbon.area evaluated.original.firstValue evaluated.connected.summary.total + energy.connected.boundary))
        <
        2 * (256 * (4 * target + ((totalTarget / 4) / 4) / 4) + 2 * (areaTarget + target)) := by
  let rest := -BoundaryRibbon.area evaluated.original.firstValue evaluated.connected.summary.total +
    energy.connected.boundary
  have first : Data.Gaussian.Norm.Basic.normSq (energy.connected.energy - (-evaluated.connected.summary.area +
    rest)) <
      256 * (4 * target + ((totalTarget / 4) / 4) / 4) :=
    (congrArg Data.Gaussian.Norm.Basic.normSq (by dsimp only [rest]; ring1)).trans_lt
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy.boundary_close energy)
  have second : Data.Gaussian.Norm.Basic.normSq ((-evaluated.connected.summary.area + rest) -
    (-evaluated.original.separated.left.area + rest)) <
      2 * (areaTarget + target) := (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_lt
        evaluated.area_close
  have close := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via energy.connected.energy (-evaluated.connected.summary.area
    + rest) (-evaluated.original.separated.left.area + rest)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first second))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by dsimp only [rest]; ring1)).trans_lt close

end RequestedEnergy
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
