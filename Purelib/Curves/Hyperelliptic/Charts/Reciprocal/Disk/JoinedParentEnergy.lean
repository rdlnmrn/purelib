module
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedChartRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

public section

/-!
# The existing joined-parent acquisition consumes the full odd cap energy

No new source, root reader, or join request is prepared. The already retained
chart and endpoint budgets pay the complete energy comparison, independently
of the final chart and radial subdivision counts.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParentEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedChartRequest.Plan (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartPlans)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Preparation regular cover}
    {totalTarget areaTarget : InverseRootPolynomial.Coordinate} {floor minimum depth
    readingIndex : Nat}
  {request : JoinedChartRequest prepared
    totalTarget areaTarget floor}
  {originalTarget : Coordinate} {original :
    ReciprocalBoundaryArea.Cover.AreaRequest cover depth originalTarget}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential original.index box}
  {plan : JoinedChartRequest.Plan request
    capSample minimum}

/-- Construct the odd-origin cap-energy certificate from the existing joined-parent chart and endpoint evaluations.

The original prepared requests, cached source cells, reading stage and actual junctions are reused at the retained
energy depth. -/
@[expose] def energy (evaluated : Plan.Evaluation original plan readingIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor :=
  RequestedEnergy.build plan.charts evaluated.compared.polynomial.cells evaluated.vertices request.joined.endpoints
    evaluated.model_later evaluated.reading_later branch oriented request.replacement.localPositive.le
      request.joined.junctions
    (Fraction.Order.Field.div_nonneg_direct request.joined.budget.positive.le (by decide))
      (JoinedRequest.energy_join_small request.joined)
    evaluated.junction_later energyTarget positive energyFloor

/-- The joined-parent request specializes the shared replacement allowance.

The original chart target is a quarter of the area target. Cancelling that
fixed denominator expresses the retained replacement payment at the full
joined-parent target. -/
theorem energy_allowance :
    ((2 * cover.mesh.edges.length : Nat) : InverseRootPolynomial.Coordinate) ^ 2 *
      (request.replacement.localTarget + request.joined.budget.tolerance / 4) < areaTarget + totalTarget / 4 := by
  have paid := ChartReplacementRequest.energy_allowance request.replacement request.joined
  have cancel : 4 * (areaTarget / 4) = areaTarget := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [cancel] at paid
  exact paid

variable {energyTarget : Coordinate} {energyFloor : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParentEnergy
/-- The retained energy chain begins at the actual first reading already cached by the original joined-parent
comparison. -/
theorem energy_first (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) : energy.firstValue = evaluated.compared.firstValue := by
  rw [energy.first_value, evaluated.compared.firstValue_eq, evaluated.readings_eq]

/-- The complete restored energy-block paths equal the exact original joined-parent replacement paths. -/
theorem energy_paths (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) :
    RestoredEnergyBlock.paths energy.blocks energy.firstValue = evaluated.replacement.paths := by
  rw [energy.paths_eq, evaluated.replacement.paths_eq, evaluated.readings_eq,
    energy_first evaluated energy]

/-- The retained energy connection and original replacement summary have exactly the same full area. -/
theorem energy_area (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) : energy.connection.summary.area =
        evaluated.replacement.summary.area := by
  rw [energy.connection.summary.area_eq, energy_paths
    evaluated energy, ← evaluated.replacement.summary.area_eq]

/-- The actual energy trace is the original replacement area plus its cached first-value and total endpoint term. -/
theorem energy_trace (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) :
    energy.connection.trace = evaluated.replacement.summary.area +
      BoundaryRibbon.area evaluated.compared.firstValue evaluated.replacement.summary.total := by
  rw [energy.connection.trace_eq, energy_paths evaluated
    energy, energy_first evaluated energy,
    IncrementArea.traceArea_eq, ← evaluated.replacement.summary.area_eq, ← evaluated.replacement.summary.total_eq]

/-- The reference is the existing restored path, with every source and endpoint correction retained. Only shifted
exterior potentials remain.

The paid replacement allowance bounds the original energy discrepancy.
The retained path and trace identities preserve the same endpoint term and
terminal potential on both sides of the comparison. -/
theorem energy_boundary_close (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (energy.connection.energy - (-evaluated.replacement.summary.area -
      BoundaryRibbon.area evaluated.compared.firstValue evaluated.replacement.summary.total +
      RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential)) <
        256 * (areaTarget + totalTarget / 4) := by
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 256)
    (energy_allowance (request := request))
  have paid : (cover.mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * (1024 *
      (request.replacement.localTarget + request.joined.budget.tolerance / 4)) < 256 * (areaTarget + totalTarget / 4) :=
    (show _ = 256 * (((2 * cover.mesh.edges.length : Nat) : InverseRootPolynomial.Coordinate) ^ 2 *
      (request.replacement.localTarget + request.joined.budget.tolerance / 4)) by
          simp only [Algebra.NatCast.mul, Nat.cast_ofNat, -eq_self, -iff_self];
          ring1).trans_lt scaled
  have close := energy.boundary_error.trans_lt paid
  rw [energy_trace evaluated energy] at close
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt close
  ring1

/-- The signed energy now compares with the original source area of the same retained parent. The explicit exterior
terms are preserved for sewing.

The retained replacement-area error is combined with the original energy
bound. Both comparisons use the same parent, endpoint value and potential
terms, so the resulting bound concerns their actual common source. -/
theorem energy_source_boundary_close (evaluated : Plan.Evaluation original plan readingIndex)
    (energy : RestoredParentEnergy.RequestedEnergy plan.charts evaluated.compared.polynomial.cells evaluated.vertices
      request.joined.endpoints energyTarget energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (energy.connection.energy - (-evaluated.compared.polynomial.left.area -
      BoundaryRibbon.area evaluated.compared.firstValue evaluated.replacement.summary.total +
      RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential)) <
        2 * (256 * (areaTarget + totalTarget / 4) + areaTarget) := by
  let rest := -BoundaryRibbon.area evaluated.compared.firstValue evaluated.replacement.summary.total +
    RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential
  have first : Data.Gaussian.Norm.Basic.normSq (energy.connection.energy - (-evaluated.replacement.summary.area
    + rest)) < 256 * (areaTarget + totalTarget / 4) := by
    refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt
      (energy_boundary_close evaluated energy)
    dsimp only [rest]; ring1
  have second : Data.Gaussian.Norm.Basic.normSq ((-evaluated.replacement.summary.area + rest) -
    (-evaluated.compared.polynomial.left.area + rest)) < areaTarget :=
    (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1 : (-evaluated.replacement.summary.area + rest) -
      (-evaluated.compared.polynomial.left.area + rest) =
      evaluated.compared.polynomial.left.area - evaluated.replacement.summary.area)).trans_lt evaluated.area_close
  have close := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via energy.connection.energy
    (-evaluated.replacement.summary.area + rest) (-evaluated.compared.polynomial.left.area + rest)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first second))
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt close
  dsimp only [rest]; ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParentEnergy
