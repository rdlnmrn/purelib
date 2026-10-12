module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-!
# Signed energy on the actual connected exterior parent bank

The same-depth fan energies are summed over the complete retained bank.
Every original inter-parent connector is included in the trace identity.
Shifted endpoint potentials and connector areas remain explicit; this
statement does not yet assert their cancellation around the closed boundary.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.IncrementArea (traceArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock (terminalPotential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests (ChartReplacements)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests (EnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections (connectedPaths Connected)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget :
    Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the actual same-depth parent fan energies in their original retained order. -/
@[expose] def EnergyData.values :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → List
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => []
  | _, _, _, _, .cons _ rest, .cons _ _ tail, energies => energies.1.val.connection.energy :: values rest tail
    energies.2

/-- Read each actual shifted endpoint-potential difference with its original inter-parent connector wedge. -/
@[expose] def EnergyData.boundaryTerms :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → InverseRootPolynomial.Gaussian
      → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _ => []
  | _, _, _, _, .cons first rest, .cons _ _ tail, energies, previous =>
      (RestoredEnergyBlock.terminalPotential energies.1.val.blocks energies.1.val.firstPotential -
        energies.1.val.firstPotential + BoundaryRibbon.area previous first.cap.firstValue) ::
        boundaryTerms rest tail energies.2 first.cap.joined.lastValue

set_option genInjectivity false in
/-- The complete retained exterior energy sum and its exact connected trace and boundary correction.

The actual parent-count error list and signed lower energy bound use the same cached fans and every original connector.
-/
structure EnergyConnection {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) (charts : SideChartRequests.ChartReplacements
      target evaluated)
    (energies : SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts) (previous :
      InverseRootPolynomial.Gaussian) where
  /-- The cached sum of all actual retained parent fan energies. -/ energy : InverseRootPolynomial.Gaussian
  /-- The energy cache is exactly the Gaussian sum of the original parent energy readings. -/ energy_eq : energy =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyData.values evaluated charts energies)
  /-- The signed imaginary energy is bounded below by the negative original parent-count energy allowance. -/ lower :
    -((parents.length : InverseRootPolynomial.Coordinate) * energyTarget) ≤ energy.im / 4
  /-- The cached complete connected replacement-path trace from the supplied previous value. -/ trace :
    InverseRootPolynomial.Gaussian
  /-- The trace cache equals the actual original connected path's full trace area. -/ trace_eq : trace =
    IncrementArea.traceArea previous (SideChartConnections.connectedPaths evaluated charts previous).flatten
  /-- The cached sum of original potential differences and inter-parent connector wedges. -/ boundary :
    InverseRootPolynomial.Gaussian
  /-- The boundary cache equals the complete original ordered boundary-term sum. -/ boundary_eq : boundary =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyData.boundaryTerms evaluated charts energies previous)
  /-- The retained list of actual parent energy-versus-trace residuals. -/ errors : List InverseRootPolynomial.Gaussian
  /-- There is exactly one retained energy residual per actual original parent. -/ count_eq : errors.length =
    parents.length
  /-- The actual total energy discrepancy equals the sum of the retained parent residuals. -/ discrepancy : energy -
    (-trace + boundary) = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- Every actual parent residual satisfies the original chart and total-error allowance. -/ bounded : ∀ error ∈
    errors, Data.Gaussian.Norm.Basic.normSq error ≤ 256 * (4 * target + totalTarget / 4)

constructive_injectivity EnergyConnection

namespace EnergyConnection

/-- Combine the actual retained same-depth fan energies, preserving every original connector and exact trace and
boundary readback. -/
@[expose] def build :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    (energies : SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts) → (previous :
      InverseRootPolynomial.Gaussian) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyConnection evaluated charts energies previous
  | _, _, _, _, .nil, .nil, _, _ => by
      refine ⟨0, rfl, ?_, 0, rfl, 0, rfl, [], rfl, ?_, ?_⟩
      · change -((0 : InverseRootPolynomial.Coordinate) * energyTarget) ≤ 0 / 4
        rw [show -((0 : InverseRootPolynomial.Coordinate) * energyTarget) = 0 by ring1]; decide
      · change (0 : InverseRootPolynomial.Gaussian) - (-0 + 0) = 0; ring1
      · intro _ member; exact False.elim (List.not_mem_nil member)
  | _, _, _, _, .cons (parents := restParents) first rest, .cons _ head tail, energies, previous => by
      let energy := energies.1.val
      let remaining := build rest tail
        energies.2 first.cap.joined.lastValue
      let potential := RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential
      let boundary := potential + BoundaryRibbon.area previous first.cap.firstValue
      let error := energy.connection.energy - (-energy.connection.trace + potential)
      refine ⟨energy.connection.energy + remaining.energy, ?_, ?_,
        BoundaryRibbon.area previous first.cap.firstValue + energy.connection.trace + remaining.trace, ?_,
        boundary + remaining.boundary, ?_, error :: remaining.errors, congrArg Nat.succ remaining.count_eq, ?_, ?_⟩
      · change energy.connection.energy + remaining.energy = energy.connection.energy +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum _
        rw [remaining.energy_eq]
      · have lower := Fraction.Order.Arithmetic.add_le_add_direct energy.lower.le remaining.lower
        simp only [List.length_cons, Nat.cast_succ, Purelib.Data.Gaussian.Basic.add_im]
        exact (by ring1 : -(((restParents.length : InverseRootPolynomial.Coordinate) + 1) * energyTarget) =
          -energyTarget + -((restParents.length : InverseRootPolynomial.Coordinate) * energyTarget)).trans_le
          (lower.trans_eq (by simp only [Purelib.Data.Rat.Fraction.Field.div_eq_mul_inv_direct]; ring1))
      · change _ = IncrementArea.traceArea previous (((first.cap.firstValue - previous) ::
          head.replacement.paths.flatten) ++
          (SideChartConnections.connectedPaths rest tail first.cap.joined.lastValue).flatten)
        rw [IncrementArea.traceArea_append]
        have headTotal : Data.Gaussian.Norm.Sum.Basic.gaussianSum ((first.cap.firstValue - previous) ::
          head.replacement.paths.flatten) = first.cap.joined.lastValue - previous := by
          change first.cap.firstValue - previous + Data.Gaussian.Norm.Sum.Basic.gaussianSum
            head.replacement.paths.flatten = _
          rw [← head.replacement.summary.total_eq,
            Replacement.total_preserved head.replacement first.cap.joined,
            first.cap.joined.total_eq]
          ring1
        rw [headTotal, show previous + (first.cap.joined.lastValue - previous) = first.cap.joined.lastValue by ring1,
          IncrementArea.traceArea, show previous + (first.cap.firstValue - previous) = first.cap.firstValue by ring1,
          IncrementArea.traceArea_eq, ← head.replacement.summary.area_eq, ← head.replacement.summary.total_eq,
          ← ChartReplacement.energy_trace head energy, ← remaining.trace_eq]
      · change boundary + remaining.boundary = boundary + Data.Gaussian.Norm.Sum.Basic.gaussianSum _
        rw [remaining.boundary_eq]
      · change energy.connection.energy + remaining.energy -
          (-(BoundaryRibbon.area previous first.cap.firstValue + energy.connection.trace + remaining.trace) + (boundary
            + remaining.boundary)) =
          error + Data.Gaussian.Norm.Sum.Basic.gaussianSum remaining.errors
        rw [← remaining.discrepancy]
        dsimp only [error, boundary]
        ring1
      · intro term member
        rcases Data.List.Membership.mem_cons.mp member with same | member
        · subst term
          have close := ChartReplacement.energy_boundary_close head energy
          have errorEq : error = energy.connection.energy - (-head.replacement.summary.area -
              BoundaryRibbon.area first.cap.firstValue head.replacement.summary.total +
              RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential) := by
            dsimp only [error, potential]
            rw [ChartReplacement.energy_trace head energy]
            ring1
          exact (congrArg Data.Gaussian.Norm.Basic.normSq errorEq).trans_le close.le
        · exact remaining.bounded term member

variable {parents : List (CenteredEdge curve differential)}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}
  {evaluated : Evaluations sample depth
    readingIndex requests} {charts :
    ChartReplacements target evaluated}
  {energies : EnergyData energyTarget energyFloor
    energyDepth evaluated charts} {previous : Gaussian}

/-- The actual complete energy and connected boundary-area discrepancy satisfies the original parent-count squared error
bound. -/
theorem boundary_error (energy : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyConnection evaluated
  charts energies previous) (connected : SideChartConnections.Connected evaluated charts previous) :
    Data.Gaussian.Norm.Basic.normSq (energy.energy - (-connected.summary.area - BoundaryRibbon.area previous
      connected.summary.total + energy.boundary)) ≤
      (parents.length : InverseRootPolynomial.Coordinate) ^ 2 * (256 * (4 * target + totalTarget / 4)) := by
  have trace : energy.trace = connected.summary.area + BoundaryRibbon.area previous connected.summary.total := by
    rw [energy.trace_eq, ← connected.paths_eq, IncrementArea.traceArea_eq,
      ← connected.summary.area_eq, ← connected.summary.total_eq]
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le energy.errors _ energy.bounded
  rw [energy.count_eq, ← energy.discrepancy, trace] at bound
  refine (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_le (bound.trans_eq (by ring1))

end EnergyConnection
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
