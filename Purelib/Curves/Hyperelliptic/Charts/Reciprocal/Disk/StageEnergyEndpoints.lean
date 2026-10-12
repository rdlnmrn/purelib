module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ChartPlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

public section

/-!
# The energy endpoints are the original synchronized boundary readings

The original sample identity transports the endpoint certificates to the
common cap sample. Both endpoint potentials use the supplied common depth,
and the original parent replacement request pays their chart offsets.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices (EnergyEndpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock (terminalPotential)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests (StageRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement (ChartReplacement)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy (RequestedEnergy)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
    {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget
    reciprocalTarget coefficientTarget totalTarget areaTarget minimum}
  {replacement : ChartReplacementRequest
    prepared target minimum}
  {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample
    depth readingIndex}

/-- Transport the original energy endpoint certificate along equality of the retained cap sample and model index. -/
private theorem transportEndpoint {firstIndex lastIndex energyDepth : Nat}
    {first : Primitives.Sample cap differential firstIndex box}
    {last : Primitives.Sample cap differential lastIndex box}
    {root value potential : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (indices : firstIndex = lastIndex) (samples : HEq first last)
    (endpoint : ReciprocalDiskVertices.EnergyEndpoint first regular energyDepth target root value potential) :
    ReciprocalDiskVertices.EnergyEndpoint last regular energyDepth target root value potential := by
  cases indices
  cases samples
  exact endpoint

/-- The original per-cell chart replacement allowance is at most the requested whole-parent target. -/
private theorem local_le_target (replacement : ChartReplacementRequest prepared target minimum)
  : replacement.localTarget ≤ target := by
  have oneNat : 1 ≤ cover.mesh.edges.length := by
    cases equal : cover.mesh.edges with
    | nil => exact False.elim (Owners.mesh_nonempty cover.mesh equal)
    | cons head tail => simp only [List.length_cons]; omega
  have one : (1 : InverseRootPolynomial.Coordinate) ≤ (cover.mesh.edges.length : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct oneNat
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ (cover.mesh.edges.length :
    InverseRootPolynomial.Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have square : (1 : InverseRootPolynomial.Coordinate) ≤ (cover.mesh.edges.length : InverseRootPolynomial.Coordinate) ^
    2 := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_direct one one (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) countNonnegative
    exact (by ring1 : (1 : InverseRootPolynomial.Coordinate) = 1 * 1).trans_le (bound.trans_eq (by ring1))
  have quarter := Fraction.Order.Field.div_nonneg_direct replacement.localPositive.le (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  have factor : replacement.localTarget ≤ 2 * (replacement.localTarget + replacement.localTarget / 4) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg replacement.localPositive.le (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) quarter)).trans_eq (by ring1)
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square replacement.localPositive.le
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factor
    (Fraction.Order.Arithmetic.sq_nonneg_direct (cover.mesh.edges.length : InverseRootPolynomial.Coordinate))
  exact (show replacement.localTarget = 1 * replacement.localTarget by ring1).trans_le (counted.trans (scaled.trans
    replacement.paid.le))

namespace ChartReplacement

variable {energyTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}
  (chart : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartReplacement replacement
    evaluated)
  (energy : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy.RequestedEnergy chart.charts
    evaluated.cap.polynomial.cells chart.vertices request.cap.endpoints energyTarget energyFloor)
  (branch : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (sameDepth :
    energy.depth = energyDepth)

include branch sameDepth in
/-- The actual energy chain begins at the original synchronized first reading with its retained potential and paid chart
offset. -/
theorem energy_first_endpoint :
    ReciprocalDiskVertices.EnergyEndpoint sample regular energyDepth target evaluated.firstReading.coordinate
      evaluated.cap.firstValue energy.firstPotential := by
  cases sameDepth
  have endpoint := RequestedEnergy.first_endpoint energy branch (Owners.mesh_nonempty cover.mesh)
  dsimp only at endpoint
  rw [← chart.readings_eq, ← evaluated.cap.boundary.first_coordinate,
    ChartReplacement.energy_first chart energy,
    ← evaluated.first_coordinate] at endpoint
  have shared := Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints.transportEndpoint
    evaluated.original_index evaluated.capSample_eq endpoint
  exact ⟨shared.potential_eq, shared.offset.trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints.local_le_target replacement), shared.small,
    shared.inside⟩

include branch sameDepth in
/-- The actual energy chain ends at the original synchronized last reading with its retained terminal potential and paid
chart offset. -/
theorem energy_last_endpoint :
    ReciprocalDiskVertices.EnergyEndpoint sample regular energyDepth target evaluated.lastReading.coordinate
      evaluated.cap.joined.lastValue
      (RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential) := by
  cases sameDepth
  have endpoint := RequestedEnergy.last_endpoint energy branch (Owners.mesh_nonempty cover.mesh)
    evaluated.cap.firstValue 0
  dsimp only at endpoint
  rw [← chart.readings_eq, ← evaluated.cap.boundary.last_coordinate 0, ← evaluated.cap.joined.lastValue_eq, ←
    evaluated.last_coordinate] at endpoint
  have shared := Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints.transportEndpoint
    evaluated.original_index evaluated.capSample_eq endpoint
  exact ⟨shared.potential_eq, shared.offset.trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints.local_le_target replacement), shared.small,
    shared.inside⟩

end ChartReplacement
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints
