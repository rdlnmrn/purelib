module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyClosing
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-!
# All residual energy boundary terms are original join errors

The shifted potentials telescope around the retained root-closed parent
bank. The trace-origin correction supplies the last-to-first area term;
its sign is retained in the exact identity before taking any norm bounds.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryControl

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget joining closingTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth joinFloor closingFloor : Nat} {box :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
    Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget coefficientTarget
    totalTarget areaTarget minimum prepared}
  {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
    requests} {charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated}
  {energies : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
    evaluated charts} {previous : Normalization.InverseRootPolynomial.Gaussian}

/-- The actual shifted energy boundary is bounded by the original internal join errors and closing error on the retained
root-closed parent bank. -/
theorem boundary_small (energy : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyConnection evaluated charts
  energies previous) (connected : Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections.Connected evaluated charts
  previous)
    (firstEq : previous = Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstValue evaluated) (branch
      : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    (closingNonnegative : 0 ≤ closingTarget) (closingSmall : closingTarget ≤ 1)
    {links : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links prepared} (junctions :
      Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests joining joinFloor prepared links) (joinLater
      : junctions.maximum ≤ readingIndex)
    {joined : Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.ClosingJoin prepared} (closing :
      Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest closingTarget closingFloor prepared joined)
      (closingLater : closing.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (energy.boundary - Path.BoundaryRibbon.area previous connected.summary.total) ≤
      2 * ((parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (80 * target + 2 * joining) + (80 *
        target + 2 * closingTarget)) := open Purelib.Data.Rat in by
  subst previous
  let firstValue := Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstValue evaluated
  let firstPotential :=
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.firstPotential evaluated charts
    energies
  let lastPotential := Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.lastPotential
    evaluated charts energies firstPotential
  let lastValue := Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue evaluated firstValue
  let errors := Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.joinErrors evaluated
    charts energies firstValue firstPotential
  let closingError := firstPotential - lastPotential - Path.BoundaryRibbon.area lastValue firstValue
  have initial : Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.FirstJoinBound
    evaluated charts energies firstValue firstPotential (80 * target + 2 * joining) := by
    cases evaluated with
    | nil => cases charts; trivial
    | cons first rest =>
        cases charts with
        | cons replacement head tail =>
            change Data.Gaussian.Norm.Basic.normSq (energies.1.val.firstPotential - energies.1.val.firstPotential -
              Path.BoundaryRibbon.area first.cap.firstValue first.cap.firstValue) ≤ _
            rw [Gaussian.Basic.sub_self, Path.IncrementArea.area_self, Gaussian.Basic.sub_zero,
              Gaussian.Norm.Basic.normSq_zero]
            exact add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) targetNonnegative)
              (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) joinNonnegative)
  have bounded := Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins.EnergyData.joins_bounded branch joinSmall
    evaluated charts energies junctions joinLater firstValue firstPotential initial
  have sumBound : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum errors) ≤
    (parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (80 * target + 2 * joining) := by
    have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le errors _ bounded
    rw [Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins.EnergyData.joinErrors_length evaluated charts energies
      firstValue firstPotential] at bound
    exact bound.trans_eq (by ring1)
  have closingBound : Data.Gaussian.Norm.Basic.normSq closingError ≤ 80 * target + 2 * closingTarget :=
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyClosing.closing_bound branch targetNonnegative closingNonnegative
      closingSmall evaluated charts energies closing closingLater
  have identity : energy.boundary - Path.BoundaryRibbon.area firstValue connected.summary.total =
    -(Data.Gaussian.Norm.Sum.Basic.gaussianSum errors + closingError) := by
    rw [energy.boundary_eq, Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins.EnergyData.boundary_identity
      evaluated charts energies firstValue firstPotential,
      Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections.Connected.total connected,
      Path.BoundaryRibbon.area_sub_self_right]
    have swap : Path.BoundaryRibbon.area lastValue firstValue = -Path.BoundaryRibbon.area firstValue lastValue := by
      unfold Path.BoundaryRibbon.area; ring1
    dsimp only [closingError]
    rw [swap]
    dsimp only [errors, firstPotential, lastPotential, lastValue]
    ring1
  rw [identity, Gaussian.Norm.Basic.normSq_neg]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add sumBound closingBound) (by decide))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryControl
