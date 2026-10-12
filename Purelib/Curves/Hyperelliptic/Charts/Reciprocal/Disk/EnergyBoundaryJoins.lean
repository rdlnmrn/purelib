module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-!
# Shifted energy potentials across the actual exterior parent joins

The original join requests consume the same retained endpoint readings.
Their radial estimates and the cached chart offsets control every signed
potential jump at the common fan depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget joining :
    Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth joinFloor : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace EnergyData

/-- The actual retained potential-jump list has exactly the original parent count. -/
theorem joinErrors_length {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) (charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated)
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) :
    (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.joinErrors evaluated charts
      energies previous previousPotential).length = parents.length := by
  induction evaluated generalizing previous previousPotential with
  | nil => cases charts; rfl
  | cons first rest ih =>
      cases charts with
      | cons _ head tail => exact congrArg Nat.succ (ih tail energies.2 _ _)

/-- The sum of actual joined boundary terms is the terminal-minus-initial potential minus every retained join error. -/
theorem boundary_identity {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) (charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated)
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyData.boundaryTerms
      evaluated charts energies previous) =
      Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.lastPotential evaluated charts
      energies previousPotential - previousPotential -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.joinErrors evaluated charts
        energies previous previousPotential) := open Purelib.Integration in by
  induction evaluated generalizing previous previousPotential with
  | nil =>
    cases charts; change (0 : Normalization.InverseRootPolynomial.Gaussian) = previousPotential - previousPotential - 0;
      ring1
  | cons first rest ih =>
      cases charts with
      | cons _ head tail =>
          change (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential
            energies.1.val.blocks energies.1.val.firstPotential - energies.1.val.firstPotential +
            Path.BoundaryRibbon.area previous first.cap.firstValue) +
              Data.Gaussian.Norm.Sum.Basic.gaussianSum
                (Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy.EnergyData.boundaryTerms rest tail energies.2
                first.cap.joined.lastValue) =
            Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.lastPotential rest tail
              energies.2
              (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential
              energies.1.val.blocks energies.1.val.firstPotential) - previousPotential -
              ((energies.1.val.firstPotential - previousPotential - Path.BoundaryRibbon.area previous
                first.cap.firstValue) + Data.Gaussian.Norm.Sum.Basic.gaussianSum _)
          rw [ih tail energies.2 first.cap.joined.lastValue
            (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential
            energies.1.val.blocks energies.1.val.firstPotential)]
          ring1

/-- Existing connected-path clients use the same retained endpoint-bank checker. -/
theorem joins_bounded (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
  (joinSmall : joining ≤ 1)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) (charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated)
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts) {links : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links prepared}
    (junctions : Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests joining joinFloor prepared links)
      (later : junctions.maximum ≤ readingIndex)
    (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian)
    (small : Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.FirstJoinBound
      evaluated charts energies previous previousPotential (80 * target + 2 * joining)) :
    ∀ error ∈ Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.joinErrors evaluated
      charts energies previous previousPotential, Data.Gaussian.Norm.Basic.normSq error ≤ 80 * target + 2 * joining
      := by
  have first := (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_firstBound
    evaluated charts energies branch previous previousPotential _).mpr small
  have bound := (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank branch
    evaluated charts energies).errors_bounded branch joinSmall junctions later previous previousPotential first
  rw [Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_errors evaluated
    charts energies branch previous previousPotential] at bound
  exact bound

end EnergyData
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins
