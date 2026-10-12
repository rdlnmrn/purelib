module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergyEndpoints

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-!
# Read the common-depth endpoint packets from existing parent energy

All endpoint coordinates and potentials are copied from retained data.
The readback identities relate the budget-independent packet bank to the
original energy boundary terms and joins.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock (terminalPotential)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests (StageRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement (ChartReplacement)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy (RequestedEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank (EnergyEnds)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Cover data}
  {prepared : Preparation regular cover}
    {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget :
    Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request : StageRequest prepared sourceTarget
    reciprocalTarget coefficientTarget totalTarget areaTarget minimum}
  {replacement : ChartReplacementRequest
    prepared target minimum} {evaluated :
    Evaluation request sample depth
    readingIndex}

/-- Read the original endpoint coordinates, root readings and radial potentials from the retained parent energy at the
same depth. -/
@[expose] def energyEnds (chart : StageChartReplacement.ChartReplacement replacement evaluated)
    (energy : RestoredParentEnergy.RequestedEnergy chart.charts evaluated.cap.polynomial.cells chart.vertices
      request.cap.endpoints energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (sameDepth : energy.depth = energyDepth) :
    EnergyEndBank.EnergyEnds sample readingIndex energyDepth target prepared :=
  ⟨evaluated.first, evaluated.firstReading, evaluated.last, evaluated.lastReading,
    evaluated.cap.firstValue, evaluated.first_value, evaluated.cap.joined.lastValue, evaluated.last_value,
    energy.firstPotential, RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential,
    ChartReplacement.energy_first_endpoint chart energy branch sameDepth, ChartReplacement.energy_last_endpoint chart
      energy branch sameDepth⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacement

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock (terminalPotential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests (ChartReplacements)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests (EnergyData)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget joining :
    Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth joinFloor : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the first actual retained parent potential, with zero for an empty bank. -/
@[expose] def firstPotential :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _ => 0
  | _, _, _, _, .cons _ _, .cons _ _ _, energies => energies.1.val.firstPotential

/-- Read the last actual terminal potential, retaining the supplied previous potential for an empty bank. -/
@[expose] def lastPotential :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → InverseRootPolynomial.Gaussian
      → InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, previous => previous
  | _, _, _, _, .cons _ rest, .cons _ _ tail, energies, _ =>
      lastPotential
        rest tail energies.2 (RestoredEnergyBlock.terminalPotential energies.1.val.blocks energies.1.val.firstPotential)

/-- Read every original inter-parent potential discrepancy with its actual connector wedge. -/
@[expose] def joinErrors :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → InverseRootPolynomial.Gaussian
      → InverseRootPolynomial.Gaussian → List InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _, _ => []
  | _, _, _, _, .cons first rest, .cons _ _ tail, energies, previous, previousPotential =>
      (energies.1.val.firstPotential - previousPotential - BoundaryRibbon.area previous first.cap.firstValue) ::
        joinErrors
          rest tail energies.2 first.cap.joined.lastValue (RestoredEnergyBlock.terminalPotential energies.1.val.blocks
          energies.1.val.firstPotential)

/-- The original first connector discrepancy satisfies the supplied bound, vacuously for an empty bank. -/
@[expose] def FirstJoinBound :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → InverseRootPolynomial.Gaussian
      → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Coordinate → Prop
  | _, _, _, _, .nil, .nil, _, _, _, _ => True
  | _, _, _, _, .cons first _, .cons _ _ _, energies, previous, previousPotential, bound =>
      Data.Gaussian.Norm.Basic.normSq (energies.1.val.firstPotential - previousPotential - BoundaryRibbon.area
        previous first.cap.firstValue) ≤ bound

/-- Read the actual energy-end packet bank from the original retained same-depth parent evaluations. -/
@[expose] def endBank (branch : HyperellipticReciprocal.originOrder curve = 1) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → {requests : SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (evaluated : SideBank.Evaluations sample depth readingIndex requests) → (charts :
      SideChartRequests.ChartReplacements target evaluated) →
    SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth evaluated charts → EnergyEndBank sample
      readingIndex energyDepth target prepared
  | _, _, _, _, .nil, .nil, _ => .nil
  | _, _, _, _, .cons _ rest, .cons _ head tail, energies =>
      .cons (Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacement.energyEnds
        head energies.1.val branch energies.1.property)
          (endBank
          branch rest tail energies.2)

variable {parents : List (CenteredEdge curve differential)}
  {covers : ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}
  (evaluated : Evaluations sample depth
    readingIndex requests) (charts :
    ChartReplacements target evaluated)
  (energies : EnergyData energyTarget energyFloor
    energyDepth evaluated charts) (branch :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)

/-- The packet bank's first value is exactly the original evaluated parent bank's first value. -/
theorem endBank_firstValue :
  (endBank branch evaluated
  charts energies).firstValue = Evaluations.firstValue evaluated := by
  cases evaluated with
  | nil => cases charts; rfl
  | cons first rest => cases charts; rfl

/-- The packet bank's first potential is exactly the original retained energy potential. -/
theorem endBank_firstPotential :
  (endBank branch evaluated
  charts energies).firstPotential =
  firstPotential evaluated
  charts energies := by
  cases evaluated with
  | nil => cases charts; rfl
  | cons first rest => cases charts; rfl

/-- The packet bank's last value is exactly the original evaluated parent bank's terminal value. -/
theorem endBank_lastValue (previous : InverseRootPolynomial.Gaussian) :
  (endBank branch evaluated
  charts energies).lastValue previous = Evaluations.lastValue evaluated previous := by
  induction evaluated generalizing previous with
  | nil => cases charts; rfl
  | cons first rest ih =>
      cases charts with
      | cons replacement head tail => exact ih tail energies.2 first.cap.joined.lastValue

/-- The packet bank's last potential is exactly the original retained energy terminal potential. -/
theorem endBank_lastPotential (previous : InverseRootPolynomial.Gaussian) :
    (endBank branch evaluated
      charts energies).lastPotential previous =
      lastPotential evaluated
      charts energies previous := by
  induction evaluated generalizing previous with
  | nil => cases charts; rfl
  | cons first rest ih =>
      cases charts with
      | cons replacement head tail =>
        exact ih tail energies.2 (RestoredEnergyBlock.terminalPotential energies.1.val.blocks
          energies.1.val.firstPotential)

/-- The packet bank retains exactly the original ordered join-error list. -/
theorem endBank_errors (previous potential : InverseRootPolynomial.Gaussian) :
    (endBank branch evaluated
      charts energies).errors previous potential =
      joinErrors evaluated
      charts energies previous potential := by
  induction evaluated generalizing previous potential with
  | nil => cases charts; rfl
  | cons first rest ih =>
      cases charts with
      | cons replacement head tail => exact congrArg (List.cons _) (ih tail energies.2 _ _)

/-- The packet bank's first-error predicate is exactly the original first connector bound. -/
theorem endBank_firstBound (previous potential : InverseRootPolynomial.Gaussian) (bound :
  InverseRootPolynomial.Coordinate) :
    (endBank branch evaluated
      charts energies).FirstBound previous potential bound ↔
      FirstJoinBound
      evaluated charts energies previous potential bound := by
  cases evaluated with
  | nil => cases charts; rfl
  | cons first rest => cases charts; rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData
