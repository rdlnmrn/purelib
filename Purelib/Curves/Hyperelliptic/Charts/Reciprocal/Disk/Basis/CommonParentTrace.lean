module
-- The exposed connection retains the original nonempty-cover certificate.
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! One paid homogeneous trace on the literal connected common-parent path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentTrace

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : UniformReciprocalCover.Cover data} {covers :
    SourceLocations.BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Traces

variable {coverFloor spatialFloor : Nat}
  {common : CommonCover.BasisCommonCover cover covers coverFloor}
  {coordinate : CommonCoordinateRequest.BasisCommonCoordinateRequest regular
    common.intervals spatialFloor}
  {arcAllowance connectorAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- Construct the paid homogeneous trace on the literal joined original parent path.

The cached increment summary, corrected chart areas and signed ribbons retain exact endpoint/potential readbacks and the
combined energy, arc and connector allowance. -/
@[expose] def connection (arcRequest : CommonArcRequest.BasisCommonArcRequest
  common basis coordinate arcAllowance)
    {requests : CommonChartSchedule.BasisCommonChartRequests regular
      arcRequest.depth arcRequest.tolerance sourceTarget floor sourceFloor common.intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    {paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings}
    (preparation : CommonEnergyPreparation.EnergyPreparation requests plans
      readings energyTarget energyFloor)
    {energies : CommonChartEnergy.Energies preparation.allowance energyFloor
      energyDepth requests plans readings}
    {samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    (traces : CommonChartTraces.Traces arcRequest.allowance requests plans
      readings paths energies samples)
    (budget : CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      connectorAllowance joinFloor)
    (nonnegative : 0 ≤ connectorAllowance)
    {connectors : CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (ribbons : CommonRibbons.Connectors.RibbonSample energies samples
      connectors)
    (summary : Path.IncrementArea.Summary

        (((CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedBlocks
        0 paths connectors).map (fun block => block.1 :: block.2)).flatten)) :
    Path.HomogeneousTraceConnection.HomogeneousTrace coefficients

        (((CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedBlocks
        0 paths connectors).map (fun block => block.1 :: block.2)).flatten)
      (CommonTraceReadback.Readings.firstChartValue coefficients requests
        readings) (CommonTraceReadback.Readings.lastChartValue coefficients
        requests readings)
      (CommonTraceReadback.EnergySamples.firstPotential requests samples)
        (CommonTraceReadback.EnergySamples.lastPotential requests samples)
      (energyTarget + arcAllowance + connectorAllowance) := by
  let first := CommonTraceReadback.Readings.firstChartValue coefficients
    requests readings
  let trace := summary.area + Path.BoundaryRibbon.area first summary.total
  let corrected := Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas + ribbons.total
  have traceEq : trace = Path.IncrementArea.traceArea first

        (((CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedBlocks
        0 paths connectors).map (fun block => block.1 :: block.2)).flatten) := by
    rw [Path.IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq]
  have begins : first + 0 = CommonTraceReadback.Readings.firstChartValue
    coefficients requests readings := _root_.add_zero first
  have total := CommonTraceReadback.Traces.joined_total requests readings
    paths energies samples traces connectors
    (CommonParentBoundary.common_nonempty common) first 0 begins
  have identity := CommonTraceReadback.Traces.joined_trace requests readings
    paths energies samples traces connectors
    (CommonParentBoundary.common_nonempty common) first 0 begins
  rw [← traceEq, Path.IncrementArea.area_self, _root_.add_zero] at identity
  have correctedEq : corrected = -trace +
    CommonTraceReadback.EnergySamples.lastPotential requests samples -
    CommonTraceReadback.EnergySamples.firstPotential requests samples := by
    dsimp only [corrected]
    rw [ribbons.total_eq, ribbons.values_eq]
    exact identity
  exact ⟨summary, summary.total_eq.trans total, trace, traceEq, corrected, correctedEq,
    CommonRibbons.Traces.with_ribbons_lower arcRequest preparation traces
      budget nonnegative ribbons⟩

end Traces
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentTrace
