module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
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
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.HomogeneousTraceConnection
public import Purelib.Integration.Path.HomogeneousTraceRestoration
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentTrace
public import Purelib.Integration.Budget.Trace.Restoration
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

open Purelib.Data.Rat

open Purelib.Integration.Budget.Trace

open Purelib.Integration.Path

open Purelib.Integration.Path.HomogeneousTraceRestoration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Restore the actual connected common-parent trace using its cached extremes.
The remaining incoming estimates refer to the original physical root join. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Coordinate}
  {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {anchorBank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index
    cover.mesh.edges}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Coordinate} {joinFloor : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest (BasisCommonCoordinateRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest (BasisCommonArcRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget (BasisCommonConnectorBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans
  (Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy (Energies)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples (EnergySamples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank (Connectors)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces (Traces)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation (BasisFanGeometry)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
  covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)
open Purelib.Integration.Path.HomogeneousTraceRestoration (sourceRestoredPath)
open Purelib.Integration.Path.HomogeneousTraceRestoration.HomogeneousTrace
open Purelib.Integration.Path.IncrementRestoration (potential)
open Purelib.Integration.Budget.Trace.Restoration (BasisCommonRestorationAllowance)

namespace Paths.Extremes

variable {intervals : List (BasisCommonInterval
  cover covers)}
  {requests : BasisCommonChartRequests
    regular depth target sourceTarget floor sourceFloor intervals}
  {plans : Plans
    capSample polynomials minimum requests} {readings :
    CommonChartReadings.BasisCommonChartRequests.Plans.Readings
    anchorBank bank stage requests plans}
  {paths :
    Paths
    originals coefficients requests plans readings}
  {connectors : Connectors coefficients
    energyDepth joinTarget requests plans readings}
  {firstPotential lastPotential : Gaussian} {loss allowance :
    Coordinate}

/-- No source/chart endpoint bounds are supplied: the acquired extreme combinations and preselected allowance discharge
all four of them. -/
def restore (ends : Paths.Extremes paths)
    (connection : HomogeneousTraceConnection.HomogeneousTrace coefficients
      (((Paths.joinedBlocks 0 paths connectors).map (fun block => block.1 :: block.2)).flatten)
      (Readings.firstChartValue coefficients requests readings) (Readings.lastChartValue coefficients requests readings)
      firstPotential lastPotential loss)
    (allocation : Restoration.BasisCommonRestorationAllowance allowance) (positive : 0 ≤ allowance)
    (sourcePaid : sourceTarget ^ 2 ≤ allocation.sourceAllowance ^ 2)
    (previous previousPotential : InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (ends.first.2 - previous) ≤ allocation.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (joined : Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential firstPotential
      (Readings.firstChartValue coefficients requests readings) ends.first.2 -
        previousPotential - BoundaryRibbon.area previous ends.first.2) ≤
      (80 * allocation.target + 2 * allocation.target) * (PreparedObservationCoercivity.coefficientNormSq coefficients)
        ^ 2) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients
      (HomogeneousTraceRestoration.sourceRestoredPath (((Paths.joinedBlocks 0 paths connectors).map (fun block =>
        block.1 :: block.2)).flatten)
        (Readings.firstChartValue coefficients requests readings) (Readings.lastChartValue coefficients requests
          readings)
        ends.first.1 ends.last.1 ends.last.2 previous)
      previous ends.last.2 previousPotential
      (IncrementRestoration.potential lastPotential (Readings.lastChartValue coefficients requests readings)
        ends.last.2) (loss + allowance) := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have sourceBound : 4 * sourceTarget ^ 2 ≤ allocation.target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourcePaid (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq allocation.target_eq.symm
  have chartBound : 10 * sourceTarget ^ 2 ≤ 4 * allocation.target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourcePaid (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10)).trans allocation.chart_paid
  have firstSource := ends.first_bounded.source_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    sourceBound normNonnegative)
  have lastSource : Data.Gaussian.Norm.Basic.normSq (ends.last.2 - ends.last.1) ≤ allocation.target *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show ends.last.2 - ends.last.1 = -(ends.last.1 - ends.last.2) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact ends.last_bounded.source_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourceBound
      normNonnegative)
  have firstChart : Data.Gaussian.Norm.Basic.normSq (Readings.firstChartValue coefficients requests readings -
    ends.first.1) ≤
      4 * allocation.target * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show Readings.firstChartValue coefficients requests readings - ends.first.1 =
      -(ends.first.1 - Readings.firstChartValue coefficients requests readings) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
    exact ends.first_bounded.chart_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartBound
      normNonnegative)
  have lastChart := ends.last_bounded.chart_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    chartBound normNonnegative)
  exact HomogeneousTrace.restore connection ends.first.1 ends.last.1 ends.first.2 ends.last.2 previous previousPotential
    allocation.positive.le allocation.positive.le allocation.small firstSource lastSource firstChart lastChart gap
      joined
    allowance positive allocation.paid

end Paths.Extremes
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration
