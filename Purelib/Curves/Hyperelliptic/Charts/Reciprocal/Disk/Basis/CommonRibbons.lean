module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Signed physical ribbons from cached common-chart endpoint potentials.
The retained connector budget pays their complete finite sum. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons

open Purelib.Riemann.Topology

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

namespace Connectors

variable {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The signed physical ribbons between consecutive original chart fan samples.

Each ribbon retains both cached endpoint potentials and subtracts the actual connector endpoint area. -/
@[expose] def ribbonValues : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth joinTarget
      requests plans readings → List Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _, _ => []
  | _, .cons _ .nil, _, _, _, _, _ => []
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors =>
      (samples.2.1.firstPotential - samples.1.lastPotential -
        Path.BoundaryRibbon.area connectors.1.firstValue connectors.1.lastValue) ::
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues (.cons next
        remaining) energies.2 samples.2 connectors.2

/-- Every retained signed ribbon meets the original connector target weighted by the squared coefficient norm. -/
theorem ribbonValues_bounded : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    ∀ value ∈ Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues requests energies samples
      connectors, Data.Gaussian.Norm.Basic.normSq value ≤ joinTarget *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, .nil, _, _, _, _, _, _, member => by cases member
  | _, .cons _ .nil, _, _, _, _, _, _, member => by cases member
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors, value, member => by
      change value ∈ (_ :: Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues (.cons next
        remaining) energies.2 samples.2 connectors.2) at member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | tail
      · subst value
        rw [samples.2.1.first_eq, samples.1.last_eq, energies.2.1.property, energies.1.property]
        exact connectors.1.radial_bound
      · exact Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues_bounded
          (.cons next remaining) energies.2 samples.2 connectors.2 value tail

/-- The actual ribbon count is at most the retained original interval count. -/
theorem ribbonValues_count : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues requests energies samples
      connectors).length ≤ intervals.length
  | _, .nil, _, _, _, _, _ => Nat.le_refl _
  | _, .cons _ .nil, _, _, _, _, _ => Nat.zero_le _
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors =>
      Nat.succ_le_succ
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues_count (.cons
        next remaining) energies.2 samples.2 connectors.2)

variable {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
    target sourceTarget floor sourceFloor intervals}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests} {readings :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage requests plans}

set_option genInjectivity false in
/-- The cached signed ribbon list and total with their complete interval-count bound. -/
structure RibbonSample (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget
  energyFloor energyDepth requests plans readings)
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies)
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) where
  /-- The cached original signed ribbon contributions. -/ values : List Normalization.InverseRootPolynomial.Gaussian
  /-- The cached contributions are exactly the ribbons from the retained samples and connectors. -/ values_eq : values =
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues requests energies samples
    connectors
  /-- The cached sum of the original signed ribbons. -/ total : Normalization.InverseRootPolynomial.Gaussian
  /-- The total is the exact Gaussian sum of the retained ribbon list. -/ total_eq : total =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The actual interval count and connector target bound the complete cached ribbon sum. -/ bound :
    Data.Gaussian.Norm.Basic.normSq total ≤ (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
    joinTarget * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity RibbonSample

/-- Cache all original signed ribbon contributions and their total with the paid finite-sum bound. -/
@[expose] def sampleRibbons (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies
  energyTarget energyFloor energyDepth requests plans readings)
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies)
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings)
    (nonnegative : 0 ≤ joinTarget) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.RibbonSample
      energies samples connectors := by
  let values := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues requests energies
    samples connectors
  have bounded := Path.IncrementArea.sum_bound_of_length
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)))
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues_bounded requests energies samples
      connectors) (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.ribbonValues_count requests
      energies samples connectors)
  exact ⟨values, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum values, rfl, bounded.trans_eq (by ring1)⟩

variable {parentAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- The polygon insertion budget also pays the sum of signed radial ribbons. -/
theorem RibbonSample.parent_bound
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      parentAllowance joinFloor)
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings}
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    {connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (sampled : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.RibbonSample energies samples
      connectors) :
    Data.Gaussian.Norm.Basic.normSq sampled.total ≤ parentAllowance^2 *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  sampled.bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.total_paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The entire signed connector contribution consumes one parent allowance. -/
theorem RibbonSample.parent_lower
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      parentAllowance joinFloor)
    (nonnegative : 0 ≤ parentAllowance)
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings}
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    {connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (sampled : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.RibbonSample energies samples
      connectors) :
    -(parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ sampled.total.im / 4 :=
      open Purelib.Algebra in by
  have coefficientNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have enlarged := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct parentAllowance)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)))
  have error : Data.Gaussian.Norm.Basic.normSq ((0 : Normalization.InverseRootPolynomial.Gaussian) - sampled.total)
    ≤ (4 * (parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [Gaussian.Basic.zero_sub, Gaussian.Norm.Basic.normSq_neg]
    exact (sampled.parent_bound budget).trans
      ((show parentAllowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 =
        1 * (parentAllowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2) by
          ring1).trans_le
        (enlarged.trans_eq (by ring1)))
  have estimate := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le (0 :
    Normalization.InverseRootPolynomial.Gaussian) sampled.total
    (parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative) error
  exact (show -(parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    (0 : Normalization.InverseRootPolynomial.Gaussian).im / 4 - parentAllowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by
      change _ = 0 / 4 - _; simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; ring1).trans_le
        estimate

end Connectors
/-- Combine the complete chart and ribbon contributions before identifying
them with the connected path. Every endpoint potential keeps its sign. -/
theorem Traces.with_ribbons_lower {coverFloor spatialFloor : Nat}
    {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers coverFloor}
    {coordinate : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest
      regular common.intervals spatialFloor}
    {arcAllowance connectorAllowance : Normalization.InverseRootPolynomial.Coordinate}
    (arcRequest : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest common basis
      coordinate arcAllowance)
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular
      arcRequest.depth arcRequest.tolerance sourceTarget floor sourceFloor common.intervals}
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
      covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings}
    (preparation : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation requests plans
      readings energyTarget energyFloor)
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies preparation.allowance energyFloor
      energyDepth requests plans readings}
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    (traces : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcRequest.allowance requests plans
      readings paths energies samples)
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      connectorAllowance joinFloor)
    (nonnegative : 0 ≤ connectorAllowance)
    {connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (ribbons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons.Connectors.RibbonSample energies samples
      connectors) :
    -((energyTarget + arcAllowance + connectorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas + ribbons.total).im / 4 := by
  have combined := Fraction.Order.Arithmetic.add_le_add_direct (traces.parent_lower arcRequest preparation)
    (ribbons.parent_lower budget nonnegative)
  exact (show -((energyTarget + arcAllowance + connectorAllowance) *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    -((energyTarget + arcAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) -
      connectorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    (combined.trans_eq (by
        rw [Gaussian.Basic.add_im];
        simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct];
        ring1))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons
