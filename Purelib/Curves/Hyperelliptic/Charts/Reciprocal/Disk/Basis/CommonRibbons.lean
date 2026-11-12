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

open Purelib.Data.Rat.Fraction.Order

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

namespace Connectors

variable {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The signed physical ribbons between consecutive original chart fan samples.

Each ribbon retains both cached endpoint potentials and subtracts the actual connector endpoint area. -/
@[expose] def ribbonValues : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies →
    CommonConnectorBank.Connectors coefficients energyDepth joinTarget
      requests plans readings → List Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _, _ => []
  | _, .cons _ .nil, _, _, _, _, _ => []
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors =>
      (samples.2.1.firstPotential - samples.1.lastPotential -
        Path.BoundaryRibbon.area connectors.1.firstValue connectors.1.lastValue) ::
      Connectors.ribbonValues (.cons next
        remaining) energies.2 samples.2 connectors.2

/-- Every retained signed ribbon meets the original connector target weighted by the squared coefficient norm. -/
theorem ribbonValues_bounded : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    ∀ value ∈ ribbonValues requests energies samples
      connectors, Gaussian.Norm.Basic.normSq value ≤ joinTarget *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, .nil, _, _, _, _, _, _, member => by cases member
  | _, .cons _ .nil, _, _, _, _, _, _, member => by cases member
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors, value, member => by
      change value ∈ (_ :: ribbonValues (.cons next
        remaining) energies.2 samples.2 connectors.2) at member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | tail
      · subst value
        rw [samples.2.1.first_eq, samples.1.last_eq, energies.2.1.property, energies.1.property]
        exact connectors.1.radial_bound
      · exact Connectors.ribbonValues_bounded
          (.cons next remaining) energies.2 samples.2 connectors.2 value tail

/-- The actual ribbon count is at most the retained original interval count. -/
theorem ribbonValues_count : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    (ribbonValues requests energies samples
      connectors).length ≤ intervals.length
  | _, .nil, _, _, _, _, _ => Nat.le_refl _
  | _, .cons _ .nil, _, _, _, _, _ => Nat.zero_le _
  | _, .cons _ (.cons next remaining), _, _, energies, samples, connectors =>
      Nat.succ_le_succ
        (Connectors.ribbonValues_count (.cons
        next remaining) energies.2 samples.2 connectors.2)

variable {intervals : List (CommonCover.BasisCommonInterval cover covers)}
  {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
    target sourceTarget floor sourceFloor intervals}
  {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests} {readings :
    CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage requests plans}

set_option genInjectivity false in
/-- The cached signed ribbon list and total with their complete interval-count bound. -/
structure RibbonSample (energies : CommonChartEnergy.Energies energyTarget
  energyFloor energyDepth requests plans readings)
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies)
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) where
  /-- The cached original signed ribbon contributions. -/ values : List Normalization.InverseRootPolynomial.Gaussian
  /-- The cached contributions are exactly the ribbons from the retained samples and connectors. -/ values_eq : values =
    ribbonValues requests energies samples
    connectors
  /-- The cached sum of the original signed ribbons. -/ total : Normalization.InverseRootPolynomial.Gaussian
  /-- The total is the exact Gaussian sum of the retained ribbon list. -/ total_eq : total =
    Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The actual interval count and connector target bound the complete cached ribbon sum. -/ bound :
    Gaussian.Norm.Basic.normSq total ≤ (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
    joinTarget * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity RibbonSample

/-- Cache all original signed ribbon contributions and their total with the paid finite-sum bound. -/
@[expose] def sampleRibbons (energies : CommonChartEnergy.Energies
  energyTarget energyFloor energyDepth requests plans readings)
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies)
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings)
    (nonnegative : 0 ≤ joinTarget) : RibbonSample
      energies samples connectors := by
  let values := ribbonValues requests energies
    samples connectors
  have bounded := Path.IncrementArea.sum_bound_of_length
    (Arithmetic.mul_nonneg_direct nonnegative (Arithmetic.sq_nonneg_direct
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)))
    (ribbonValues_bounded requests energies samples
      connectors) (ribbonValues_count requests
      energies samples connectors)
  exact ⟨values, rfl, Gaussian.Norm.Sum.Basic.gaussianSum values, rfl, bounded.trans_eq (by ring1)⟩

variable {parentAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- The polygon insertion budget also pays the sum of signed radial ribbons. -/
theorem RibbonSample.parent_bound
    (budget : CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      parentAllowance joinFloor)
    {energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings}
    {samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    {connectors : CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (sampled : RibbonSample energies samples
      connectors) :
    Gaussian.Norm.Basic.normSq sampled.total ≤ parentAllowance^2 *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  sampled.bound.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct budget.total_paid
    (Arithmetic.sq_nonneg_direct _))

/-- The entire signed connector contribution consumes one parent allowance. -/
theorem RibbonSample.parent_lower
    (budget : CommonConnectorBudget.BasisCommonConnectorBudget basis requests
      parentAllowance joinFloor)
    (nonnegative : 0 ≤ parentAllowance)
    {energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings}
    {samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    {connectors : CommonConnectorBank.Connectors coefficients energyDepth
      budget.tolerance requests plans readings}
    (sampled : RibbonSample energies samples
      connectors) :
    -(parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤ sampled.total.im / 4 :=
      open Purelib.Algebra in by
  have coefficientNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg
      (coefficients row)))
  have enlarged := Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
    (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct parentAllowance)
      (Arithmetic.sq_nonneg_direct (Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)))
  have error : Gaussian.Norm.Basic.normSq ((0 : Normalization.InverseRootPolynomial.Gaussian) - sampled.total)
    ≤ (4 * (parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))^2 := by
    rw [Gaussian.Basic.zero_sub, Gaussian.Norm.Basic.normSq_neg]
    exact (sampled.parent_bound budget).trans
      ((show parentAllowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 =
        1 * (parentAllowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2) by
          ring1).trans_le
        (enlarged.trans_eq (by ring1)))
  have estimate := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le (0 :
    Normalization.InverseRootPolynomial.Gaussian) sampled.total
    (parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative) error
  exact (show -(parentAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
    (0 : Normalization.InverseRootPolynomial.Gaussian).im / 4 - parentAllowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients by
      change _ = 0 / 4 - _; simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; ring1).trans_le
        estimate

end Connectors
/-- Combine the complete chart and ribbon contributions before identifying
them with the connected path. Every endpoint potential keeps its sign. -/
theorem Traces.with_ribbons_lower {coverFloor spatialFloor : Nat}
    {common : CommonCover.BasisCommonCover cover covers coverFloor}
    {coordinate : CommonCoordinateRequest.BasisCommonCoordinateRequest
      regular common.intervals spatialFloor}
    {arcAllowance connectorAllowance : Normalization.InverseRootPolynomial.Coordinate}
    (arcRequest : CommonArcRequest.BasisCommonArcRequest common basis
      coordinate arcAllowance)
    {requests : CommonChartSchedule.BasisCommonChartRequests regular
      arcRequest.depth arcRequest.tolerance sourceTarget floor sourceFloor common.intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
      covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
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
    (ribbons : Connectors.RibbonSample energies samples
      connectors) :
    -((energyTarget + arcAllowance + connectorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients) ≤
      (Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas + ribbons.total).im / 4 := by
  have combined := Arithmetic.add_le_add_direct (traces.parent_lower arcRequest preparation)
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
