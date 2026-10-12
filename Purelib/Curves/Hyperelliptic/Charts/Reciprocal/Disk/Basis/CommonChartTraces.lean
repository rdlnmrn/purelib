module
import Purelib.Algebra.NatCast
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartArcs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
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

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Homogeneous trace certificates for every actual common chart polygon,
using the retained fan samples and the preselected arc allowance. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces

open Purelib.Riemann.RootContinuation

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

variable {originals :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The dependent homogeneous trace certificates for the original common-chart polygons.

Each certificate keeps its actual polynomial endpoints, cached fan potentials and separately paid fan and arc errors. -/
@[expose] def Traces (arcAllowance : Normalization.InverseRootPolynomial.Coordinate) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies → Type
  | _, .nil, _, _, _, _, _ => PUnit
  | _, .cons _ tail, plans, readings, paths, energies, samples =>
      Path.HomogeneousTraceConnection.HomogeneousTrace coefficients (paths.1.paired.pairs.map Prod.snd)
        (polynomials.value coefficients readings.1.evaluated.first.root.coordinate)
        (polynomials.value coefficients readings.1.evaluated.last.root.coordinate)
        samples.1.firstPotential samples.1.lastPotential (energies.1.val.error + arcAllowance) ×
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcAllowance tail plans.2
        readings.2 paths.2 energies.2 samples.2

namespace Traces

/-- Build every original chart trace from its cached fan sample and paid coordinate arc bounds. -/
@[expose] def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (padded : target ≤ regular.padded.squareTolerance) (mesh : target ≤ Rational.Geometric.Basic.quarterRadius 1 depth)
    (arcAllowance : Normalization.InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ arcAllowance) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (coordinates : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds
      regular intervals) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonCoordinateBounds.ArcPaid basis depth
      arcAllowance coordinates → Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcAllowance
      requests plans readings paths energies samples
  | _, .nil, _, _, _, _, _, .nil, _ => ⟨⟩
  | _, .cons _ tail, plans, readings, paths, energies, samples, .cons head remaining, paid =>

        ⟨IntervalChartArcs.BasisIntervalChartRequest.Plan.Evaluation.PathData.trace
        readings.1.evaluated paths.1 energies.1.val samples.1 basis head
          (CoordinatePolynomial.build readings.1.sample)
          branch padded mesh arcAllowance nonnegative paid.1,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces.build basis branch padded
          mesh arcAllowance nonnegative tail plans.2 readings.2 paths.2 energies.2 samples.2 remaining paid.2⟩

variable {arcAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- Read the cached corrected chart areas in original interval order. -/
@[expose] def correctedAreas : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    {paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings} →
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcAllowance requests plans readings paths
      energies samples → List Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _, _, _ => []
  | _, .cons _ _, _, _, _, _, _, traces => traces.1.corrected ::
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces.correctedAreas traces.2

/-- The corrected chart area sum has the coefficient-weighted lower bound paid by the actual interval count and common
fan and arc allowances. -/
theorem lower : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers)} →
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals} →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    {paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings} →
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies} →
    (traces : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcAllowance requests plans readings
      paths energies samples) →
    -(((intervals.length : Normalization.InverseRootPolynomial.Coordinate) * (energyTarget + arcAllowance)) *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas).im / 4
  | _, .nil, _, _, _, _, _, _ => by
      change -((0 * (energyTarget + arcAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) ≤ 0 / 4
      rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct]
      decide
  | _, .cons _ _, _, _, _, energies, _, traces => by
      have coefficientNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
        Algebra.FiniteSum.Fin.sumFin_zero.symm.trans_le
        (Algebra.FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
          Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
          (coefficients row)))
      have head := (Fraction.Order.Arithmetic.neg_le_neg_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.add_le_add_direct energies.1.val.error_lt.le (le_refl arcAllowance))
          coefficientNonnegative)).trans traces.1.lower
      have combined := Fraction.Order.Arithmetic.add_le_add_direct head
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces.lower traces.2)
      change -((((_ + 1 : Nat) : Normalization.InverseRootPolynomial.Coordinate) * (energyTarget + arcAllowance)) *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
        (traces.1.corrected + Data.Gaussian.Norm.Sum.Basic.gaussianSum traces.2.correctedAreas).im / 4
      rw [Purelib.Algebra.NatCast.add, Nat.cast_one, Gaussian.Basic.add_im]
      exact (show -(((_ + 1) * (energyTarget + arcAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) =
        -((energyTarget + arcAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) +
        -((_ * (energyTarget + arcAllowance)) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
          by ring1).trans_le
        (combined.trans_eq (by simp only [-eq_self, -iff_self, Fraction.Field.div_eq_mul_inv_direct]; ring1))

variable {coverFloor spatialFloor : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers coverFloor}
  {coordinate : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest regular
    common.intervals spatialFloor}
  {parentAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- Construct the original chart traces from the retained arc request, acquired fan energies and cached samples. -/
@[expose] def ofRequest (arcRequest : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest
  common basis coordinate parentAllowance)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular
      arcRequest.depth arcRequest.tolerance sourceTarget floor sourceFloor common.intervals)
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans)
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings)
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcRequest.allowance requests plans readings
      paths energies samples :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces.build basis branch
    (arcRequest.coordinate_tolerance.trans coordinate.padded) arcRequest.mesh
    arcRequest.allowance arcRequest.positive.le requests plans readings paths energies samples coordinate.bounds
      arcRequest.arc_paid

/-- Parent fan and arc allowances account for every interval; no connector
or endpoint cancellation is included in this sum. -/
theorem parent_lower (arcRequest : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest
  common basis coordinate parentAllowance)
    {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular
      arcRequest.depth arcRequest.tolerance sourceTarget floor sourceFloor common.intervals}
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    {paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings}
    (preparation : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation requests plans
      readings energyTarget energyFloor)
    {energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies preparation.allowance energyFloor
      energyDepth requests plans readings}
    {samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies}
    (traces : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces.Traces arcRequest.allowance requests plans
      readings paths energies samples) :
    -((energyTarget + parentAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas).im / 4 := open Purelib.Algebra in by
  have coefficientNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have paid : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * (preparation.allowance +
    arcRequest.allowance) ≤
      energyTarget + parentAllowance :=
    (show (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * (preparation.allowance +
      arcRequest.allowance) =
      (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * preparation.allowance +
      (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * arcRequest.allowance by
        ring1).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct preparation.paid arcRequest.sum_paid)
  exact (Fraction.Order.Arithmetic.neg_le_neg_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    coefficientNonnegative)).trans traces.lower

end Traces
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces
