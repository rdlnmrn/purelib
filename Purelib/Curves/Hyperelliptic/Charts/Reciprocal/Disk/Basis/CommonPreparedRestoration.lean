module
import Purelib.Data.List.Append
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Transport prepared-integral errors through the literal source restoration. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Coordinate}
  {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {anchorBank : PrimitiveCells data index
    cover.mesh.edges}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {basis : BasisBounds bounds}
  {joinTarget : Coordinate} {joinFloor : Nat}

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
open Purelib.Riemann.RootContinuation

/-- Every finite dyadic subdivision has a positive number of edges. -/
private theorem dyadic_nonempty (depth : Nat)
    (first last : ClearSheetContinuation.Subdivision.Endpoint) :
    0 < (ClearSheetContinuation.Subdivision.dyadicEdges depth first last).length := by
  induction depth generalizing first last with
  | zero => exact Nat.zero_lt_succ _
  | succ depth ih =>
    rw [ClearSheetContinuation.Subdivision.dyadicEdges, List.Append.length_append]
    exact Nat.lt_of_lt_of_le (ih _ _) (Nat.le_add_right _ _)

/-- The retained common cover contains at least one actual interval. -/
private theorem common_nonempty {coverFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor) : common.intervals ≠ [] := by
  intro empty
  have edges := common.edges_eq
  rw [empty, List.map_nil] at edges
  have positive := dyadic_nonempty
    common.depth
    UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint
  rw [← edges] at positive
  exact Nat.not_lt_zero _ positive

open Purelib.Integration.Path.IncrementAreaReplacement (bracket)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs.BasisBounds (chord_increment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest (firstView
  lastView)
open
  Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.Plan.Acquisition
  (firstReading lastReading first_inside last_inside)

namespace BasisCommonParentRequest

variable {coverFloor : Nat} {common :
  BasisCommonCover cover covers coverFloor}
  {allowance coefficientTarget : Coordinate}

namespace Plan.Acquisition

variable {request :
  BasisCommonParentRequest common basis
  allowance coefficientTarget floor}
  {plan : Plan
    request capSample polynomials minimum}
  {acquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    plan anchorBank bank stage}
  {energyFloor radialDepth : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy (Energies)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples (EnergySamples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank (Connectors)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces (Traces)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
open
  Reciprocal.Disk.Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan.Acquisition.Sample
  (PreparedComparison)

namespace Sample

variable {preparation :
  EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

/-- The chart summary with those very same corrections. -/
@[expose] def restoredChart (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
  (previous : InverseRootPolynomial.Gaussian) :
    IncrementArea.Summary (Acquisition.Sample.restoredPath sample previous) :=
  (IncrementAreaReplacement.bracket sample.connection.summary
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings - sample.endpoints.first.1)
    (sample.endpoints.last.1 - Readings.lastChartValue coefficients request.charts.requests acquired.readings)) |> fun
      summary => IncrementAreaReplacement.bracket summary
    (sample.endpoints.first.1 - previous) (sample.endpoints.last.2 - sample.endpoints.last.1)

namespace PreparedComparison

variable {sample :
  CommonParentSample.BasisCommonParentRequest.Plan.Acquisition.Sample
  acquired preparation originals coefficients radialDepth}

/-- Reuse the prepared integral summary under the same literal endpoint corrections as the restored chart path. No
interior polygon is recomputed. -/
@[expose] def restoredIntegral (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian) :=
  (IncrementAreaReplacement.bracket comparison.weighted.integral
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings - sample.endpoints.first.1)
    (sample.endpoints.last.1 - Readings.lastChartValue coefficients request.charts.requests acquired.readings)) |> fun
      summary => IncrementAreaReplacement.bracket summary
    (sample.endpoints.first.1 - previous) (sample.endpoints.last.2 - sample.endpoints.last.1)

/-- The total error survives restoration unchanged. -/
theorem restored_total_difference (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian) :

      (restoredIntegral
      comparison previous).total -
      (restoredChart
      sample previous).total =
      comparison.totalDifference := by
  rw
    [restoredIntegral,
    restoredChart,
    IncrementAreaReplacement.bracket_total,
    IncrementAreaReplacement.bracket_total, IncrementAreaReplacement.bracket_total,
    IncrementAreaReplacement.bracket_total, comparison.totalDifference_eq]
  ring1

/-- Unequal interior totals leave a location term. In particular, endpoint restoration cannot use the equal-total
replacement lemma. -/
theorem restored_area_difference (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian) :

      (restoredIntegral
      comparison previous).area -
      (restoredChart
      sample previous).area =
      comparison.difference + BoundaryRibbon.area
        (Readings.firstChartValue coefficients request.charts.requests acquired.readings - previous -
          (sample.endpoints.last.2 - Readings.lastChartValue coefficients request.charts.requests acquired.readings))
        comparison.totalDifference := by
  rw
    [restoredIntegral,
    restoredChart,
    IncrementAreaReplacement.bracket_area,
    IncrementAreaReplacement.bracket_area, IncrementAreaReplacement.bracket_area,
    IncrementAreaReplacement.bracket_area, IncrementAreaReplacement.bracket_total,
    IncrementAreaReplacement.bracket_total, comparison.difference_eq, comparison.totalDifference_eq]
  apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, BoundaryRibbon.area,
    Data.Gaussian.Basic.conj, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
    Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
    ring1

/-- Pay the restored area error once a homogeneous bound on the retained endpoint location is available. The primitive
origin is not discarded. -/
private theorem restored_area_bound (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    {locationBound : InverseRootPolynomial.Coordinate}
    (location : Data.Gaussian.Norm.Basic.normSq
      (Readings.firstChartValue coefficients request.charts.requests acquired.readings - previous -
        (sample.endpoints.last.2 - Readings.lastChartValue coefficients request.charts.requests acquired.readings)) ≤
      locationBound * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq
      ((restoredIntegral
      comparison previous).area -
      (restoredChart
      sample previous).area) ≤
      (2 * (4 * allowance)^2 + 8 * locationBound * (4 * allowance)^2) * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct location comparison.total_bounded
    (Data.Gaussian.Norm.Basic.normSq_nonneg comparison.totalDifference) ((Data.Gaussian.Norm.Basic.normSq_nonneg
      _).trans location)
  let position := Readings.firstChartValue coefficients request.charts.requests acquired.readings - previous -
    (sample.endpoints.last.2 - Readings.lastChartValue coefficients request.charts.requests acquired.readings)
  have ribbon : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area position comparison.totalDifference) ≤
      4 * locationBound * (4 * allowance)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq position * Data.Gaussian.Norm.Basic.normSq
        comparison.totalDifference := BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq position * Data.Gaussian.Norm.Basic.normSq
        comparison.totalDifference) := by
        ring1
      _ ≤ 4 * (locationBound * PreparedObservationCoercivity.coefficientNormSq coefficients * ((4 * allowance)^2 *
        PreparedObservationCoercivity.coefficientNormSq coefficients)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
      _ = _ := by ring1
  rw
    [restored_area_difference
    comparison]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      comparison.bounded ribbon)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))

/-- The finite squared norm of the actual coefficient vector is nonnegative. -/
private theorem coefficient_nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- The retained chart allowance has squared size at most one. -/
private theorem local_small : request.charts.localAllowance^2 ≤ 1 := by
  have paid := request.restoration.incoming_paid request.charts.local_positive.le request.source_le
  have divided : request.restoration.target / 16 ≤ request.restoration.target := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 16)).mpr
    exact (show request.restoration.target = request.restoration.target * 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by
          decide : (1 : InverseRootPolynomial.Coordinate) ≤ 16) request.restoration.positive.le)
  exact paid.trans (divided.trans request.restoration.small)

/-- The initial primitive value has a uniform homogeneous bound; its contribution to the trace comparison must therefore
be estimated, not dropped. -/
theorem first_direct_bound (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq sample.endpoints.first.2 ≤ (2 + 8 * basis.coefficient) *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have zeroInside : regular.padded.Contains ((0 : InverseRootPolynomial.Gaussian) * 0) := by
    change ReciprocalExteriorCollar.radius curve ^ 2 * Data.Gaussian.Norm.Basic.normSq ((0 :
      InverseRootPolynomial.Gaussian) * 0) ≤ _
    rw [Data.Gaussian.Basic.mul_zero, Data.Gaussian.Norm.Basic.normSq_zero, Fraction.Field.mul_zero_direct]
    exact Fraction.Order.Arithmetic.sq_nonneg_direct _
  have chart := BasisBounds.chord_increment basis polynomials coefficients branch (first := 0) (last :=
    (Acquisition.firstReading acquired).reading.coordinate) zeroInside (Acquisition.first_inside acquired)
    (left := 0) (right := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
  have atZero : RootRadialGeometry.chord 0 (Acquisition.firstReading acquired).reading.coordinate 0 = 0 := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im] <;> ring1
  have atOne : RootRadialGeometry.chord 0 (Acquisition.firstReading acquired).reading.coordinate 1 =
    (Acquisition.firstReading acquired).reading.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.zero_re, Data.Gaussian.Basic.zero_im] <;> ring1
  have valueZero : polynomials.value coefficients 0 = 0 := by
    unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
    exact (FiniteSum.Fin.sumFin_congr (fun row => by
      rw [(polynomials.get row).primitive_zero, Data.Gaussian.Basic.mul_zero])).trans FiniteSum.Fin.sumFin_zero
  rw [atZero, atOne, valueZero, Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.sub_zero, show ((1 :
    InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct] at chart
  have rootScalar := regular.padded.root_norm_le (root := (Acquisition.firstReading acquired).reading.coordinate)
    (Acquisition.first_inside acquired)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at rootScalar
  have valueBound := chart.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootScalar
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        basis.coefficient_nonnegative))

      coefficient_nonnegative).trans_eq
      (show PreparedObservationCoercivity.coefficientNormSq coefficients * (2 * basis.coefficient * 2) =
      4 * basis.coefficient * PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  have firstEq : Readings.firstChartValue coefficients request.charts.requests acquired.readings =
      polynomials.value coefficients (Acquisition.firstReading acquired).reading.coordinate :=
    Plans.firstReading_chart request.charts.requests acquired.readings (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration.common_nonempty common)
  rw [← firstEq] at valueBound
  have offset := sample.endpoints.first_bounded.direct_close.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      local_small
      coefficient_nonnegative).trans_eq
      (show 1 * PreparedObservationCoercivity.coefficientNormSq coefficients =
        PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (sample.endpoints.first.2 - Readings.firstChartValue coefficients request.charts.requests acquired.readings)
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct offset
      valueBound) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [show sample.endpoints.first.2 - Readings.firstChartValue coefficients request.charts.requests acquired.readings +
    Readings.firstChartValue coefficients request.charts.requests acquired.readings = sample.endpoints.first.2 by ring1]
      at estimate
  exact estimate.trans_eq (by ring1)

/-- Retained direct/chart offsets and the scheduled incoming gap control the location term, independently of the
coefficient vector. -/
private theorem restored_area_bound_of_gap (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤
      request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq
      ((restoredIntegral
      comparison previous).area -
      (restoredChart
      sample previous).area) ≤
      (82 * (4 * allowance)^2) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have small : request.charts.localAllowance^2 * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
    PreparedObservationCoercivity.coefficientNormSq coefficients :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      local_small
      coefficient_nonnegative).trans_eq
      (by ring1)
  have first : Data.Gaussian.Norm.Basic.normSq (Readings.firstChartValue coefficients request.charts.requests
    acquired.readings -
      sample.endpoints.first.2) ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show Readings.firstChartValue coefficients request.charts.requests acquired.readings - sample.endpoints.first.2
      =
      -(sample.endpoints.first.2 - Readings.firstChartValue coefficients request.charts.requests acquired.readings) by
        ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact sample.endpoints.first_bounded.direct_close.trans small
  have last := sample.endpoints.last_bounded.direct_close.trans small
  have gapSmall := gap.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.restoration.small
    coefficient_nonnegative).trans_eq
    (show 1 * PreparedObservationCoercivity.coefficientNormSq coefficients =
      PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  have incoming := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings)
    sample.endpoints.first.2 previous).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
      gapSmall) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have location := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings - previous)
    (sample.endpoints.last.2 - Readings.lastChartValue coefficients request.charts.requests acquired.readings)).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct incoming
      last) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq
      (show 2 * (2 * (PreparedObservationCoercivity.coefficientNormSq coefficients +
        PreparedObservationCoercivity.coefficientNormSq coefficients) + PreparedObservationCoercivity.coefficientNormSq
        coefficients) =
        10 * PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  exact
    (restored_area_bound
    comparison previous location).trans_eq (by ring1)

/-- The first restored parent starts at its own cached direct endpoint. -/
theorem restored_first_area_bound (comparison : Acquisition.Sample.PreparedComparison sample) :
    Data.Gaussian.Norm.Basic.normSq
      ((restoredIntegral
      comparison sample.endpoints.first.2).area -

        (restoredChart
        sample sample.endpoints.first.2).area) ≤
      (82 * (4 * allowance)^2) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  apply
    restored_area_bound_of_gap
    comparison
  rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct request.restoration.positive.le
    coefficient_nonnegative

/-- The restored chart total satisfies a homogeneous bound when the actual incoming endpoint gap is paid.

The estimate retains both direct/chart offsets and the root displacement of the original prepared parent. -/
private theorem restored_chart_total_bound (sample : Acquisition.Sample acquired preparation originals coefficients
  radialDepth) (previous : InverseRootPolynomial.Gaussian)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq
      (restoredChart
      sample previous).total ≤ (12 + 64 * basis.coefficient) * PreparedObservationCoercivity.coefficientNormSq
      coefficients := by
  have firstRootScalar := regular.padded.root_norm_le (root := (Acquisition.firstReading acquired).reading.coordinate)
    (Acquisition.first_inside acquired)
  have lastRootScalar := regular.padded.root_norm_le (root := (Acquisition.lastReading acquired).reading.coordinate)
    (Acquisition.last_inside acquired)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstRootScalar lastRootScalar
  have roots := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (Acquisition.lastReading acquired).reading.coordinate
    (Acquisition.firstReading acquired).reading.coordinate).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct lastRootScalar firstRootScalar)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by
          decide : (2 : InverseRootPolynomial.Coordinate) * (2 + 2) = 8))
  have chart := BasisBounds.chord_increment basis polynomials coefficients branch (first := (Acquisition.firstReading
    acquired).reading.coordinate) (last := (Acquisition.lastReading acquired).reading.coordinate)
    (Acquisition.first_inside acquired) (Acquisition.last_inside acquired)
    (left := 0) (right := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
  have atZero : RootRadialGeometry.chord (Acquisition.firstReading acquired).reading.coordinate (Acquisition.lastReading
    acquired).reading.coordinate 0 =
      (Acquisition.firstReading acquired).reading.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im] <;> ring1
  have atOne : RootRadialGeometry.chord (Acquisition.firstReading acquired).reading.coordinate (Acquisition.lastReading
    acquired).reading.coordinate 1 =
      (Acquisition.lastReading acquired).reading.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootRadialGeometry.chord,
      Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im] <;> ring1
  rw [atZero, atOne, show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct]
    at chart
  have chartBound := chart.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct roots (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) basis.coefficient_nonnegative))

      coefficient_nonnegative).trans_eq
      (show PreparedObservationCoercivity.coefficientNormSq coefficients * (2 * basis.coefficient * 8) =
      16 * basis.coefficient * PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  have firstEq : Readings.firstChartValue coefficients request.charts.requests acquired.readings =
      polynomials.value coefficients (Acquisition.firstReading acquired).reading.coordinate :=
    Plans.firstReading_chart request.charts.requests acquired.readings (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration.common_nonempty common)
  have lastEq : Readings.lastChartValue coefficients request.charts.requests acquired.readings =
      polynomials.value coefficients (Acquisition.lastReading acquired).reading.coordinate :=
    Plans.lastReading_chart request.charts.requests acquired.readings (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration.common_nonempty common)
  rw [← firstEq, ← lastEq] at chartBound
  have small : request.charts.localAllowance^2 * PreparedObservationCoercivity.coefficientNormSq coefficients ≤
    PreparedObservationCoercivity.coefficientNormSq coefficients :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      local_small
      coefficient_nonnegative).trans_eq
      (by ring1)
  have first : Data.Gaussian.Norm.Basic.normSq (Readings.firstChartValue coefficients request.charts.requests
    acquired.readings - sample.endpoints.first.2) ≤
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show Readings.firstChartValue coefficients request.charts.requests acquired.readings - sample.endpoints.first.2
      =
      -(sample.endpoints.first.2 - Readings.firstChartValue coefficients request.charts.requests acquired.readings) by
        ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact sample.endpoints.first_bounded.direct_close.trans small
  have last := sample.endpoints.last_bounded.direct_close.trans small
  have gapSmall := gap.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.restoration.small
    coefficient_nonnegative).trans_eq
    (show 1 * PreparedObservationCoercivity.coefficientNormSq coefficients =
      PreparedObservationCoercivity.coefficientNormSq coefficients by ring1))
  have left := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via sample.endpoints.last.2
    (Readings.lastChartValue coefficients request.charts.requests acquired.readings)
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct last
      chartBound) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have right := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings) sample.endpoints.first.2
      previous).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
      gapSmall) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have total :
    (restoredChart
    sample previous).total = sample.endpoints.last.2 - previous := by
    rw
      [restoredChart,
      IncrementAreaReplacement.bracket_total, IncrementAreaReplacement.bracket_total, sample.connection.total_eq]
    ring1
  rw [total]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via sample.endpoints.last.2
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings) previous).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left
      right) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))

/-- A single coefficient-independent ceiling for both restored block totals. -/
@[expose] def restoredTotalBound : Coordinate := 2 * ((4 * allowance)^2 + 12 + 64 * basis.coefficient)

/-- Both restored integral and chart totals satisfy the same retained homogeneous ceiling once the incoming gap is paid.
-/
private theorem restored_total_bounds_of_gap (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq
      (restoredIntegral
      comparison previous).total ≤
      restoredTotalBound
      (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq
      (restoredChart
      sample previous).total ≤
      restoredTotalBound
      (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have chart :=
    restored_chart_total_bound
    sample previous branch gap
  have error : Data.Gaussian.Norm.Basic.normSq
    ((restoredIntegral
    comparison previous).total -
    (restoredChart
    sample previous).total) ≤
      (4 * allowance)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw
      [restored_total_difference
      comparison]
    exact comparison.total_bounded
  have integral := (Data.Gaussian.Norm.Bounds.normSq_add_le_two

      ((restoredIntegral
      comparison previous).total -
      (restoredChart
      sample previous).total)

      (restoredChart
      sample previous).total).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct error
      chart) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [show
    (restoredIntegral
    comparison previous).total -
    (restoredChart
    sample previous).total +

      (restoredChart
      sample previous).total =
      (restoredIntegral
      comparison previous).total by ring1] at integral
  have larger : 12 + 64 * basis.coefficient ≤
    restoredTotalBound
    (basis := basis) (allowance := allowance) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤
      2) (Fraction.Order.Arithmetic.sq_nonneg_direct (4 * allowance)))
      (add_nonneg (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 12)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
          basis.coefficient_nonnegative))).trans_eq (by
          unfold
            restoredTotalBound;
            ring1)
  exact ⟨integral.trans_eq (by
      unfold restoredTotalBound;
      ring1),
    chart.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct larger
      coefficient_nonnegative)⟩

/-- The first restored integral and chart totals satisfy the common ceiling at their own cached direct starting
endpoint. -/
theorem restored_first_total_bounds (comparison : Acquisition.Sample.PreparedComparison sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq
      (restoredIntegral
      comparison sample.endpoints.first.2).total ≤

        restoredTotalBound
        (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq
      (restoredChart
      sample sample.endpoints.first.2).total ≤

        restoredTotalBound
        (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  apply
    restored_total_bounds_of_gap
    comparison sample.endpoints.first.2 branch
  rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct request.restoration.positive.le
    coefficient_nonnegative

variable {previousCount previousCoverFloor previousFloor previousMinimum previousStage previousEnergyFloor : Nat}
  {previousParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {previousPatch : PreparedPatch previousParent}
  {previousData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data previousPatch
    previousCount}
  {previousCover : Cover previousData}
  {previousCovers : BasisSourceCovers
    previousParent}
  {previousCommon : BasisCommonCover previousCover
    previousCovers previousCoverFloor}
  {previousCoefficientTarget : Coordinate}
  {previousRequest :
    BasisCommonParentRequest
    previousCommon basis allowance previousCoefficientTarget previousFloor}
  {previousPlan :
    Plan
    previousRequest capSample polynomials previousMinimum}
  {previousAnchorBank : PrimitiveCells
    previousData index previousCover.mesh.edges}
  {previousBank :
    BasisSourceLocations.SampleBank
    previousCovers index}
  {previousAcquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    previousPlan previousAnchorBank previousBank previousStage}
  {previousPreparation :
    EnergyPreparation
    previousRequest.charts.requests previousPlan.charts previousAcquired.readings allowance previousEnergyFloor}
  {previousOriginals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    previousCovers index}

/-- Scheduled incoming root readings bound the retained direct endpoint gap. -/
theorem incoming_gap
    (previous : Acquisition.Sample previousAcquired previousPreparation previousOriginals coefficients radialDepth)
    (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    {joined : ArcOwners.Join (BasisCommonParentRequest.lastView previousRequest).point
      (BasisCommonParentRequest.firstView request).point}
    (joining : RestorationJoins.BasisRestorationRequest basis joined request.restoration.target joinFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (previousLater : joining.index ≤ previousStage) (later : joining.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous.endpoints.last.2) ≤
      request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have targetEq : previousRequest.restoration.target = request.restoration.target := by
    rw [previousRequest.restoration.target_eq, request.restoration.target_eq,
      previousRequest.restoration.source_eq, request.restoration.source_eq]
  have previousPaid := previousRequest.restoration.incoming_paid
    previousRequest.charts.local_positive.le previousRequest.source_le
  rw [targetEq] at previousPaid
  have currentPaid := request.restoration.incoming_paid request.charts.local_positive.le request.source_le
  have previousClose := previous.endpoints.last_bounded.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (previousPaid.trans_eq joining.endpoint_eq.symm)
      coefficient_nonnegative)
  have currentClose := sample.endpoints.first_bounded.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (currentPaid.trans_eq joining.endpoint_eq.symm)
      coefficient_nonnegative)
  rw [Plans.lastReading_chart previousRequest.charts.requests previousAcquired.readings
    (BasisCommonChartRequests.common_from previousCommon)
      (common_nonempty previousCommon)] at previousClose
  rw [Plans.firstReading_chart request.charts.requests acquired.readings
    (BasisCommonChartRequests.common_from common)
      (common_nonempty common)] at currentClose
  have chartGap := joining.chart_gap polynomials coefficients (Acquisition.lastReading previousAcquired).reading
    (Acquisition.firstReading acquired).reading
    branch (Acquisition.last_inside previousAcquired) (Acquisition.first_inside acquired) previousLater later
  exact joining.direct_gap coefficients previousClose currentClose chartGap

/-- The actual predecessor and scheduled physical root join pay restoration. -/
theorem restored_after_area_bound
    (previous : Acquisition.Sample previousAcquired previousPreparation previousOriginals coefficients radialDepth)
    (comparison : Acquisition.Sample.PreparedComparison sample)
    {joined : ArcOwners.Join (BasisCommonParentRequest.lastView previousRequest).point
      (BasisCommonParentRequest.firstView request).point}
    (joining : RestorationJoins.BasisRestorationRequest basis joined request.restoration.target joinFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (previousLater : joining.index ≤ previousStage) (later : joining.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      ((restoredIntegral
      comparison previous.endpoints.last.2).area -

        (restoredChart
        sample previous.endpoints.last.2).area) ≤
      (82 * (4 * allowance)^2) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  exact
    restored_area_bound_of_gap
    comparison previous.endpoints.last.2

      (incoming_gap
      previous sample joining branch previousLater later)

/-- Both later-parent totals use the same preselected homogeneous ceiling. -/
theorem restored_after_total_bounds
    (previous : Acquisition.Sample previousAcquired previousPreparation previousOriginals coefficients radialDepth)
    (comparison : Acquisition.Sample.PreparedComparison sample)
    {joined : ArcOwners.Join (BasisCommonParentRequest.lastView previousRequest).point
      (BasisCommonParentRequest.firstView request).point}
    (joining : RestorationJoins.BasisRestorationRequest basis joined request.restoration.target joinFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (previousLater : joining.index ≤ previousStage) (later : joining.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (restoredIntegral
      comparison previous.endpoints.last.2).total ≤

        restoredTotalBound
        (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq
      (restoredChart
      sample previous.endpoints.last.2).total ≤

        restoredTotalBound
        (basis := basis) (allowance := allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  exact
    restored_total_bounds_of_gap
    comparison previous.endpoints.last.2 branch

      (incoming_gap
      previous sample joining branch previousLater later)

end PreparedComparison
end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
