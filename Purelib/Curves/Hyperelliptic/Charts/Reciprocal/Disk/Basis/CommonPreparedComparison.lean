module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
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
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTotals

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement.CommonPrimitivePlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Compare the retained connected chart polygon with actual prepared child
integrals on the same original numerical banks and common cover. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison

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

namespace Sample

variable {preparation :
  EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)

/-- Four successive Gaussian discrepancies bounded by one squared radius give an endpoint bound of sixteen times that
radius. -/
private theorem four_steps (a b c d e : InverseRootPolynomial.Gaussian) (radius : InverseRootPolynomial.Coordinate)
    (ab : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ radius) (bc : Data.Gaussian.Norm.Basic.normSq (b -
      c) ≤ radius)
    (cd : Data.Gaussian.Norm.Basic.normSq (c - d) ≤ radius) (de : Data.Gaussian.Norm.Basic.normSq (d -
      e) ≤ radius) :
    Data.Gaussian.Norm.Basic.normSq (a - e) ≤ 16 * radius := by
  have left := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via a b c).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ab bc) (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have right := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via c d e).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct cd de) (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  exact ((Data.Gaussian.Norm.Bounds.normSq_sub_le_via a c e).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left right)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))).trans_eq (by ring1)

/-- Auxiliary coarse blocks occur only in the proof. Executable transport uses the sample's cached chart summary and the
retained fine integral data. -/
theorem prepared_area_bound (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    (integrals : request.prepared.request.Acquisition polynomials originals bank coefficients request.arcs.depth)
    {pairs : Acquisition.ChildPairs integrals} (weighted : ChildPairs.Weighted pairs) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.area - sample.connection.summary.area) ≤
      (4 * allowance)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  let comparison := request.prepared.request.comparison
  let coarse := comparison.acquire polynomials originals bank coefficients request.arcs.depth
    (request.prepared.request.comparison_le.trans (request.prepared_le.trans later))
  have integralBound := request.prepared.bounded integrals weighted
  have refinementBound := request.refinement.acquisition_later coarse integrals.area request.refinement_le
    integrals.minimum_le
  have chartBound := request.charts.acquisition_bounded sample.paths coarse
  have chartPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct request.chart_positive.le request.chart_le 2)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (PreparedObservationCoercivity.coefficientNormSq coefficients))
  have small : comparison.tolerance ≤ 1 := by rw [comparison.tolerance_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have connectorBound := request.connectors.area_bounded sample.paths sample.connectors coarse.blocks small
  rw [(Paths.joinedSummary 0 sample.paths sample.connectors).area_eq, ← sample.connection.summary.area_eq]
    at connectorBound
  have reversed : Data.Gaussian.Norm.Basic.normSq (sample.paths.chartSummary.area -
    sample.connection.summary.area) ≤
      allowance^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
    rw [show sample.paths.chartSummary.area - sample.connection.summary.area =
      -(sample.connection.summary.area - sample.paths.chartSummary.area) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact connectorBound
  exact
    (four_steps
    weighted.integral.area integrals.area.pullback.area coarse.pullback.area sample.paths.chartSummary.area
    sample.connection.summary.area (allowance^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2)
    integralBound refinementBound (chartBound.trans chartPaid) reversed).trans_eq (by ring1)

/-- Refining the retained original common primitive blocks preserves their exact pullback total. -/
private theorem pullback_total_later {areaAllowance : InverseRootPolynomial.Coordinate} {coarse depth : Nat}
    {comparison : CommonPrimitiveRequest regular common areaAllowance floor}
    (before : comparison.Acquisition polynomials originals bank coefficients coarse)
    (after : comparison.Acquisition polynomials originals bank coefficients depth) (later : coarse ≤ depth) :
    after.pullback.total = before.pullback.total := by
  obtain ⟨fine, equal⟩ : ∃ fine, depth = coarse + fine :=
    ⟨depth - coarse, (Nat.Subtraction.add_sub_of_le later).symm⟩
  subst depth
  have same := Blocks.pullback_refinement_total before.blocks after.blocks
  rw [after.blocks.pullbackSummary.total_eq, before.blocks.pullbackSummary.total_eq,
    ← after.pullback.total_eq, ← before.pullback.total_eq] at same
  exact same

/-- The actual weighted child-integral total approximates the cached connected chart total.

The bound retains the original coefficient norm and combines prepared, refinement, chart and connector comparisons on
the same primitive banks. -/
theorem prepared_total_bound (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    (integrals : request.prepared.request.Acquisition polynomials originals bank coefficients request.arcs.depth)
    {pairs : Acquisition.ChildPairs integrals} (weighted : ChildPairs.Weighted pairs) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.total - sample.connection.summary.total) ≤
      (4 * allowance)^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let comparison := request.prepared.request.comparison
  let coarse := comparison.acquire polynomials originals bank coefficients request.arcs.depth
    (request.prepared.request.comparison_le.trans (request.prepared_le.trans later))
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have integralBound := BasisPreparedAreaRequest.total_bounded request.prepared integrals weighted
  have refinementBound : Data.Gaussian.Norm.Basic.normSq (integrals.area.pullback.total -
    coarse.pullback.total) ≤
      allowance^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw
      [pullback_total_later
      coarse integrals.area integrals.minimum_le, Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) normNonnegative
  have chartBound := BasisCommonChartBudget.acquisition_total_bounded request.charts sample.paths coarse
  have chartPaid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct request.chart_positive.le request.chart_le 2) normNonnegative
  have connectorBound := request.connectors.total_bounded sample.paths sample.connectors
  rw [(Paths.joinedSummary 0 sample.paths sample.connectors).total_eq, ← sample.connection.summary.total_eq]
    at connectorBound
  have reversed : Data.Gaussian.Norm.Basic.normSq (sample.paths.chartSummary.total -
    sample.connection.summary.total) ≤
      allowance^2 * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show sample.paths.chartSummary.total - sample.connection.summary.total =
      -(sample.connection.summary.total - sample.paths.chartSummary.total) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
    exact connectorBound
  exact
    (four_steps
    weighted.integral.total integrals.area.pullback.total coarse.pullback.total sample.paths.chartSummary.total
    sample.connection.summary.total (allowance^2 * PreparedObservationCoercivity.coefficientNormSq coefficients)
    integralBound refinementBound (chartBound.trans chartPaid) reversed).trans_eq (by ring1)

set_option genInjectivity false in
/-- The actual prepared child integrals compared with one cached connected parent trace.

Weighted increments and both signed area and total discrepancies are cached with exact readbacks and their distinct
homogeneous bounds. -/
structure PreparedComparison (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth) where
  /-- The actual prepared child integrals acquired on the original polynomial and primitive banks. -/ integrals :
    request.prepared.request.Acquisition polynomials originals bank coefficients request.arcs.depth
  /-- The retained source/integral child pairs of that exact acquisition. -/ pairs : Acquisition.ChildPairs integrals
  /-- The cached coefficient-weighted pair list and its two summaries. -/ weighted : ChildPairs.Weighted pairs
  /-- The cached signed prepared-integral area minus the connected chart area. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The cached area discrepancy uses the exact retained integral and chart summaries. -/ difference_eq : difference =
    weighted.integral.area - sample.connection.summary.area
  /-- The area discrepancy satisfies its retained squared-coefficient-norm bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq difference ≤ (4 * allowance)^2 *
    (PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  /-- The cached signed prepared-integral total minus the connected chart total. -/ totalDifference :
    InverseRootPolynomial.Gaussian
  /-- The cached total discrepancy uses the exact retained integral and chart totals. -/ totalDifference_eq :
    totalDifference = weighted.integral.total - sample.connection.summary.total
  /-- The total discrepancy satisfies its retained coefficient-norm bound. -/ total_bounded :
    Data.Gaussian.Norm.Basic.normSq totalDifference ≤ (4 * allowance)^2 *
    PreparedObservationCoercivity.coefficientNormSq coefficients

constructive_injectivity PreparedComparison

/-- Prepare child integrals from the already materialized source primitives, then retain their weighted values, summary
and complete chart area/total errors. -/
@[expose] def comparePrepared (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (later : request.index ≤ index) :
      PreparedComparison
      sample :=
  let integrals := request.prepared.request.acquire proper polynomials originals bank coefficients request.arcs.depth
    (request.prepared_le.trans later)
  let pairs := Acquisition.childPairs integrals
  let weighted := ChildPairs.weighted pairs
  ⟨integrals, pairs, weighted, weighted.integral.area - sample.connection.summary.area, rfl,

      prepared_area_bound
      sample integrals weighted later, weighted.integral.total - sample.connection.summary.total, rfl,

      prepared_total_bound
      sample integrals weighted later⟩

end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
