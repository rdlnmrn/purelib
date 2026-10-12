module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.UniformPreparedRequests

public section

/-! Reuse the common-parent prepared requests on the scheduled row bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples (PreparedComparisons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest (BasisPreparedAreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Samples

/-- Each retained first-parent basis source model has exactly the original genus count. -/
theorem head_count {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (sources : SourceLocations.BasisParentSourceCovers (parent :: parents)) (row : Fin genus) :
    (sources.head.get row).count = genus := by
  unfold SourceLocations.BasisParentSourceCovers.head
  rw [DependentVector.ofFn_get]
  cases sources.get row
  rfl

/-- The retained prepared source tolerance is at most one. -/
theorem sourceTolerance_le_one
    {sources : SourceLocations.BasisSourceCovers parent} {cover : UniformReciprocalCover.Cover data} {commonMinimum :
      Nat}
    {common : CommonCover.BasisCommonCover cover sources commonMinimum}
    (budget : PreparedAreaRequest.BasisPreparedAreaRequest regular common allowance coefficientTarget floor) :
    budget.request.sourceTolerance ≤ 1 := by
  rw [budget.request.sourceTolerance_eq]
  apply (Aggregate.perTerm_le budget.request.source_positive.le genus).trans
  rw [budget.sourceTarget_eq]
  exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _

/-- Extract the retained row requests from the acquired common-parent bank. Only their tolerance indices are enlarged;
polynomial and child data are reused. -/
@[expose] def scheduledRowRequests : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples →
    (row : Fin genus) → UniformPreparedRequests.RequestedParents genus 1
      (parents.map (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row)))
  | _, .nil, _, _, _, _, _, _, _, _, _ => .nil
  | parent :: _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, row =>
      let head := (comparisons.1.integrals.prepared.get row).localRequest.weaken
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.sourceTolerance_le_one
          bank.1.request.prepared)
      .cons (Eq.mp (congrArg (fun count => UniformPreparedRequests.LocalRequest
        (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row) parent) count 1)
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.head_count sources row)) head)
        (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests tail
          sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 row)

/-- Transporting a retained request's finite count preserves its actual coefficient bound. -/
theorem coefficient_cast {source : Differentials.Basic.Differential genus} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source}
    {first second : Nat} {target : InverseRootPolynomial.Coordinate} (equal : first = second)
    (request : UniformPreparedRequests.LocalRequest parent first target) :
    PreparedPrimitiveChargeBounds.localCoefficient
      (Eq.mp (congrArg (fun count => UniformPreparedRequests.LocalRequest parent count target) equal) request) =
      PreparedPrimitiveChargeBounds.localCoefficient request := by
  cases equal
  rfl

/-- The preselected coefficient-error ceiling survives extraction and weakening, so the scheduled comparison can use the
original polynomial floor. -/
theorem scheduledRowRequests_coefficient (nonnegative : 0 ≤ coefficientTarget) :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) (row : Fin
      genus),
    PreparedPrimitiveChargeBounds.coefficientMaximum
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources
        bank plans inputs readings prepared samples comparisons row) ≤ coefficientTarget
  | _, .nil, _, _, _, _, _, _, _, _, _ => nonnegative
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, row => by
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests]
      change max (PreparedPrimitiveChargeBounds.localCoefficient _) (PreparedPrimitiveChargeBounds.coefficientMaximum _)
        ≤ coefficientTarget
      apply Purelib.Data.Rat.Fraction.Order.Basic.max_le
      · rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.coefficient_cast
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.head_count sources row)]
        exact (comparisons.1.integrals.prepared.get row).coefficient_accurate.le
      · exact
          scheduledRowRequests_coefficient
          nonnegative tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 row

/-- The original source-slope maximum splits into the first retained parent and its exact tail. -/
private theorem sourceSlope_cons {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (sources : SourceLocations.BasisParentSourceCovers (parent :: parents)) (row : Fin genus) :
    (ParentCovers.sourceSlopeMaximum (sources.get row)) =
      max (sources.head.get row).data.sourceSlope (ParentCovers.sourceSlopeMaximum (sources.tail.get row)) := by
  unfold SourceLocations.BasisParentSourceCovers.head SourceLocations.BasisParentSourceCovers.tail
  rw [DependentVector.ofFn_get, DependentVector.ofFn_get]
  cases sources.get row
  rfl

/-- Transporting the retained finite count preserves the original primitive slope bound. -/
private theorem slope_cast {source : Differentials.Basic.Differential genus} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source}
    {first second : Nat} {target slope : InverseRootPolynomial.Coordinate} (equal : first = second)
    (request : UniformPreparedRequests.LocalRequest parent first target)
    (bounded : PreparedDyadicPrimitiveResampling.PrimitiveSlopeBound slope
      (RequestedParents.cons request .nil)) :
    PreparedDyadicPrimitiveResampling.PrimitiveSlopeBound slope
      (RequestedParents.cons
        (Eq.mp (congrArg (fun count => UniformPreparedRequests.LocalRequest parent count target) equal) request) .nil)
          := by
  cases equal
  exact bounded

/-- The bank's slope is read from the original source covers, uniformly in all retained polynomial indices and local
prepared depths. -/
theorem scheduledRowRequests_slope :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) (row : Fin
      genus)
    {slope : InverseRootPolynomial.Coordinate}, (ParentCovers.sourceSlopeMaximum (sources.get row)) ≤ slope →
    PreparedDyadicPrimitiveResampling.PrimitiveSlopeBound slope
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources
        bank plans inputs readings prepared samples comparisons row)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, row, _, upper => by
      have split := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.sourceSlope_cons sources
        row
      have headUpper := (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _).trans (split ▸ upper)
      have tailUpper := (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _).trans (split ▸ upper)
      have retained := PreparedTraceReadback.row_slope comparisons.1.integrals row
      have weakened : PreparedDyadicPrimitiveResampling.PrimitiveSlopeBound (sources.head.get row).data.sourceSlope
          (RequestedParents.cons
            ((comparisons.1.integrals.prepared.get row).localRequest.weaken
              (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.sourceTolerance_le_one
              bank.1.request.prepared)) .nil) := retained
      have head := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.slope_cast
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.head_count sources row) _ weakened
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests]
      constructor
      · intro first last firstInside lastInside
        exact (head.1 first last firstInside lastInside).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct headUpper
            (Fraction.Order.Arithmetic.sq_nonneg_direct (last - first)))
      · exact
          Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests_slope
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 row tailUpper

/-- Transporting a retained request's finite count preserves its actual block depth. -/
theorem depth_cast {source : Differentials.Basic.Differential genus} {parent : PreparedSubdivisionModelCore.CenteredEdge
  curve source}
    {first second : Nat} {target : InverseRootPolynomial.Coordinate} (equal : first = second)
    (request : UniformPreparedRequests.LocalRequest parent first target) :
    (Eq.mp (congrArg (fun count => UniformPreparedRequests.LocalRequest parent count target) equal)
      request).request.block.depth =
      request.request.block.depth := by
  cases equal
  rfl

/-- The original cover floor controls every local prepared depth. A later scheduled depth need only exceed the computed
maximum of the retained blocks. -/
theorem scheduledRowRequests_depths :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : UniformReciprocalCover.ParentCovers parents) (sources : SourceLocations.BasisParentSourceCovers parents)
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor)
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) (inputs :
      CommonParentPlans.NumericalBank index anchors sources)
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage)
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings)
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
    (comparisons : Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples) (row : Fin
      genus)
    {upper : Nat}, PreparedDyadicPrimitiveResampling.preparedDepthMaximum
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources
        bank plans inputs readings prepared samples comparisons row) ≤ upper →
    PreparedDyadicPrimitiveResampling.PreparedDepthBounds coverFloor upper
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources
        bank plans inputs readings prepared samples comparisons row)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, row, upper, enough =>
    by
      rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests] at enough ⊢
      change max _ (PreparedDyadicPrimitiveResampling.preparedDepthMaximum _) ≤ upper at enough
      constructor
      · constructor
        · rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.depth_cast
            (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.head_count sources row)]
          change coverFloor ≤ (comparisons.1.integrals.prepared.get row).localRequest.request.block.depth
          rw [comparisons.1.integrals.depths_eq row]
          have base : coverFloor ≤ bank.1.common.depth := (Purelib.Data.Nat.Order.le_max_left _ _).trans_eq
            bank.1.common.depth_eq.symm
          exact base.trans (Nat.le_add_right _ _)
        · exact (Purelib.Data.Nat.Order.le_max_left _ _).trans enough
      · exact
          scheduledRowRequests_depths
          tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2 row
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans enough)

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
