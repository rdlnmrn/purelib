module
meta import Purelib.Elab.ConstructiveInjectivity
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartEndpointValues
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Retain the actual extreme source/direct combinations of a common parent.
Their uniform estimates come from the already paid interval requests. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues

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

namespace Paths

/-- The first original source/direct endpoint combination, or the zero pair for an empty common interval list. -/
@[expose] def firstValues : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings → Normalization.InverseRootPolynomial.Gaussian ×
      Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _ => (0, 0)
  | _, .cons _ _, _, readings, paths =>
      let combined :=
        IntervalChartEndpointValues.BasisIntervalChartRequest.Plan.Evaluation.PathData.firstCombination
        readings.1.evaluated paths.1
      (combined.sourceValue, combined.directValue)

/-- The last original source/direct endpoint combination on the retained common traversal. -/
@[expose] def lastValues : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings → Normalization.InverseRootPolynomial.Gaussian ×
      Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _ => (0, 0)
  | _, .cons _ .nil, _, readings, paths =>
      let combined :=
        IntervalChartEndpointValues.BasisIntervalChartRequest.Plan.Evaluation.PathData.lastCombination
        readings.1.evaluated paths.1
      (combined.sourceValue, combined.directValue)
  | _, .cons _ (.cons next remaining), _, _, paths =>
    lastValues (.cons next
    remaining) paths.2

/-- An original endpoint estimate remains valid when its nonnegative coefficient-weighted target is enlarged. -/
private theorem estimate_mono {firstTarget lastTarget : Normalization.InverseRootPolynomial.Coordinate} {chart :
  Normalization.InverseRootPolynomial.Gaussian} {values : Normalization.InverseRootPolynomial.Gaussian ×
  Normalization.InverseRootPolynomial.Gaussian}
    (estimate : Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients firstTarget
      chart values) (less : firstTarget ≤ lastTarget) :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients lastTarget chart values
      := open Purelib.Algebra in open Purelib.Data in open Purelib.Data.Rat in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact ⟨estimate.source_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct less (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)) normNonnegative),
    estimate.chart_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct less (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 10)) normNonnegative),
    estimate.direct_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct less normNonnegative)⟩

/-- The zero endpoint pair satisfies the original coefficient-weighted squared-target estimate. -/
private theorem zero_estimate : Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate
  coefficients (sourceTarget^2) 0 (0, 0) := open Purelib.Algebra in open Purelib.Data in open Purelib.Data.Rat in by
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have bounded : 0 ≤ sourceTarget^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) normNonnegative
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [_root_.sub_self, Gaussian.Norm.Basic.normSq_zero]
  · exact (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) bounded).trans_eq (by ring1)
  · exact (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 10) bounded).trans_eq (by ring1)
  · exact bounded

/-- The paid original interval source allocation is bounded by the common squared source target. -/
private theorem source_le {interval : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers}
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget.BasisIntervalChartBudget interval regular
      depth target sourceTarget floor sourceFloor) :
    budget.sourceTarget ≤ sourceTarget^2 :=
  open Purelib.Data.Rat in (show budget.sourceTarget = 1 * budget.sourceTarget by ring1).trans_le
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 40)
      budget.request.source_positive.le).trans budget.total_paid)

/-- The first original source/direct combination satisfies its common coefficient-weighted endpoint estimate. -/
theorem first_bounded : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients (sourceTarget^2)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.firstChartValue coefficients requests
      readings) (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.firstValues requests paths)
  | _, .nil, _, _, _ => Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.zero_estimate
  | _, .cons head _, _, readings, paths => by
      let combined :=
        IntervalChartEndpointValues.BasisIntervalChartRequest.Plan.Evaluation.PathData.firstCombination
        readings.1.evaluated paths.1
      have estimate : Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients
        head.sourceTarget
          (polynomials.value coefficients readings.1.evaluated.first.root.coordinate) (combined.sourceValue,
            combined.directValue) :=
        ⟨combined.source_close, combined.chart_close, combined.direct_close⟩
      exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.estimate_mono estimate
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.source_le head)

/-- The last original source/direct combination satisfies its common coefficient-weighted endpoint estimate. -/
theorem last_bounded : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients (sourceTarget^2)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.lastChartValue coefficients requests
      readings) (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.lastValues requests paths)
  | _, .nil, _, _, _ => Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.zero_estimate
  | _, .cons head .nil, _, readings, paths => by
      let combined :=
        IntervalChartEndpointValues.BasisIntervalChartRequest.Plan.Evaluation.PathData.lastCombination
        readings.1.evaluated paths.1
      have estimate : Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients
        head.sourceTarget
          (polynomials.value coefficients readings.1.evaluated.last.root.coordinate) (combined.sourceValue,
            combined.directValue) :=
        ⟨combined.source_close, combined.chart_close, combined.direct_close⟩
      exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.estimate_mono estimate
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.source_le head)
  | _, .cons _ (.cons next remaining), _, _, paths =>
    last_bounded (.cons next
    remaining) paths.2

variable {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
    target sourceTarget floor sourceFloor intervals}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests} {readings :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
    bank stage requests plans}

set_option genInjectivity false in
/-- Cached extreme source/direct combinations from the original common parent path.

Both pairs retain exact readbacks and their original coefficient-weighted estimates against the corresponding chart
endpoint. -/
structure Extremes (paths :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
  coefficients requests plans readings) where
  /-- The cached first original source/direct endpoint pair. -/ first : Normalization.InverseRootPolynomial.Gaussian ×
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached first pair is the original first path combination. -/ first_eq : first =
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.firstValues requests paths
  /-- The cached last original source/direct endpoint pair. -/ last : Normalization.InverseRootPolynomial.Gaussian ×
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached last pair is the original last path combination. -/ last_eq : last =
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.lastValues requests paths
  /-- The retained first pair meets the common endpoint estimate. -/ first_bounded :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients (sourceTarget^2)
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.firstChartValue coefficients requests
    readings) first
  /-- The retained last pair meets the common endpoint estimate. -/ last_bounded :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients (sourceTarget^2)
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.lastChartValue coefficients requests
    readings) last

constructive_injectivity Extremes

/-- Cache both original endpoint combinations together with their exact readbacks and paid estimates. -/
@[expose] def extremes (paths :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
  coefficients requests plans readings) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.Extremes
  paths :=
  let first := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.firstValues requests paths
  let last := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.lastValues requests paths
  ⟨first, rfl, last, rfl, Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.first_bounded requests
    paths, Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths.last_bounded requests paths⟩

end Paths
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
