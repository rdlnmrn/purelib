module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Extreme source/direct values read from the complete retained endpoint spine. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints (BasisEndpointRequests BasisEndpointPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans (Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Riemann.RootContinuation
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary (chartFirstRoot chartLastRoot)

variable {covers : BasisSourceCovers parent}
  {sourceTarget : Coordinate} {sourceFloor : Nat}
  {numerical : BasisSourceLocations.SampleBank
    covers index}

/-- Three homogeneous comparisons needed for restoration and incoming joins. -/
structure EndpointEstimate (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (target :
  InverseRootPolynomial.Coordinate)
    (chart : InverseRootPolynomial.Gaussian) (values : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)
      : Prop where
  /-- The actual retained source and direct endpoint values satisfy the homogeneous four-times source tolerance bound.
  -/
  source_close : Data.Gaussian.Norm.Basic.normSq (values.1 - values.2) ≤ 4 * target *
    PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The actual retained source and chart endpoint values satisfy the homogeneous ten-times source tolerance bound. -/
    chart_close : Data.Gaussian.Norm.Basic.normSq (values.1 - chart) ≤ 10 * target *
    PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The actual retained direct and chart endpoint values satisfy the original homogeneous source tolerance bound. -/
    direct_close : Data.Gaussian.Norm.Basic.normSq (values.2 - chart) ≤ target *
    PreparedObservationCoercivity.coefficientNormSq coefficients

namespace Samples

/-- Read the actual coefficient-weighted source and direct values at the original first retained endpoint, returning
zeros for an empty bank. -/
@[expose] def firstValues (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) → (planned :
      ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    BasisEndpointPlans.Samples numerical plans cells evaluated sources planned → InverseRootPolynomial.Gaussian ×
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _, _, _ => (0, 0)
  | _, _, _, _, .cons _ _, .cons _ _, _, _, _, endpoints =>
      let combined := endpoints.1.first.evaluated.combine coefficients
      (combined.sourceValue, combined.directValue)

/-- Read the actual coefficient-weighted source and direct values at the original last retained endpoint, returning
zeros for an empty bank. -/
@[expose] def lastValues (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) → (planned :
      ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    BasisEndpointPlans.Samples numerical plans cells evaluated sources planned → InverseRootPolynomial.Gaussian ×
      InverseRootPolynomial.Gaussian
  | _, _, _, _, .nil, .nil, _, _, _, _ => (0, 0)
  | _, _, _, _, .cons _ .nil, .cons _ .nil, _, _, _, endpoints =>
      let combined := endpoints.1.last.evaluated.combine coefficients
      (combined.sourceValue, combined.directValue)
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated, sources, planned, endpoints =>
      lastValues coefficients
        (.cons next tail) (.cons nextCell cells) evaluated.2 sources.2 planned.2 endpoints.2

/-- The original empty endpoint bank satisfies all homogeneous bounds because the retained primitive values vanish at
zero. -/
private theorem zero_estimate (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonnegative : 0 ≤ sourceTarget) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
      (polynomials.value coefficients 0) (0, 0) := by
  have valueZero : polynomials.value coefficients 0 = 0 := by
    unfold CapBasisEnergy.RegularBasisPolynomials.value
    exact (FiniteSum.Fin.sumFin_congr (fun row => by
      rw [(polynomials.get row).primitive_zero, Data.Gaussian.Basic.mul_zero])).trans FiniteSum.Fin.sumFin_zero
  have coefficientNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have bound : Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) ≤ sourceTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative
  have four : Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) ≤ 4 * sourceTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      nonnegative) coefficientNonnegative
  have ten : Data.Gaussian.Norm.Basic.normSq ((0 : InverseRootPolynomial.Gaussian) - 0) ≤ 10 * sourceTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      nonnegative) coefficientNonnegative
  rw [valueZero]
  exact ⟨four, ten, bound⟩

/-- The actual first retained endpoint values satisfy all three original homogeneous source, direct and chart
comparisons. -/
theorem first_estimate (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonnegative : 0 ≤
  sourceTarget) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) → (planned :
      ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    (endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
      (polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated))
      (firstValues coefficients plans
        cells evaluated sources planned endpoints)
  | _, _, _, _, .nil, .nil, _, _, _, _ =>
    zero_estimate polynomials coefficients
    nonnegative
  | _, _, _, _, .cons _ _, .cons _ _, _, _, _, endpoints =>
      let combined := endpoints.1.first.evaluated.combine coefficients
      ⟨combined.source_close, combined.chart_close, combined.direct_close⟩

/-- The actual last retained endpoint values satisfy all three original homogeneous source, direct and chart
comparisons. -/
theorem last_estimate (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonnegative : 0 ≤
  sourceTarget) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) → (planned :
      ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) →
    (endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
      (polynomials.value coefficients (ParentBasisBoundary.chartLastRoot plans cells evaluated))
      (lastValues coefficients plans cells
        evaluated sources planned endpoints)
  | _, _, _, _, .nil, .nil, _, _, _, _ =>
    zero_estimate polynomials coefficients
    nonnegative
  | _, _, _, _, .cons _ .nil, .cons _ .nil, _, _, _, endpoints =>
      let combined := endpoints.1.last.evaluated.combine coefficients
      ⟨combined.source_close, combined.chart_close, combined.direct_close⟩
  | _, _, _, _, .cons _ (.cons next tail), .cons _ (.cons nextCell cells), evaluated, sources, planned, endpoints =>
      last_estimate coefficients
        nonnegative (.cons next tail) (.cons nextCell cells) evaluated.2 sources.2 planned.2 endpoints.2

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {sources : BasisEndpointRequests covers
    sourceTarget sourceFloor requests} {planned :
    BasisEndpointPlans polynomials plans
    sources}

set_option genInjectivity false in
/-- The cached actual source and direct values at both extremes of the original endpoint spine.

Exact readback equalities and all three homogeneous comparisons are retained for both endpoints. -/
structure Extremes (endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached original first source and direct endpoint values. -/ first : InverseRootPolynomial.Gaussian ×
    InverseRootPolynomial.Gaussian
  /-- The first cache reads exactly the original retained endpoint spine. -/ first_eq : first =
    firstValues coefficients plans cells
    evaluated sources planned endpoints
  /-- The cached original last source and direct endpoint values. -/ last : InverseRootPolynomial.Gaussian ×
    InverseRootPolynomial.Gaussian
  /-- The last cache reads exactly the original retained endpoint spine. -/ last_eq : last =
    lastValues coefficients plans cells
    evaluated sources planned endpoints
  /-- The original first endpoint cache satisfies the retained homogeneous comparisons. -/ first_bounded :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
    (polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated)) first
  /-- The original last endpoint cache satisfies the retained homogeneous comparisons. -/ last_bounded :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
    (polynomials.value coefficients (ParentBasisBoundary.chartLastRoot plans cells evaluated)) last

constructive_injectivity Extremes

/-- Cache both actual original endpoint pairs once and retain their homogeneous source, direct and chart bounds. -/
@[expose] def extremes (endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (nonnegative : 0 ≤ sourceTarget) :
      Extremes endpoints coefficients :=
  ⟨firstValues coefficients plans cells evaluated sources planned endpoints, rfl,
    lastValues coefficients plans cells
      evaluated sources planned endpoints, rfl,
    first_estimate coefficients
      nonnegative plans cells evaluated sources planned endpoints,
    last_estimate coefficients nonnegative
      plans cells evaluated sources planned endpoints⟩

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
