module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.Mesh.BasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.Mesh.BasisEndpoints.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Paid source polygons from the acquired shared parent vertex spine. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints (BasisEndpointRequests BasisEndpointPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans (Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation (BasisSourceBudgets)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk (ParentBasisSourcePreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest (BasisSourceAllowance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

universe u

variable {evaluated : Evaluation charts
  original stage}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Data.Rat.Fraction.Compatibility

variable {covers : BasisSourceCovers parent}
  {sourceTarget : Coordinate} {sourceFloor : Nat}
  {sources : BasisEndpoints request.mesh
    covers sourceTarget sourceFloor}
  {basisPlan : BasisEndpoints.Plan
    sources charts polynomials}
  {numerical : BasisSourceLocations.SampleBank
    covers index}

set_option genInjectivity false in
/-- Both polygons and their signed discrepancy are cached on the acquired cell. The source summary is inherited from the
retained vertex combinations. -/
structure SourcePolygon (evaluated : AreaRequest.Evaluation charts original stage)
    (endpoints : Plan.Evaluation basisPlan numerical evaluated.vertices)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (allowance : InverseRootPolynomial.Coordinate)
      where
  /-- The actual cached source and chart vertex combinations on the original retained cell. -/ values : Basis.PathValues
    endpoints coefficients
  /-- The cached original chart polygon summary on those same paired vertex values. -/ chart : IncrementArea.Summary
    (values.values.pairs.map Prod.snd)
  /-- The cached signed area discrepancy between the actual original source and chart polygons. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The discrepancy cache is exactly the source summary area minus the retained chart summary area. -/ difference_eq :
    difference = values.values.source.area - chart.area
  /-- The original fitted cell allowance pays the actual polygon discrepancy with its retained homogeneous coefficient
    factor. -/ bounded : Data.Gaussian.Norm.Basic.normSq difference ≤ (4 * allowance)^2 *
    (PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity SourcePolygon

/-- Acquire the source combinations once and pay their full polygon error using the preselected cell allowance and
common parent tolerance. -/
def sourcePolygon (evaluated : AreaRequest.Evaluation charts original stage)
    (endpoints : Plan.Evaluation basisPlan numerical evaluated.vertices)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    {endpointTarget allowance : InverseRootPolynomial.Coordinate} (allocation : AreaRequest.BasisSourceAllowance request
      endpointTarget allowance)
    (nonnegative : 0 ≤ sourceTarget) (fitted : sourceTarget ≤ allocation.sourceTarget) :
    SourcePolygon evaluated
      endpoints coefficients allowance := by
  let values := Evaluation.pathValues endpoints coefficients
  let chart := IncrementArea.Summary.build (values.values.pairs.map Prod.snd)
  let difference := values.values.source.area - chart.area
  have bound := BasisPathValues.area_bound values.values nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.basisBounds.coefficient_nonnegative)
    (fun segment member => Evaluation.basis_increment_bound evaluated coefficients branch segment member)
  have countEq : evaluated.vertices.path.segments.length = request.count :=
    evaluated.vertices.path.count_eq.trans request.count_eq.symm
  rw [countEq] at bound
  have paid := bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (allocation.paid_of_le nonnegative fitted) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  refine ⟨values, chart, difference, rfl, ?_⟩
  change Data.Gaussian.Norm.Basic.normSq (values.values.source.area - chart.area) ≤ _
  rw [chart.area_eq, values.values.chart_eq]
  exact paid

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints (BasisEndpointRequests BasisEndpointPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints.BasisEndpointPlans (Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePreparation (BasisSourceBudgets)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk (ParentBasisSourcePreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest (BasisSourceAllowance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

variable {target sourceTarget : Coordinate} {floor sourceFloor :
  Nat}

variable {covers : BasisSourceCovers parent}
  {index minimum depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {endpointTarget allowance : Coordinate}

namespace BasisEndpointPlans

/-- Paid source polygons in the exact heterogeneous parent cell order. -/
def SourcePolygons (numerical : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (allowance : InverseRootPolynomial.Coordinate) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → BasisEndpointPlans.Samples numerical
      plans cells evaluated sources planned → Type 2
  | _, _, _, _, .nil, .nil, _, _, _, _ => PUnit
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation.SourcePolygon
        evaluated.1 endpoints.1 coefficients allowance ×
        SourcePolygons
          numerical coefficients allowance tail cells evaluated.2 sources.2 planned.2 endpoints.2

/-- Evaluate every original coefficient-weighted cell polygon on the cached common endpoint acquisition and retain its
fitted allowance certificate. -/
def sourcePolygons (numerical : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (branch : HyperellipticReciprocal.originOrder
      curve = 1)
    (nonnegative : 0 ≤ sourceTarget) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (budgets : ParentBasisSourcePreparation.BasisSourceBudgets endpointTarget allowance requests) → budgets.Fits
      sourceTarget requests →
    SourcePolygons numerical
      coefficients allowance plans cells evaluated sources planned endpoints
  | _, _, _, _, .nil, .nil, _, _, _, _, _, _ => ⟨⟩
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, budgets, fitted =>
      ⟨Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation.sourcePolygon
        evaluated.1 endpoints.1 coefficients branch budgets.1 nonnegative fitted.1,
        sourcePolygons
          numerical coefficients branch nonnegative tail cells evaluated.2 sources.2 planned.2 endpoints.2 budgets.2
          fitted.2⟩

end BasisEndpointPlans
namespace ParentBasisSourcePreparation

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}

set_option genInjectivity false in
/-- Keep the selected basis plans with the one shared root acquisition. -/
structure Acquisition (prepared : ParentBasisSourcePreparation covers endpointTarget
  allowance sourceFloor requests)
    (numerical : BasisSourceLocations.SampleBank covers index) (plans : ParentChartRequests.ChartPlans capSample minimum
      requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (polynomials :
      CapBasisEnergy.RegularBasisPolynomials cap index box) (readingFloor : Nat) where
  /-- The original complete basis endpoint plans on the exact retained chart and source requests. -/ planned :
    ParentBasisEndpoints.BasisEndpointPlans polynomials plans prepared.sources
  /-- The single shared original root acquisition with all retained basis endpoint transports. -/ acquired :
    BasisEndpointPlans.Acquisition numerical plans cells prepared.sources planned readingFloor

constructive_injectivity Acquisition

/-- Prepare the original basis endpoint plans and acquire one shared root bank at the paid model, source, spatial and
reading floors. -/
def acquire (prepared : ParentBasisSourcePreparation covers endpointTarget allowance
  sourceFloor requests)
    (numerical : BasisSourceLocations.SampleBank covers index) (plans : ParentChartRequests.ChartPlans capSample minimum
      requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (polynomials :
      CapBasisEnergy.RegularBasisPolynomials cap index box) (readingFloor : Nat)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : requests.maximum ≤ index) (sourceLater : prepared.sources.maximum requests ≤ index)
    (spatial : requests.depthMaximum ≤ depth) :
      Acquisition
      prepared numerical plans cells polynomials readingFloor :=
  let planned := BasisEndpointPlans.build polynomials plans prepared.sources
  ⟨planned, BasisEndpointPlans.acquire numerical plans cells prepared.sources planned readingFloor branch modelLater
    sourceLater spatial⟩

/-- Consume the cached acquisition and its preparation's fitted budgets. Only the coefficient combinations are evaluated
at this stage. -/
def Acquisition.polygons
    {prepared : ParentBasisSourcePreparation covers endpointTarget allowance sourceFloor
      requests}
    {numerical : BasisSourceLocations.SampleBank covers index} {plans : ParentChartRequests.ChartPlans capSample minimum
      requests}
    {cells : ParentPaths.ComparedCells source capSample depth bank} {readingFloor : Nat}
    (acquisition :
      Acquisition
      prepared numerical plans cells polynomials readingFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (branch : HyperellipticReciprocal.originOrder
      curve = 1) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.BasisEndpointPlans.SourcePolygons numerical
      coefficients allowance plans cells acquisition.acquired.original
      prepared.sources acquisition.planned acquisition.acquired.endpoints :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.BasisEndpointPlans.sourcePolygons numerical
    coefficients branch prepared.positive.le plans cells acquisition.acquired.original
    prepared.sources acquisition.planned acquisition.acquired.endpoints prepared.budgets prepared.fitted

end ParentBasisSourcePreparation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.ParentBasisSourcePreparation

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.ParentBasisSourcePreparation

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation
namespace SourcePolygon

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation.SourcePolygon
