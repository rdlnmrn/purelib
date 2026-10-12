module
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
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Complete cell increments for the source/chart joining-polygon comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceTotals

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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.AreaRequest.Evaluation
  (SourcePolygon)
open Purelib.Riemann.RootContinuation
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

namespace AreaRequest.Evaluation

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

namespace SourcePolygon

variable {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {allowance :
  Coordinate}
  {endpoints :
    BasisEndpoints.Plan.Evaluation
    basisPlan numerical evaluated.vertices}

/-- The complete original chart polygon increment is the last retained polynomial value minus the first. -/
theorem chart_total (polygon : Evaluation.SourcePolygon evaluated endpoints coefficients allowance) :
    polygon.chart.total = polynomials.value coefficients evaluated.vertices.last.root.coordinate -
      polynomials.value coefficients evaluated.vertices.first.root.coordinate := by
  rw [polygon.chart.total_eq, polygon.values.values.chart_eq]
  exact Segment.value_total (polynomials.value coefficients) _ evaluated.vertices.path.chain

/-- Endpoint estimates control the complete cell increment without an internal vertex-count factor. Source primitive
origins remain explicit in the values. -/
theorem total_error (polygon : Evaluation.SourcePolygon evaluated endpoints coefficients allowance) :
    Data.Gaussian.Norm.Basic.normSq (polygon.values.values.source.total - polygon.chart.total) ≤
      40 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have first := endpoints.first.evaluated.accurate coefficients
  have last := endpoints.last.evaluated.accurate coefficients
  rw [← polygon.values.first_eq] at first
  rw [← polygon.values.last_eq] at last
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    (polygon.values.lastSource - polynomials.value coefficients evaluated.vertices.last.root.coordinate)
    (polygon.values.firstSource - polynomials.value coefficients evaluated.vertices.first.root.coordinate)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct last
        first) (by decide))
  rw [polygon.values.values.source_total,
    chart_total
    polygon]
  rw [show (polygon.values.lastSource - polygon.values.firstSource) -
      (polynomials.value coefficients evaluated.vertices.last.root.coordinate -
        polynomials.value coefficients evaluated.vertices.first.root.coordinate) =
      (polygon.values.lastSource - polynomials.value coefficients evaluated.vertices.last.root.coordinate) -
        (polygon.values.firstSource - polynomials.value coefficients evaluated.vertices.first.root.coordinate) by ring1]
  exact bound.trans_eq (by ring1)

/-- At a simple reciprocal origin, the original complete chart increment obeys the retained basis bound and homogeneous
coefficient factor. -/
theorem chart_total_bound (polygon : Evaluation.SourcePolygon evaluated endpoints coefficients allowance)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq polygon.chart.total ≤ 16 * request.basisBounds.coefficient *
      PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have firstInside := Evaluation.square_inside request branch evaluated.vertices.first
  have lastInside := Evaluation.square_inside request branch evaluated.vertices.last
  have firstRoot := regular.padded.root_norm_le firstInside
  have lastRoot := regular.padded.root_norm_le lastInside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstRoot lastRoot
  have step : Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.last.root.coordinate -
    evaluated.vertices.first.root.coordinate) ≤ 8 := by
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two evaluated.vertices.last.root.coordinate
      evaluated.vertices.first.root.coordinate).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct lastRoot
        firstRoot) (by decide)).trans_eq (by ring1))
  have bound := BasisBounds.chord_increment request.basisBounds polynomials coefficients branch firstInside lastInside
    (left := 0) (right := 1) (by decide) (by decide)
  have atZero : RootRadialGeometry.chord evaluated.vertices.first.root.coordinate
    evaluated.vertices.last.root.coordinate 0 =
      evaluated.vertices.first.root.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
  have atOne : RootRadialGeometry.chord evaluated.vertices.first.root.coordinate evaluated.vertices.last.root.coordinate
    1 =
      evaluated.vertices.last.root.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
  rw [atZero, atOne, show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct]
    at bound
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct step
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      request.basisBounds.coefficient_nonnegative)
  rw [chart_total
    polygon]
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scaled normNonnegative).trans_eq (by
    ring1))

/-- The actual original complete source increment is bounded by the retained endpoint error allowance and basis
magnitude coefficient. -/
theorem source_total_bound (polygon : Evaluation.SourcePolygon evaluated endpoints coefficients allowance)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq polygon.values.values.source.total ≤
      (80 * sourceTarget + 32 * request.basisBounds.coefficient) * PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (polygon.values.values.source.total - polygon.chart.total)
    polygon.chart.total).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (total_error
      polygon)
      (chart_total_bound
      polygon branch)) (by decide))
  rw [show polygon.values.values.source.total - polygon.chart.total + polygon.chart.total =
    polygon.values.values.source.total by ring1] at bound
  exact bound.trans_eq (by ring1)

end SourcePolygon
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceTotals
