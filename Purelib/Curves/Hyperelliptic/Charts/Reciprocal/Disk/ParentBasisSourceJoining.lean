module
import Purelib.Data.List.Membership
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceTotals
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceTotals.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Compare the complete coarse polygons of the retained source/chart cells. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining

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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourcePolygons.BasisEndpointPlans (SourcePolygons)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceTotals.AreaRequest.Evaluation.SourcePolygon
  (total_error chart_total_bound source_total_bound)
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

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

namespace BasisEndpointPlans.SourcePolygons

variable {numerical :
  BasisSourceLocations.SampleBank covers
  index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Uniform coefficient ceiling selected from the retained requests. -/
def basisMaximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {owners : ParentOwners.Owners bank} →
    ParentChartRequests.ChartRequests target floor owners → InverseRootPolynomial.Coordinate
  | _, _, _, .nil => 0
  | _, _, _, .cons head tail => max head.basisBounds.coefficient
    (basisMaximum
    tail)

/-- The maximum of the retained basis magnitude coefficients is nonnegative. -/
theorem basisMaximum_nonnegative : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank :
  ParentBank.Bank regular data edges} → {owners : ParentOwners.Owners bank} →
    (requests : ParentChartRequests.ChartRequests target floor owners) → 0 ≤
      basisMaximum
      requests
  | _, _, _, .nil => le_rfl
  | _, _, _, .cons head _ => head.basisBounds.coefficient_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The actual source and chart cell totals paired in the original parent order. -/
def totals : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data
  edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned endpoints →
      List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      (polygons.1.values.values.source.total, polygons.1.chart.total) ::

          totals
          tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2

/-- The retained total-pair list has one entry per original parent edge. -/
theorem totals_count : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {owners : ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints) →
    (totals plans
      cells evaluated sources planned endpoints polygons).length = edges.length
  | _, _, _, _, .nil, .nil, _, _, _, _, _ => rfl
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons =>
      congrArg Nat.succ
        (totals_count
        tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2)

/-- The finite squared coefficient norm is nonnegative. -/
public theorem norm_nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- The finite squared coefficient norm is nonnegative. -/
theorem norm_nonnegative_for_joining : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- Each retained cell-total pair obeys the original endpoint discrepancy and common magnitude ceiling.

Both source and chart bounds retain the same homogeneous coefficient factor and require a simple reciprocal origin. -/
theorem totals_bounded (branch : HyperellipticReciprocal.originOrder curve = 1)
    (nonnegative : 0 ≤ sourceTarget) (ceiling : InverseRootPolynomial.Coordinate) : {edges : List
      ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} → {owners :
      ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans : ParentChartRequests.ChartPlans
      capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated : ChartPlans.EvaluationData
      readingIndex plans cells) →
    (sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests) →
    (planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources) → (endpoints :
      BasisEndpointPlans.Samples numerical plans cells evaluated sources planned) →
    (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated sources planned
      endpoints) →
    basisMaximum
      requests ≤ ceiling → ∀ pair ∈
      totals
      plans cells evaluated sources planned endpoints polygons,
      Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ 40 * sourceTarget *
        PreparedObservationCoercivity.coefficientNormSq coefficients ∧
      Data.Gaussian.Norm.Basic.normSq pair.1 ≤ (80 * sourceTarget + 32 * ceiling) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ∧
      Data.Gaussian.Norm.Basic.normSq pair.2 ≤ (80 * sourceTarget + 32 * ceiling) *
        PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, _, _, _, .nil, .nil, _, _, _, _, _, _, _, member => by cases member
  | _, _, _, _, .cons (head := request) _ tail, .cons _ cells, evaluated, sources, planned, endpoints, polygons,
    bounded, pair, member =>
    by
      rcases List.Membership.mem_cons.mp member with equal | later
      · subst pair
        have coefficientLe := (Fraction.Order.Basic.le_max_left _ _).trans bounded
        have commonLe := Fraction.Order.Arithmetic.add_le_add_direct (le_refl (80 * sourceTarget))
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientLe (by
              decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32))
        have sourceBound := (SourcePolygon.source_total_bound polygons.1 branch).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct commonLe
            norm_nonnegative)
        have extra : 0 ≤ 80 * sourceTarget + 16 * request.basisBounds.coefficient :=
          add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative)
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
              request.basisBounds.coefficient_nonnegative)
        have chartLe : 16 * request.basisBounds.coefficient ≤ 80 * sourceTarget + 32 * ceiling := by
          have le := Fraction.Order.Arithmetic.add_le_add_direct (le_refl (16 * request.basisBounds.coefficient)) extra
          exact (show 16 * request.basisBounds.coefficient = 16 * request.basisBounds.coefficient + 0 by ring1).trans_le
            ((le.trans_eq (by ring1)).trans commonLe)
        exact ⟨total_error polygons.1, sourceBound,
          (SourcePolygon.chart_total_bound polygons.1 branch).trans
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartLe
            norm_nonnegative)⟩
      · exact
          totals_bounded
          branch nonnegative ceiling tail cells evaluated.2 sources.2 planned.2 endpoints.2 polygons.2
          ((Fraction.Order.Basic.le_max_right _ _).trans bounded) pair later

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
    sourceTarget sourceFloor requests}
  {planned : BasisEndpointPlans polynomials
    plans sources} {endpoints :
    Samples numerical plans
    cells evaluated sources planned}

set_option genInjectivity false in
/-- The complete joining-polygon comparison formed from the retained source and chart cell totals.

Both coarse polygon summaries are cached with every cross term, and their actual area difference carries the original
homogeneous count and magnitude bound. -/
structure JoiningComparison (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells
  evaluated sources planned endpoints) where
  /-- The cached source/chart total pairs in original parent order. -/ pairs : List (InverseRootPolynomial.Gaussian ×
    InverseRootPolynomial.Gaussian)
  /-- The retained pairs are exactly the original cell-total pairs. -/ pairs_eq : pairs =
    totals plans
    cells evaluated sources planned endpoints polygons
  /-- The complete cached joining-polygon summary of the actual source totals. -/ source : IncrementArea.Summary
    (pairs.map Prod.fst)
  /-- The complete cached joining-polygon summary of the actual chart totals. -/ chart : IncrementArea.Summary
    (pairs.map Prod.snd)
  /-- The cached signed area discrepancy between the two retained joining polygons. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The retained difference is the source joining area minus the chart joining area. -/ difference_eq : difference =
    source.area - chart.area
  /-- The cached joining discrepancy satisfies the original fourth-power count and homogeneous magnitude bound. -/
    bounded : Data.Gaussian.Norm.Basic.normSq difference ≤ 640 * (edges.length :
    InverseRootPolynomial.Coordinate)^4 * sourceTarget *
    (80 * sourceTarget + 32 *
      basisMaximum
      requests) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity JoiningComparison

/-- Preserve the full coarse polygon of cell totals, including every cross term. -/
def compareJoining (polygons : BasisEndpointPlans.SourcePolygons numerical coefficients allowance plans cells evaluated
  sources planned endpoints)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonnegative : 0 ≤ sourceTarget) :
      JoiningComparison
      polygons := by
  let pairs :=
    totals plans
    cells evaluated sources planned endpoints polygons
  let source := IncrementArea.Summary.build (pairs.map Prod.fst)
  let chart := IncrementArea.Summary.build (pairs.map Prod.snd)
  have each :=
    totals_bounded
    branch nonnegative
    (basisMaximum
    requests) plans cells evaluated sources planned endpoints polygons le_rfl
  have bound := IncrementAreaComparison.pathArea_difference_bound pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      nonnegative)
      norm_nonnegative_for_joining)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide +kernel) nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (basisMaximum_nonnegative
        requests)))
        norm_nonnegative_for_joining)
    (fun pair member => (each pair member).1) (fun pair member => (each pair member).2.1) (fun pair member => (each pair
      member).2.2)
  have countEq : pairs.length = edges.length :=
    totals_count
    plans cells evaluated sources planned endpoints polygons
  rw [countEq, ← source.area_eq, ← chart.area_eq] at bound
  exact ⟨pairs, rfl, source, chart, source.area - chart.area, rfl, bound.trans_eq (by ring1)⟩

end BasisEndpointPlans.SourcePolygons
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceJoining
