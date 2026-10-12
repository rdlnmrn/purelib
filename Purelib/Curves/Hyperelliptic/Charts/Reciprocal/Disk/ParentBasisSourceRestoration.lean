module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration.BasisBoundarySample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Parent endpoint restoration from the actual cached basis source readings. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration

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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration.BasisBoundarySample
  (EndpointRestoration)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample (BasisBoundarySample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues (EndpointEstimate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues.Samples (Extremes)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundary (chartFirstRoot chartLastRoot)

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

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {requests : ChartRequests target floor owners}
    {plans : ChartPlans capSample minimum
    requests}
  {cells : ComparedCells source capSample depth bank}
    {evaluated : EvaluationData
    readingIndex plans cells}
  {energyTarget joinTarget : Coordinate} {energyFloor energyDepth :
    Nat}

namespace BasisBoundarySample

open Purelib.Integration.Path.IncrementArea (Summary traceArea)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.IncrementRestoration (potential detour)

variable {energies : BasisEnergyData
  (polynomials := polynomials) energyTarget energyFloor energyDepth plans cells evaluated}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {sample : BasisBoundarySample energies
    coefficients joinTarget}
  {endpointTarget joining : Coordinate}

variable {covers : BasisSourceCovers parent}
  {sourceTarget : Coordinate} {sourceFloor : Nat}
  {numerical : BasisSourceLocations.SampleBank
    covers index}
  {sources : BasisEndpointRequests covers
    sourceTarget sourceFloor requests}
  {planned : BasisEndpointPlans polynomials
    plans sources}
  {endpoints : Samples
    numerical plans cells evaluated sources planned}

/-- Read the extreme values of the complete acquired endpoint spine. The parent's root readbacks discharge both chart
identities, including empty paths. -/
@[expose] def EndpointRestoration.ofEndpoints
    (ends : Samples.Extremes endpoints coefficients)
    (sourcePaid : 4 * sourceTarget ≤ joining) (chartPaid : 10 * sourceTarget ≤ 4 * endpointTarget) :
    BasisBoundarySample.EndpointRestoration sample endpointTarget joining := by
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have firstSource := ends.first_bounded.source_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    sourcePaid nonnegative)
  have lastSource : Data.Gaussian.Norm.Basic.normSq (ends.last.2 - ends.last.1) ≤ joining *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show ends.last.2 - ends.last.1 = -(ends.last.1 - ends.last.2) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact ends.last_bounded.source_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourcePaid
      nonnegative)
  have firstChart : Data.Gaussian.Norm.Basic.normSq (sample.firstValue - ends.first.1) ≤ 4 * endpointTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [sample.first_value, sample.first_root,
      show polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated) - ends.first.1 =
      -(ends.first.1 - polynomials.value coefficients (ParentBasisBoundary.chartFirstRoot plans cells evaluated)) by
        ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact ends.first_bounded.chart_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartPaid
      nonnegative)
  have lastChart : Data.Gaussian.Norm.Basic.normSq (ends.last.1 - sample.lastValue) ≤ 4 * endpointTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [sample.last_value, sample.last_root]
    exact ends.last_bounded.chart_close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartPaid
      nonnegative)
  exact EndpointRestoration.build sample ends.first.1 ends.last.1 ends.first.2 ends.last.2
    firstSource lastSource firstChart lastChart

end BasisBoundarySample

namespace BasisBoundarySample

set_option genInjectivity false in
/-- Retain the acquired direct-to-chart estimates with the restored path. Both ends are needed when this parent is
joined to its neighbours. -/
structure SourceRestoration
    {energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    (sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients joinTarget) (endpointTarget
      sourceTarget : InverseRootPolynomial.Coordinate) where
  /-- The actual endpoint-restored parent path using the same endpoint and joining target. -/ restored :
    BasisBoundarySample.EndpointRestoration sample endpointTarget endpointTarget
  /-- The retained first source/direct/chart endpoint estimate on that exact restoration. -/ first_estimate :
    ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
    sample.firstValue (restored.firstSource, restored.firstValue)
  /-- The retained last source/direct/chart endpoint estimate on that exact restoration. -/ last_estimate :
    ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget
    sample.lastValue (restored.lastSource, restored.lastValue)

constructive_injectivity SourceRestoration

end BasisBoundarySample

namespace ParentBasisRestorationAllowance

variable {allowance : Coordinate}

/-- This also matches the endpoint target of the restored root-join request. -/
@[expose] def sourceTarget (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length allowance)
  : Coordinate :=
  allocation.target / 16

/-- The restoration's one-sixteenth source target is strictly positive. -/
theorem sourceTarget_positive (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length
  allowance) :
    0 <
      (sourceTarget
      allocation) := Fraction.Order.Field.div_pos_direct allocation.target_positive (by decide)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration.ParentBasisRestorationAllowance
/-- Multiplying the selected source target by any factor at most sixteen fits the retained endpoint target. -/
private theorem scaled_sourceTarget_le (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length
  allowance)
    {factor : InverseRootPolynomial.Coordinate} (small : factor ≤ 16) : factor *
      (sourceTarget
      allocation) ≤ allocation.target := by
  have paid : 16 *
    (sourceTarget
    allocation) = allocation.target := by
    rw [sourceTarget, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small
    (sourceTarget_positive
    allocation).le).trans_eq paid

/-- Multiplying the selected source target by any factor at most sixteen fits the retained endpoint target. -/
theorem scaled_sourceTarget_le_for_restore (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance
  edges.length allowance)
    {factor : InverseRootPolynomial.Coordinate} (small : factor ≤ 16) : factor *
      (sourceTarget
      allocation) ≤ allocation.target := by
  have paid : 16 *
    (sourceTarget
    allocation) = allocation.target := by
    rw [sourceTarget, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small
    (sourceTarget_positive
    allocation).le).trans_eq paid

/-- No endpoint error estimate is supplied by the caller: the complete acquisition and the preselected source target pay
both restoration bounds. -/
@[expose] def restore (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length allowance)
    {requests : ParentChartRequests.ChartRequests allocation.target floor owners} {plans :
      ParentChartRequests.ChartPlans capSample minimum requests}
    {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated : ChartPlans.EvaluationData readingIndex
      plans cells}
    {energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {sample :
      ParentBasisBoundarySample.BasisBoundarySample energies
      coefficients allocation.target}
    {covers : SourceLocations.BasisSourceCovers parent} {sourceFloor : Nat} {sourceTarget :
      InverseRootPolynomial.Coordinate}
    {numerical : BasisSourceLocations.SampleBank covers index}
    {sources : ParentBasisEndpoints.BasisEndpointRequests covers sourceTarget sourceFloor requests}
    {planned : ParentBasisEndpoints.BasisEndpointPlans polynomials plans sources}
    {endpoints : BasisEndpointPlans.Samples numerical plans cells evaluated sources planned}
    (ends : Samples.Extremes endpoints coefficients)
    (sourceLe : sourceTarget ≤
      (ParentBasisRestorationAllowance.sourceTarget allocation)) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration.BasisBoundarySample.SourceRestoration
      sample allocation.target sourceTarget := by
  let restored : BasisBoundarySample.EndpointRestoration sample allocation.target allocation.target :=

      BasisBoundarySample.EndpointRestoration.ofEndpoints
      ends
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLe (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)).trans

          (scaled_sourceTarget_le_for_restore
          allocation (by decide)))
      (((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLe (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10)).trans

          (scaled_sourceTarget_le_for_restore
          allocation (by decide : (10 : InverseRootPolynomial.Coordinate) ≤ 16))).trans
        ((show allocation.target = 1 * allocation.target by ring1).trans_le
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) allocation.target_positive.le)))
  refine ⟨restored, ?_, ?_⟩
  · change ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget sample.firstValue ends.first
    rw [sample.first_value, sample.first_root]
    exact ends.first_bounded
  · change ParentBasisEndpointValues.EndpointEstimate coefficients sourceTarget sample.lastValue ends.last
    rw [sample.last_value, sample.last_root]
    exact ends.last_bounded

end ParentBasisRestorationAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration
