module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Prepay the full retained source-polygon comparison before acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues (BasisPathValues)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
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

open Purelib.Data.Rat.Fraction.Compatibility

namespace AreaRequest

set_option genInjectivity false in
/-- A source target chosen from the retained mesh count and uniform basis ceiling, before any source polynomial or root
reading is acquired. -/
structure BasisSourceAllowance (request : ChartAreaRequest.AreaRequest comparison owners target floor)
    (endpointTarget allowance : InverseRootPolynomial.Coordinate) where
  /-- The cached complete source-polygon comparison weight from the original mesh count and uniform basis bound. -/
    weight : InverseRootPolynomial.Coordinate
  /-- The weight is exactly the original fourth-power mesh-count expression with the retained basis coefficient. -/
    weight_eq : weight = 1280 * (request.count : InverseRootPolynomial.Coordinate)^4 * (40 + 2 *
    request.basisBounds.coefficient)
  /-- The cached common positive source comparison tolerance. -/ sourceTarget : InverseRootPolynomial.Coordinate
  /-- The source tolerance is the minimum of the unit ceiling, original endpoint tolerance and retained weighted area
    allowance. -/ source_eq : sourceTarget = min 1 (min endpointTarget (Weighted.allowance ((4 * allowance)^2) weight))
  /-- The actual retained source tolerance is strictly positive. -/ positive : 0 < sourceTarget
  /-- The retained source tolerance is at most one. -/ small : sourceTarget ≤ 1
  /-- The retained source tolerance pays the original endpoint comparison target. -/ endpoint_le : sourceTarget ≤
    endpointTarget
  /-- The complete original source-polygon error expression is paid by the retained squared area allowance. -/ paid :
    1280 * (request.count : InverseRootPolynomial.Coordinate)^4 * sourceTarget *
    (40 * sourceTarget + 2 * request.basisBounds.coefficient) ≤ (4 * allowance)^2

constructive_injectivity BasisSourceAllowance

namespace BasisSourceAllowance

/-- Choose the positive source tolerance from the original geometry and uniform basis bounds, retaining both endpoint
and complete polygon payment. -/
def build (request : ChartAreaRequest.AreaRequest comparison owners target floor)
    (endpointTarget allowance : InverseRootPolynomial.Coordinate) (endpointPositive : 0 < endpointTarget) (positive : 0
      < allowance) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest.BasisSourceAllowance request
      endpointTarget allowance := by
  let coefficient := request.basisBounds.coefficient
  have coefficientNonnegative : 0 ≤ coefficient := request.basisBounds.coefficient_nonnegative
  let factor := 1280 * (request.count : InverseRootPolynomial.Coordinate)^4
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  let weight := factor * (40 + 2 * coefficient)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (add_nonneg (by decide +kernel) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative))
  have squarePositive : 0 < (4 * allowance)^2 := Fraction.Order.Arithmetic.pow_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) 2
  let sourceTarget := min 1 (min endpointTarget (Weighted.allowance ((4 * allowance)^2) weight))
  have sourcePositive : 0 < sourceTarget := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min endpointPositive (Weighted.allowance_positive squarePositive weightNonnegative))
  have small : sourceTarget ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have factorLe : 40 * sourceTarget + 2 * coefficient ≤ 40 + 2 * coefficient := by
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 40)
    rw [Fraction.Field.mul_one_direct] at scaled
    exact Fraction.Order.Arithmetic.add_le_add_direct scaled le_rfl
  have estimated := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorLe
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative sourcePositive.le)
  have budgetLe : sourceTarget ≤ Weighted.allowance ((4 * allowance)^2) weight :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  have budgetPaid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budgetLe weightNonnegative).trans
    (Weighted.mul_allowance_le squarePositive.le weightNonnegative)
  refine ⟨weight, rfl, sourceTarget, rfl, sourcePositive, small,
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _), ?_⟩
  exact estimated.trans ((show factor * sourceTarget * (40 + 2 * coefficient) = weight * sourceTarget by ring1).trans_le
    budgetPaid)

/-- A common parent tolerance may be smaller than each cell's allocation. -/
theorem paid_of_le {endpointTarget allowance sourceTarget : InverseRootPolynomial.Coordinate}
    (allocation : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest.BasisSourceAllowance
      request endpointTarget allowance)
    (nonnegative : 0 ≤ sourceTarget) (smaller : sourceTarget ≤ allocation.sourceTarget) :
    1280 * (request.count : InverseRootPolynomial.Coordinate)^4 * sourceTarget *
      (40 * sourceTarget + 2 * request.basisBounds.coefficient) ≤ (4 * allowance)^2 := by
  have factorNonnegative : 0 ≤ 1280 * (request.count : InverseRootPolynomial.Coordinate)^4 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have left := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller factorNonnegative
  have right := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 40))
    (le_refl (2 * request.basisBounds.coefficient))
  have rightNonnegative : 0 ≤ 40 * sourceTarget + 2 * request.basisBounds.coefficient :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.basisBounds.coefficient_nonnegative)
  exact (Fraction.Order.Arithmetic.mul_le_mul_direct left right rightNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative allocation.positive.le)).trans allocation.paid

end BasisSourceAllowance
end AreaRequest

namespace AreaRequest.Evaluation

variable {polynomials :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- The automatically chosen source target pays the homogeneous polygon error, with the two trace-origin terms still
explicitly present. -/
theorem source_path_paid (evaluated : AreaRequest.Evaluation charts original stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    {endpointTarget allowance : InverseRootPolynomial.Coordinate} (allocation :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance.AreaRequest.BasisSourceAllowance request
      endpointTarget allowance)
    {sourceTarget : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ sourceTarget) (smaller : sourceTarget ≤
      allocation.sourceTarget)
    {firstSource lastSource : InverseRootPolynomial.Gaussian}
    (values : PathValues.BasisPathValues polynomials coefficients sourceTarget evaluated.vertices.path.segments
      firstSource lastSource) :
    Data.Gaussian.Norm.Basic.normSq ((IncrementArea.traceArea firstSource (values.pairs.map Prod.fst) -
      IncrementArea.traceArea (polynomials.value coefficients evaluated.vertices.first.root.coordinate)
        (values.pairs.map Prod.snd)) -
      (BoundaryRibbon.area firstSource (lastSource - firstSource) -
        BoundaryRibbon.area (polynomials.value coefficients evaluated.vertices.first.root.coordinate)
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.pairs.map Prod.snd)))) ≤
      (4 * allowance)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bound := Evaluation.source_path_trace_bound evaluated coefficients branch nonnegative values
  have countEq : evaluated.vertices.path.segments.length = request.count :=
    evaluated.vertices.path.count_eq.trans request.count_eq.symm
  rw [countEq] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (allocation.paid_of_le nonnegative
    smaller) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceAllowance
