module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
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
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
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

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathArea

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Uniform geometry supplies the homogeneous polygon comparison ceiling. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

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
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

universe u

namespace AreaRequest.Evaluation

variable {evaluated : Evaluation charts
  original stage}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

open Purelib.Data.Rat.Fraction.Compatibility

/-- The preselected coordinate request bounds every retained root step by one. The resulting basis ceiling is
independent of polynomial and reading stages. -/
theorem basis_increment_bound (evaluated : AreaRequest.Evaluation charts original stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients segment.last.root.coordinate -
      polynomials.value coefficients segment.first.root.coordinate) ≤
      (2 * request.basisBounds.coefficient) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound := BasisBounds.chord_increment request.basisBounds polynomials coefficients branch
    (Evaluation.square_inside request branch segment.first) (Evaluation.square_inside request branch segment.last)
    (left := 0) (right := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩
  have atZero : RootRadialGeometry.chord segment.first.root.coordinate segment.last.root.coordinate 0 =
      segment.first.root.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
  have atOne : RootRadialGeometry.chord segment.first.root.coordinate segment.last.root.coordinate 1 =
      segment.last.root.coordinate := by
    apply Data.Gaussian.Basic.ext <;> simp only [RootRadialGeometry.chord, Data.Gaussian.Scale.scale_re,
      Data.Gaussian.Scale.scale_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
  rw [atZero, atOne, show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct]
    at bound
  have step := ((evaluated.coordinate_step_bound branch segment member).trans request.coordinateStep_paid).le.trans
    request.coordinateSmall
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct step
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      request.basisBounds.coefficient_nonnegative)
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scaled normNonnegative).trans_eq (by
    ring1))

/-- Complete source/chart polygon comparison on the acquired geometry. Only the source tolerance remains to be paid by
the request schedule. -/
theorem source_path_trace_bound (evaluated : AreaRequest.Evaluation charts original stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    {sourceTarget : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ sourceTarget) {firstSource lastSource :
      InverseRootPolynomial.Gaussian}
    (values : PathValues.BasisPathValues polynomials coefficients sourceTarget evaluated.vertices.path.segments
      firstSource lastSource) :
    Data.Gaussian.Norm.Basic.normSq ((IncrementArea.traceArea firstSource (values.pairs.map Prod.fst) -
      IncrementArea.traceArea (polynomials.value coefficients evaluated.vertices.first.root.coordinate)
        (values.pairs.map Prod.snd)) -
      (BoundaryRibbon.area firstSource (lastSource - firstSource) -
        BoundaryRibbon.area (polynomials.value coefficients evaluated.vertices.first.root.coordinate)
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.pairs.map Prod.snd)))) ≤
      1280 * (evaluated.vertices.path.segments.length : InverseRootPolynomial.Coordinate)^4 * sourceTarget *
        (40 * sourceTarget + 2 * request.basisBounds.coefficient) * (PreparedObservationCoercivity.coefficientNormSq
          coefficients)^2 :=
  BasisPathValues.trace_origin_bound values _ nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.basisBounds.coefficient_nonnegative)
    (fun segment member =>
      basis_increment_bound
      evaluated coefficients branch segment member)

end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathGeometry
