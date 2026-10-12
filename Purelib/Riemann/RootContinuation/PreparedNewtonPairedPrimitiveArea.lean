module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Full paired primitive area is compared at every actual intermediate vertex.
The quadratic error and both factors of the edge count remain explicit. -/
namespace Purelib.Integration.Path.PairedIncrementArea

open Purelib
open Purelib.Data.Rat
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (area)
open Purelib.Algebra.FiniteSum.Fin (sumFin_succ)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The area of original indexed prefix totals equals the retained ordered trace area.

The initial primitive point and exact increment list remain fixed; finite-sum transport preserves each original oriented
edge. -/
theorem indexed_prefix_area (values : List Stokes.PrimitivePoint) (start : Stokes.PrimitivePoint) :
    CenteredBilinearPath.area
      (fun vertex : Fin (values.length + 1) => start.add (PairedIncrementArea.total (values.take vertex.val))) =
        PairedIncrementArea.traceArea start values := by
  induction values generalizing start with
  | nil => rfl
  | cons first rest ih =>
    have reassociate : CenteredBilinearPath.area
        (fun vertex : Fin (rest.length + 1) => start.add (first.add (PairedIncrementArea.total (rest.take vertex.val))))
          =
        CenteredBilinearPath.area
          (fun vertex : Fin (rest.length + 1) => (start.add first).add (PairedIncrementArea.total (rest.take
            vertex.val))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro edge
      apply congrArg₂ Stokes.edgeArea
      · exact congrArg₂ Stokes.PrimitivePoint.mk (Basic.add_assoc _ _ _).symm (Basic.add_assoc _ _ _).symm
      · exact congrArg₂ Stokes.PrimitivePoint.mk (Basic.add_assoc _ _ _).symm (Basic.add_assoc _ _ _).symm
    calc
      _ = Stokes.edgeArea start (start.add first) +
        CenteredBilinearPath.area
          (fun vertex : Fin (rest.length + 1) => start.add (first.add (PairedIncrementArea.total (rest.take
            vertex.val)))) := by
        rw [CenteredBilinearPath.area, FiniteSum.Fin.sumFin_succ]
        apply congrArg₂ (fun left right : PairedIncrementArea.Gaussian => left + right)
        · simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero,
            List.take_zero, List.take_succ_cons, PairedIncrementArea.total, List.map_cons, List.map_nil,
              Data.Gaussian.Norm.Sum.Basic.gaussianSum,
            Stokes.PrimitivePoint.add, Basic.add_zero, -eq_self, -iff_self]
          rfl
        · apply FiniteSum.Fin.sumFin_congr
          intro edge
          rfl
      _ = Stokes.edgeArea start (start.add first) + PairedIncrementArea.traceArea (start.add first) rest := by
        rw [reassociate, ih]
      _ = _ := rfl

end Purelib.Integration.Path.PairedIncrementArea

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent

open Purelib
open Purelib.Data.Rat
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin_sub)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (area)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {parent : CenteredEdge
    curve differential}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Topology.Surface in
/-- Bound an original edge-area perturbation from its retained endpoint magnitudes and errors.

The separate endpoint bounds give 24 times magnitude times error plus 16 times error squared. -/
private theorem edge_difference {first last changedFirst changedLast : PrimitivePoint}
    {magnitude error : Fraction.Rational} (firstBound : PrimitiveAreaBounds.PrimitivePoint.Bounded first magnitude)
      (lastBound : PrimitiveAreaBounds.PrimitivePoint.Bounded last magnitude)
    (firstError : PrimitiveAreaBounds.PrimitivePoint.Bounded (changedFirst.sub first) error) (lastError :
      PrimitiveAreaBounds.PrimitivePoint.Bounded (changedLast.sub last) error) :
    normSq (edgeArea changedFirst changedLast - edgeArea first last) ≤
      24 * magnitude * error + 16 * error^2 := by
  have expanded : edgeArea changedFirst changedLast - edgeArea first last =
      edgeArea (changedFirst.sub first) changedLast + edgeArea first (changedLast.sub last) := by
    simp only [edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
    ring1
  rw [expanded]
  have firstArea := PrimitiveAreaBounds.PrimitivePoint.area_bound firstError
    (Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded lastBound lastError)
  have lastArea := PrimitiveAreaBounds.PrimitivePoint.area_bound firstBound lastError
  rw [← Norm.Basic.normSq_eq_canonical] at firstArea lastArea
  exact ((Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct firstArea lastArea) (by decide))).trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Bound the original primitive-versus-numerical vertex area using retained prefix comparisons.

The exact increment count squared multiplies the same endpoint perturbation estimate, with the original density sum,
movement and maximum model error. -/
theorem primitive_area_error_le (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    normSq (area (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1)
      => paired.primitiveVertex first second vertex.val) -
      area (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
        paired.numericalVertex vertex.val)) ≤
      ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length : Fraction.Rational)^2 *
        (24 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
          PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
            PreparedPrimitiveRequests.movement parent) *
          max first.2.2.bound second.2.2.bound + 16 * (max first.2.2.bound second.2.2.bound)^2) := by
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le
    (fun edge : Fin (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length =>
      edgeArea (paired.primitiveVertex first second edge.val)
          (paired.primitiveVertex first second (edge.val + 1)) -
        edgeArea (paired.numericalVertex edge.val) (paired.numericalVertex (edge.val + 1)))
    _ (fun edge => edge_difference (paired.numericalVertex_bounded otherProfile edge.val)
      (paired.numericalVertex_bounded otherProfile (edge.val + 1))
      (paired.vertices_accurate first second edge.val) (paired.vertices_accurate first second (edge.val + 1)))
  rw [FiniteSum.Fin.sumFin_sub] at estimate
  exact estimate

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- The area of original numerical prefix vertices is exactly the retained zero-anchored trace area. -/
theorem numerical_area_readback (paired : PairedBoundaryParent request parent other) :
    area (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
      paired.numericalVertex vertex.val) =
      PairedIncrementArea.traceArea PrimitivePoint.zero (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments
        paired) := by
  have readback := PairedIncrementArea.indexed_prefix_area
    (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired) PrimitivePoint.zero
  simpa only [area, numericalVertex, PairedIncrementArea.total, PrimitivePoint.zero, PrimitivePoint.add,
    Basic.zero_add, -eq_self, -iff_self] using readback

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Compare the original primitive vertex area directly with the retained numerical trace.

The exact numerical-area readback preserves the original count, density and maximum-error factors of the vertex
comparison. -/
theorem primitive_trace_area_error_le (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    normSq (area (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1)
      => paired.primitiveVertex first second vertex.val) -
      PairedIncrementArea.traceArea PrimitivePoint.zero (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments
        paired)) ≤
      ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length : Fraction.Rational)^2 *
        (24 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
          PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
            PreparedPrimitiveRequests.movement parent) *
          max first.2.2.bound second.2.2.bound + 16 * (max first.2.2.bound second.2.2.bound)^2) := by
  have bounded := paired.primitive_area_error_le otherProfile first second
  rw [paired.numerical_area_readback] at bounded
  exact bounded

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent
