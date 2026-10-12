module
import Purelib.Algebra.NatCast
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.RootContinuation.RootRadialGeometry

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Mesh.CoordinateTriangulation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Cached paired polynomial samples on the actual bounded root fan.
Finite Stokes pays the full fan boundary without an orientation premise. -/
namespace Purelib.Riemann.RootContinuation.RootRadialPairedBoundary

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (Sample)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Riemann.Periods.ReciprocalCapBilinearBounds (pairedValue bilinearScale bilinear_triangle_bound)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (BoundedRefinement)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential other : Differential genus} {index otherIndex depth :
    Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Sample cap differential index box}
  {otherSample : Sample cap other otherIndex otherBox}
  {first last : Canonical} {parameters :
    Parameters depth}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.RootContinuation in
/-- Bound the original paired radial boundary by its retained geometric decay.

The actual triangle containment and distance witnesses retain both sample energy bounds; exact face-count cancellation
gives quarter-radius scale 128 squared times 64 times the bilinear scale. -/
theorem BoundedRefinement.paired_boundary_bound (refinement : BoundedRefinement first last parameters)
    (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample RootRadialGeometry.domain) (right :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds otherSample RootRadialGeometry.domain) :
    Data.Gaussian.Norm.Basic.normSq (edgeListArea (fun vertex => pairedValue sample otherSample (refinement.coordinates
      vertex))
      parameters.mesh.mesh.triangulation.boundary) ≤
        Geometric.Basic.quarterRadius (128^2 * 64 * bilinearScale left right) depth := by
  have nonnegative : (0 : Fraction.Rational) ≤ 64 := by decide +kernel
  have localBound (face : Fin (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length) :
      Data.Gaussian.Norm.Basic.normSq (triangleWedgeArea
        (pairedValue sample otherSample (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first))
        (pairedValue sample otherSample (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second))
        (pairedValue sample otherSample (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third)))
          ≤
      bilinearScale left right * (Geometric.Basic.quarterRadius 64 depth)^3 := by
    have inside := refinement.inside face
    have distance := refinement.distances face
    exact bilinear_triangle_bound left right
      inside.1 inside.2.1 inside.2.2
      (Geometric.Basic.quarterRadius_nonneg nonnegative depth)
      (Geometric.Basic.quarterRadius_le_scale nonnegative depth) distance.1 distance.2
  rw [← parameters.mesh.mesh.triangulation.wedgeSum_eq_boundaryArea]
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin _ _ localBound
  rw [Algebra.FiniteSum.Fin.Rational.sum_constant] at estimate
  have count : (((PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length : Nat) :
    Fraction.Rational) *
      Geometric.Basic.quarterRadius 64 depth = 128 := by
    rw [parameters.mesh.faceCount_eq, Purelib.Algebra.NatCast.mul, Purelib.Algebra.NatCast.pow, Nat.cast_ofNat,
      Nat.cast_ofNat, Geometric.Basic.quarterRadius]
    have denominator : (4 : Fraction.Rational)^depth ≠ 0 := (Fraction.Order.Arithmetic.pow_pos_direct (by decide)
      depth).ne'
    calc
      _ = 2 * ((64 / (4 : Fraction.Rational)^depth) * (4 : Fraction.Rational)^depth) := by ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ denominator]; decide +kernel
  apply estimate.trans_eq
  calc
    _ = ((((PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length : Nat) : Fraction.Rational) *
        Geometric.Basic.quarterRadius 64 depth)^2 * bilinearScale left right * Geometric.Basic.quarterRadius 64 depth :=
          by ring1
    _ = 128^2 * bilinearScale left right * Geometric.Basic.quarterRadius 64 depth := by rw [count]
    _ = _ := by
      simp only [Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self];
      ring1

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Cached original paired polynomial values, boundary area and certified decay bound.

The actual bounded radial refinement and both energy witnesses index the vertex cache and exact area/error readbacks. -/
structure PairedPolynomialSample (refinement : BoundedRefinement first last parameters)
    (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample RootRadialGeometry.domain) (right :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds otherSample RootRadialGeometry.domain) where
  /-- The cached paired primitive values at the original retained radial vertices. -/ values : Data.Vector
    PrimitivePoint parameters.mesh.mesh.vertices.length
  /-- Every cached entry reads back the exact original paired value at its refinement coordinate. -/ values_eq : ∀
    vertex, values vertex = pairedValue sample otherSample (refinement.coordinates vertex)
  /-- The cached original oriented boundary area. -/ area : Basic.Canonical
  /-- The area is exactly the boundary-edge sum over the actual cached values. -/ area_eq : area = edgeListArea values
    parameters.mesh.mesh.triangulation.boundary
  /-- The retained geometric decay allowance. -/ error : Fraction.Rational
  /-- The error is the exact original quarter-radius scale at the retained depth. -/ error_eq : error =
    Geometric.Basic.quarterRadius (128^2 * 64 * bilinearScale left right) depth
  /-- The cached boundary area satisfies the retained squared-norm allowance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq
    area ≤ error

constructive_injectivity PairedPolynomialSample

namespace PairedPolynomialSample

/-- Pointwise equality of original primitive values preserves the same ordered boundary-edge area. -/
theorem boundary_congr {count : Nat} {left right : Fin count → PrimitivePoint}
    (equal : ∀ vertex, left vertex = right vertex) (edges : List (OrientedEdge count)) :
    edgeListArea left edges = edgeListArea right edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change edgeArea (left edge.start) (left edge.finish) + _ = edgeArea (right edge.start) (right edge.finish) + _
      rw [equal, equal, ih]

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Riemann.RootContinuation in
/-- Cache the original paired radial values and their exact bounded boundary area.

The retained refinement coordinates determine each vector entry once; pointwise readback transports the original
boundary estimate to that actual cache. -/
@[expose] def build (refinement : BoundedRefinement first last parameters)
    (left : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample RootRadialGeometry.domain) (right :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds otherSample RootRadialGeometry.domain) :
          PairedPolynomialSample
      refinement left right := by
  let values := Vector.Basic.vectorOfFn (fun vertex => pairedValue sample otherSample (refinement.coordinates vertex))
  have valuesEq (vertex) : values vertex = pairedValue sample otherSample (refinement.coordinates vertex) :=
    Vector.Basic.vectorOfFn_apply _ vertex
  let area := edgeListArea values parameters.mesh.mesh.triangulation.boundary
  refine ⟨values, valuesEq, area, rfl, Geometric.Basic.quarterRadius (128^2 * 64 * bilinearScale left right) depth, rfl,
    ?_⟩
  have equal : area = edgeListArea (fun vertex => pairedValue sample otherSample (refinement.coordinates vertex))
      parameters.mesh.mesh.triangulation.boundary := by
    exact boundary_congr valuesEq _
  rw [equal]
  exact BoundedRefinement.paired_boundary_bound refinement left right

end PairedPolynomialSample

end Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
