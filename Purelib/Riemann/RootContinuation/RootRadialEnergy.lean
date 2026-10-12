module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Tactic.Ring

public section

/-!
# Requested polynomial energy on sampled root-coordinate fans

The original cap polynomial and bounded root endpoints determine every
finite refinement and every affine error. Both the growing face count and
the number of original root edges are paid by the shared energy request.
-/

namespace Purelib.Riemann.RootContinuation.RootRadialEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyRequest)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (domain)
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (computedAffineTriangleError)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {differential : Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {first last : Purelib.Data.Gaussian.Basic.Canonical} {depth : Nat} {parameters :
    Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Geometry in
set_option genInjectivity false in
/-- Cached polynomial readings and affine energy on one retained root-coordinate fan.

The record keeps every vertex value and face coefficient, the exact affine surface construction, and its nonnegative
energy and boundary lower bound. -/
structure PolynomialSample (refinement : Refinement first last parameters)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (radius :
      Rat.Fraction.Rational) where
  /-- The retained affine error radius is strictly positive. -/ radius_positive : 0 < radius
  /-- The cached primitive-polynomial values at the actual fan vertices. -/ values : Data.Vector
    Gaussian.Basic.Canonical parameters.mesh.mesh.vertices.length
  /-- Each cached value is the original primitive polynomial at its retained coordinate. -/ values_eq : ∀ vertex, values
    vertex = sample.primitive.value.eval (refinement.coordinates vertex)
  /-- The cached coefficient at each face's original first vertex. -/ coefficients : Data.Vector
    Gaussian.Basic.Canonical (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length
  /-- Each coefficient is the original polynomial evaluated at that retained face vertex. -/ coefficients_eq : ∀ face,
    coefficients face = sample.coefficient.eval (refinement.coordinates (parameters.mesh.mesh.triangulation.faces
    face).first)
  /-- The retained affine surface sample on the actual fan mesh. -/ surface :
    Topology.PreparedSurfaceCoercivity.AffineSurfaceSample parameters.mesh.mesh.vertices.length
    (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length
  /-- The surface is exactly the construction from these coordinates and cached readings. -/ surface_eq : surface =
    Topology.PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices parameters.mesh.mesh.triangulation
    refinement.coordinates values coefficients radius radius_positive
  /-- The retained affine energy is nonnegative. -/ affine_nonnegative : 0 ≤ surface.affineEnergy
  /-- The signed boundary energy is bounded below by the negative affine error budget. -/ lower : -surface.errorBudget ≤
    surface.boundaryArea.im / 4

constructive_injectivity PolynomialSample

namespace PolynomialSample

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- Evaluate the retained cap polynomial on the actual root-coordinate fan.

Cache its vertex readings and face coefficients once, then retain the affine surface and its exact energy certificates.
-/
@[expose] def build (refinement : Refinement first last parameters)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (radius : Rat.Fraction.Rational) (radiusPositive : 0 < radius) : PolynomialSample refinement sample radius := by
  let values := Vector.Basic.vectorOfFn (fun vertex => sample.primitive.value.eval (refinement.coordinates vertex))
  let coefficients := Vector.Basic.vectorOfFn (fun face => sample.coefficient.eval (refinement.coordinates
    (parameters.mesh.mesh.triangulation.faces face).first))
  let surface := Topology.PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices parameters.mesh.mesh.triangulation
    refinement.coordinates values coefficients radius radiusPositive
  have nonnegative : 0 ≤ surface.affineEnergy := by
    change 0 ≤ FiniteSum.Fin.sumFin (fun face => Energy.AffineTriangle.coordinateTriangleArea
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third) *
        Data.Gaussian.Norm.Basic.normSq (coefficients face))
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Rat.Fraction.Rational)) _
      (fun face => Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (refinement.nonnegative face)
        (Gaussian.Norm.Basic.normSq_nonneg (coefficients face)))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le estimate
  have lower : -surface.errorBudget ≤ surface.boundaryArea.im / 4 := by
    have monotone := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct nonnegative (le_rfl (a := surface.errorBudget))
    rw [zero_sub] at monotone
    exact monotone.trans surface.affineEnergy_sub_errorBudget_le_boundaryEnergy
  exact ⟨radiusPositive, values, Vector.Basic.vectorOfFn_apply _, coefficients, Vector.Basic.vectorOfFn_apply _,
    surface, rfl, nonnegative, lower⟩

variable {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {minimum : Nat}

open Purelib.Algebra in
open Purelib.Data in
/-- A finite constant rational sum is the index count times its value. -/
private theorem sum_constant (count : Nat) (value : Rat.Fraction.Rational) : FiniteSum.Fin.sumFin (fun _ : Fin count =>
  value) = (count : Rat.Fraction.Rational) * value := by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- Bound the fan's total affine error using the shared energy request.

The retained face count and radial mesh diameter cancel exactly, leaving 128 times the incremented coefficient weight
and selected epsilon. -/
theorem error_le (bounds : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds sample domain) {count : Nat}
  {target : Rat.Fraction.Rational}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest bounds count target minimum) {parameters
      : Path.Dyadic.RadialTriangles.Parameters request.depth}
    {refinement : Refinement first last parameters} (evaluated : PolynomialSample refinement sample request.radius) :
    evaluated.surface.errorBudget ≤ 128 * (2 * bounds.coefficient + 4) * request.epsilon := by
  let errors (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :=
    computedAffineTriangleError (evaluated.coefficients face)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).first)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).second)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).third) request.radius evaluated.radius_positive
  have localBound (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :
      (errors face).totalBudget ≤ (2 * bounds.coefficient + 4) * request.radius := by
    have inside := refinement.inside face
    have distance := refinement.distances face
    rw [← request.diameter_eq] at distance
    dsimp only [errors]
    rw [evaluated.coefficients_eq, evaluated.values_eq, evaluated.values_eq, evaluated.values_eq]
    exact bounds.triangle_budget_le _ _ _ inside.1 inside.2.1 inside.2.2 request.epsilon request.diameter request.radius
      request.epsilon_positive request.epsilon_le_one request.diameter_positive evaluated.radius_positive
        request.radius_eq
      distance.1 distance.2 request.taylor
  have aggregate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun face => (errors face).totalBudget)
    (fun _ => (2 * bounds.coefficient + 4) * request.radius) localBound
  rw [sum_constant] at aggregate
  rw [evaluated.surface_eq]
  change FiniteSum.Fin.sumFin (fun face => (errors face).totalBudget) ≤ _
  apply aggregate.trans_eq
  rw [parameters.mesh.faceCount_eq, request.radius_eq]
  calc
    _ = (((2 * 4 ^ request.depth : Nat) : Rat.Fraction.Rational) * request.diameter) *
        ((2 * bounds.coefficient + 4) * request.epsilon) := by ring1
    _ = _ := by rw [request.face_count_cancel]; ring1

end PolynomialSample
end Purelib.Riemann.RootContinuation.RootRadialEnergy
