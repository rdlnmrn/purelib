module
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialBasisEnergy
public import Purelib.Riemann.Integration.AffineBasisUniformBudget
import Purelib.Tactic.Ring

@[expose] public section

/-! A shared finite request pays the homogeneous basis error on each actual
root-coordinate fan, including its increasing refinement face count. -/
namespace Purelib.Riemann.RootContinuation.RootRadialBasisRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Integration.Energy.AffineTriangle (affinePrimitiveIncrement affinePrimitiveIncrementError)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)
open Purelib.Riemann.RootContinuation.RootRadialBasisEnergy (BasisValues)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {first last :
    Purelib.Data.Gaussian.Basic.Canonical}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {bounds : RegularBasisBounds polynomials
    RootRadialGeometry.domain}
  {count minimum : Nat} {target : Rational}
  (request : RegularBasisRequest bounds count
    target minimum)
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters request.depth}
  {refinement : Refinement first last parameters}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration in
open Purelib.Riemann.Integration.AffineBasisUniformBudget.AffineBasis in
/-- Construct the uniform affine-basis budget for an actual retained root-coordinate fan triangle.

The original basis values and derivatives, domain containment, selected geometric distance and Taylor request certify
the same four local scales at the requested depth. -/
def triangleBudget (sample : BasisValues refinement polynomials)
    (face : Fin (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length) :
    AffineBasis.TriangleBudget sample.basis face := by
  have movement (last) (which : last = (parameters.mesh.mesh.triangulation.faces face).second ∨
      last = (parameters.mesh.mesh.triangulation.faces face).third) :
      Data.Gaussian.Norm.Basic.normSq (refinement.coordinates last - refinement.coordinates
        (parameters.mesh.mesh.triangulation.faces face).first) ≤ request.distance := by
    rw [request.distance_eq]
    rcases which with rfl | rfl
    · exact (refinement.distances face).1
    · exact (refinement.distances face).2
  have firstInside := (refinement.inside face).1
  refine TriangleBudget.uniform sample.basis face bounds.coefficient request.tolerance.epsilon request.distance
    bounds.coefficient_nonnegative request.tolerance.positive.le request.tolerance.le_one request.distance_positive.le
      ?_ ?_
  · intro last which
    have equal : FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrement
      (sample.basis.coefficients row face)
        (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last))) =
        FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq (Energy.AffineTriangle.affinePrimitiveIncrement
          ((polynomials.get row).coefficient.eval
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first))
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last)))
            := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [sample.coefficients_eq]
    rw [equal]
    exact bounds.affine_scale_bound firstInside (movement last which)
  · intro last which
    have lastInside : RootRadialGeometry.domain.Contains (refinement.coordinates last) := by
      rcases which with rfl | rfl
      · exact (refinement.inside face).2.1
      · exact (refinement.inside face).2.2
    have equal : FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrementError (sample.basis.coefficients row face)
        (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last)
        (sample.basis.values row (parameters.mesh.mesh.triangulation.faces face).first) (sample.basis.values row last)))
          =
        FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Norm.Basic.normSq
          (Energy.AffineTriangle.affinePrimitiveIncrementError
          ((polynomials.get row).coefficient.eval
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first))
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last)
          ((polynomials.get row).primitive.value.eval (refinement.coordinates (parameters.mesh.mesh.triangulation.faces
            face).first))
          ((polynomials.get row).primitive.value.eval (refinement.coordinates last)))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [sample.coefficients_eq, sample.values_eq, sample.values_eq]
    rw [equal]
    have estimate := bounds.error_scale_bound firstInside lastInside (movement last which)
    have taylor : bounds.remainder * request.distance^2 ≤ request.tolerance.epsilon^2 * request.distance :=
      (show bounds.remainder * request.distance^2 = (bounds.remainder * request.distance) * request.distance by
        ring1).trans_le
        (Arithmetic.mul_le_mul_of_nonneg_right_direct request.taylor request.distance_positive.le)
    have doubled := Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Rat.Fraction.Rational) ≤ 2)
      (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct request.tolerance.epsilon)
        request.distance_positive.le)
    exact (estimate.trans taylor).trans ((show request.tolerance.epsilon^2 * request.distance =
      (request.tolerance.epsilon^2 * request.distance) * 1 by ring1).trans_le (doubled.trans_eq (by ring1)))

section
open Purelib.Algebra
open Purelib.Data
/-- Cache the triangle budgets and their sum for the retained root-coordinate fan.

Each dependent vector entry uses the same basis sample and shared request, preserving the actual refined face indices.
-/
def surfaceBudget (sample : BasisValues refinement polynomials) :
    AffineBasis.SurfaceBudget sample.basis :=
  let triangles := Vector.DependentVector.ofFn (triangleBudget request sample)
  ⟨triangles, FiniteSum.Fin.sumFin (fun face => (triangles.get face).total), rfl⟩

/-- A finite constant rational sum equals its count times the constant. -/
private theorem sum_constant (size : Nat) (value : Rat.Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin size => value) = (size : Rat.Fraction.Rational) * value := by
  induction size with
  | zero => change 0 = 0 * value; ring1
  | succ size ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

end

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Geometry.Rectangle.Partition in
/-- The retained fan budget has the exact count-paid total determined by its coefficient ceiling and tolerance.

The actual refined triangle count cancels the requested squared distance, leaving the stated factor independent of
refinement depth. -/
theorem surfaceBudget_total (sample : BasisValues refinement polynomials) :
    (surfaceBudget request sample).total = 128 * (2 * bounds.coefficient + 3) * request.tolerance.epsilon := by
  rw [(surfaceBudget request sample).total_eq]
  have terms (face : Fin (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length) :
      ((surfaceBudget request sample).triangles.get face).total =
        request.tolerance.epsilon * request.distance * (2 * bounds.coefficient + 3) := by
    rw [surfaceBudget, Vector.DependentVector.ofFn_get]
    rfl
  rw [FiniteSum.Fin.sumFin_congr terms, sum_constant, parameters.mesh.faceCount_eq]
  calc
    _ = (((2 * 4^request.depth : Nat) : Rat.Fraction.Rational) * request.distance) *
        (2 * bounds.coefficient + 3) * request.tolerance.epsilon := by ring1
    _ = _ := by rw [request.face_count_cancel]

open Purelib.LinearAlgebra.Gaussian.Energy in
open Purelib.Riemann in
/-- Bound the retained root-coordinate fan's oriented boundary area from below.

The same basis coefficients multiply the count-paid error allowance, while positivity uses the retained fan orientation.
-/
theorem lower (sample : BasisValues refinement polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
      (128 * (2 * bounds.coefficient + 3) * request.tolerance.epsilon)) ≤
      ((surfaceBudget request sample).sample coefficients).boundaryArea.im / 4 := by
  have bound := sample.lower (surfaceBudget request sample) coefficients
  rw [surfaceBudget_total request sample] at bound
  exact bound

end Purelib.Riemann.RootContinuation.RootRadialBasisRequest
