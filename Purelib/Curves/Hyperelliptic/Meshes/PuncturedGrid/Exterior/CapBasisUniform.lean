module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
public import Purelib.Riemann.Integration.AffineBasisUniformBudget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Requested homogeneous triangle budgets on the actual reciprocal cap refinement. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility

namespace RegularBasisRequest

variable {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index
  box}
  {bounds : CapBasisBounds.RegularBasisBounds polynomials
    Charts.Reciprocal.Disk.RegularBounds.boundingBox}
  {count minimum : Nat} {target : Fraction.Rational}
  (request : RegularBasisRequest bounds count target
    minimum)
  {parameters : Path.Dyadic.RadialTriangles.Parameters request.depth}
  {refinement : CapRefinement.Refinement geometry coarse parameters}

/-- The actual retained basis values and derivatives satisfy the uniform
triangle budget at the selected geometric depth. -/
def triangleBudget (sample : CapBasisEnergy.RegularBasisSample refinement
  polynomials) (member : coarse ∈ attached.caps)
    (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length) :
    Readings.AffineBasisEnergy.AffineBasis.TriangleBudget sample.basis face := by
  have movement (last) (which : last = (parameters.mesh.mesh.triangulation.faces face).second ∨
      last = (parameters.mesh.mesh.triangulation.faces face).third) :
      Gaussian.Norm.Basic.normSq (refinement.coordinates last - refinement.coordinates
        (parameters.mesh.mesh.triangulation.faces face).first) ≤ request.distance := by
    rw [request.distance_eq]
    rcases which with rfl | rfl
    · exact (refinement.distances member face).1
    · exact (refinement.distances member face).2
  have firstInside := Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains (refinement.inside face).1
  refine Integration.AffineBasisUniformBudget.AffineBasis.TriangleBudget.uniform sample.basis face bounds.coefficient
    request.tolerance.epsilon request.distance
    bounds.coefficient_nonnegative request.tolerance.positive.le request.tolerance.le_one request.distance_positive.le
      ?_ ?_
  · intro last which
    have equal : FiniteSum.Fin.sumFin (fun row => Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrement (sample.basis.coefficients row face)
        (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last))) =
        FiniteSum.Fin.sumFin (fun row => Gaussian.Norm.Basic.normSq
          (Energy.AffineTriangle.affinePrimitiveIncrement ((polynomials.get row).coefficient.eval
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first))
          (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last)))
            := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [sample.coefficients_eq]
    rw [equal]
    exact bounds.affine_scale_bound firstInside (movement last which)
  · intro last which
    have lastInside : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox.Contains (refinement.coordinates
      last) := by
      rcases which with rfl | rfl
      · exact Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains (refinement.inside face).2.1
      · exact Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains (refinement.inside face).2.2
    have equal : FiniteSum.Fin.sumFin (fun row => Gaussian.Norm.Basic.normSq
      (Energy.AffineTriangle.affinePrimitiveIncrementError (sample.basis.coefficients row face)
        (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) (refinement.coordinates last)
        (sample.basis.values row (parameters.mesh.mesh.triangulation.faces face).first) (sample.basis.values row last)))
          =
        FiniteSum.Fin.sumFin (fun row => Gaussian.Norm.Basic.normSq
          (Energy.AffineTriangle.affinePrimitiveIncrementError ((polynomials.get row).coefficient.eval
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
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.taylor request.distance_positive.le)
    have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct
        request.tolerance.epsilon) request.distance_positive.le)
    exact (estimate.trans taylor).trans ((show request.tolerance.epsilon^2 * request.distance =
      (request.tolerance.epsilon^2 * request.distance) * 1 by ring1).trans_le (doubled.trans_eq (by ring1)))

/-- Assemble the actual retained uniform triangle budgets and cache their complete finite sum. -/
def surfaceBudget (sample : CapBasisEnergy.RegularBasisSample refinement
  polynomials) (member : coarse ∈ attached.caps) :
    Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget sample.basis :=
  let triangles := Vector.DependentVector.ofFn
    (RegularBasisRequest.triangleBudget request sample
    member)
  ⟨triangles, FiniteSum.Fin.sumFin (fun face => (triangles.get face).total), rfl⟩

/-- A constant finite rational sum equals its index count times the constant. -/
private theorem sum_constant (size : Nat) (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin size => value) = (size : Fraction.Rational) * value := by
  induction size with
  | zero => change 0 = 0 * value; ring1
  | succ size ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

/-- The actual retained surface budget has the exact fixed coefficient-and-tolerance total after cancellation of the
original face count. -/
theorem surfaceBudget_total (sample : CapBasisEnergy.RegularBasisSample
  refinement polynomials) (member : coarse ∈ attached.caps) :
    (RegularBasisRequest.surfaceBudget request sample
      member).total = 128 * (2 * bounds.coefficient + 3) * request.tolerance.epsilon := by
  rw [(RegularBasisRequest.surfaceBudget request sample
    member).total_eq]
  have terms (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :
      ((RegularBasisRequest.surfaceBudget request sample
        member).triangles.get face).total =
        request.tolerance.epsilon * request.distance * (2 * bounds.coefficient + 3) := by
    rw [RegularBasisRequest.surfaceBudget,
      Vector.DependentVector.ofFn_get]
    rfl
  rw [FiniteSum.Fin.sumFin_congr terms,
    RegularBasisRequest.sum_constant,
    parameters.mesh.faceCount_eq]
  calc
    _ = (((2 * 4^request.depth : Nat) : Fraction.Rational) * request.distance) *
        (2 * bounds.coefficient + 3) * request.tolerance.epsilon := by ring1
    _ = _ := by rw [request.face_count_cancel]

end RegularBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
