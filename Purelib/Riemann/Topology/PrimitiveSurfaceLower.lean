module
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
public import Purelib.Riemann.Topology.PrimitiveBoxSurface
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Checked surface density below actual operational primitive energy

An operational root reading is approximate, not an exact algebraic root.
Its proved residual estimate retains one quarter of the existing checked
surface-cell density.  Exact triangulated area summation transfers that
lower bound to the actual affine energy, then to the shared primitive's
exterior boundary after paying the requested homogeneous total error.
-/

namespace Purelib.Riemann.Topology.PrimitiveSurfaceLower

open Purelib.Data.Rat in
/-- Rational coordinate type for primitive surface lower bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- Gaussian rational carrier for primitive surface readings. -/
private abbrev Gaussian := Basic.Canonical
/-- Rational box type for retained primitive surface cells. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
open Purelib.Riemann.Integration.PrimitiveBasis (Coefficients PrimitiveBasisPreflight)
open _root_.Purelib.Riemann.Topology (PrimitiveSurfaceBudget)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (TriangulatedPartition boxTriangles)
open _root_.Purelib.Riemann.Topology (PrimitiveBoxSurface)
open _root_.Purelib.Riemann.Topology.PrimitiveBoxSurface (PrimitiveFaceReading)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (rectangleBoundary)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.LinearAlgebra
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial

namespace PreparedEnergy.SurfaceCell

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A controlled square residual bounds the approximate root's squared norm.

If the root-square residual is no larger than the parameter norm, the squared root norm is bounded by four times that
parameter norm. -/
private theorem approximate_root_square_le {parameter root : Basic.Canonical}
    (residual : normSq (root ^ 2 - parameter) ≤ normSq parameter) :
    normSq root ^ 2 ≤ 4 * normSq parameter := by
  calc
    _ = normSq (root ^ 2) := by
      have scalar := Power.normSq_pow root 2
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar.symm
    _ = normSq ((root ^ 2 - parameter) + parameter) := by rw [sub_add_cancel]
    _ ≤ 2 * (normSq (root ^ 2 - parameter) + normSq parameter) := by
      have scalar := Norm.Bounds.normSq_add_le_two (root ^ 2 - parameter) parameter
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar
    _ ≤ 2 * (normSq parameter + normSq parameter) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_right_direct residual (normSq parameter))
        (by decide : (0 : Fraction.Rational) ≤ 2)
    _ = _ := by ring1

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- One quarter of the retained density lower bound controls an approximate differential.

For a point inside the cell and a nonzero root whose square residual is bounded by the polynomial norm, compares the
numerator and root norms using the original density certificates. -/
theorem densityLower_quarter_le_approximateDifferential {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {coefficients : Coefficients genus}
    (cell : Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {point root : Basic.Canonical}
    (inside : cell.box.Contains point) (nonzero : root ≠ 0)
    (residual : normSq (root ^ 2 - curve.polynomial.eval point) ≤ normSq (curve.polynomial.eval point)) :
    cell.densityLower / 4 ≤ normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point / root) :=
      by
  have rootNonnegative := Basic.Canonical.normSq_nonneg root
  have squareLe := approximate_root_square_le residual
  have multiplied : cell.densityLower * normSq root ≤
      4 * normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by
    by_cases small : normSq root ≤ 1
    · calc
        _ ≤ cell.densityLower * 1 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small cell.densityLower_nonnegative
        _ = cell.densityLower := by ring1
        _ ≤ normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by
          have scalar := cell.density_below_numerator point inside
          simpa only [Norm.Basic.normSq_eq_canonical] using scalar
        _ ≤ _ := by
          simpa only [_root_.one_mul] using
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 : Fraction.Rational) ≤ 4)
              (Basic.Canonical.normSq_nonneg ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point))
    · have oneLe : (1 : Fraction.Rational) ≤ normSq root := (lt_of_not_ge small).le
      have normLeSquare : normSq root ≤ normSq root ^ 2 := by
        calc
          _ = 1 * normSq root := by ring1
          _ ≤ normSq root * normSq root := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe
            rootNonnegative
          _ = _ := by ring1
      calc
        _ ≤ cell.densityLower * (4 * normSq (curve.polynomial.eval point)) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (normLeSquare.trans squareLe)
            cell.densityLower_nonnegative
        _ = 4 * (cell.densityLower * normSq (curve.polynomial.eval point)) := by ring1
        _ ≤ _ := by
          have scalar := cell.density_valid point inside
          simp only [Norm.Basic.normSq_eq_canonical] at scalar
          exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct scalar (by decide)
  rw [Basic.Canonical.normSq_div _ _ nonzero]
  have rootPositive : 0 < normSq root := by
    simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Basic.normSq_pos nonzero
  apply (Fraction.Order.Field.le_div_iff_pos rootPositive).mpr
  calc
    _ = (cell.densityLower * normSq root) / 4 := by
      simp only [Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ ≤ _ := (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
      (multiplied.trans_eq (by ring1))

end PreparedEnergy.SurfaceCell

namespace InverseRootPolynomial.PrimitiveFaceReading

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- A retained primitive face reading satisfies the quarter-density lower bound.

Uses its actual root candidate, positive root lower bound and retained relative-error certificate at the reading's point
inside the cell. -/
theorem density_lower {genus siteCount index : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {patch : ContinuedNeighborhood curve.polynomial siteCount} {coefficients : Coefficients genus}
    (reading : PrimitiveFaceReading patch index) (cell : Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients)
    (inside : cell.box.Contains reading.point) :
    cell.densityLower / 4 ≤ normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval reading.point /
      reading.root) := by
  have positive := patch.rootLower_positive.trans_le (reading.sample.candidate_lower _ reading.possible)
  have nonzero : reading.root ≠ 0 := by
    intro zero
    rw [zero, Basic.Canonical.normSq_zero] at positive
    exact lt_irrefl 0 positive
  have residual := reading.sample.candidate_residual (ContinuedNeighborhood.relativeRootError index)
    (ContinuedNeighborhood.relativeRootError_positive index) reading.possible
  have errorLe : ContinuedNeighborhood.relativeRootError index ≤ 1 :=
    (ContinuedNeighborhood.relativeRootError_small index).trans (by decide +kernel : (1 / 4096 : Fraction.Rational) ≤ 1)
  have residualLe : normSq (reading.root ^ 2 - curve.polynomial.eval reading.point) ≤ normSq (curve.polynomial.eval
    reading.point) :=
    residual.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct errorLe (Basic.Canonical.normSq_nonneg
      (curve.polynomial.eval reading.point))).trans_eq (by ring1))
  exact PrimitiveSurfaceLower.PreparedEnergy.SurfaceCell.densityLower_quarter_le_approximateDifferential cell inside
    nonzero residualLe

end InverseRootPolynomial.PrimitiveFaceReading

namespace InverseRootPolynomial.PrimitiveBoxSurface.Readings

variable {genus siteCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {patch : ContinuedNeighborhood curve.polynomial siteCount} {preflight : PrimitiveBasisPreflight patch genus}
  {box : Purelib.Geometry.Rational.Box} {target : Purelib.Data.Rat.Fraction.Rational} {surface :
    PrimitiveBoxSurface preflight box target}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Energy in
open Purelib.Riemann.Topology in
/-- Cell content times quarter-density is bounded by retained affine energy.

Weights the actual face readings by positive triangle areas and uses the exact partition area sum over the original cell
box. -/
theorem cell_energy_le_affineEnergy (readings : PrimitiveBoxSurface.Readings surface)
    (coefficients : Coefficients genus) (cell : Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) (boxEq :
      cell.box = box) :
    Box.Content.boxContent cell.box * (cell.densityLower / 4) ≤ (readings.sample coefficients).affineEnergy := by
  have proper : surface.mesh.partition.parent.Proper := by rw [surface.parent_eq, ← boxEq]; exact cell.proper
  have pointwise (face : Fin surface.faceCount) : cell.densityLower / 4 ≤
      normSq ((readings.sample coefficients).faceCoefficient face) := by
    change cell.densityLower / 4 ≤ normSq ((Vector.Basic.vectorOfFn _) face)
    rw [Vector.Basic.vectorOfFn_apply]
    exact PrimitiveSurfaceLower.InverseRootPolynomial.PrimitiveFaceReading.density_lower (readings.entries face) cell
      (by rw [boxEq, readings.point_eq]; exact (surface.face_inside face).1)
  rw [(readings.sample coefficients).affineEnergy_eq]
  have weighted (face : Fin surface.faceCount) :
      AffineTriangle.coordinateTriangleArea
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first)
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).second)
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).third) * (cell.densityLower / 4) ≤
      AffineTriangle.coordinateTriangleArea
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).first)
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).second)
        (surface.mesh.mesh.coordinate (surface.mesh.mesh.triangulation.faces face).third) *
        Data.Gaussian.Norm.Basic.normSq ((readings.sample coefficients).faceCoefficient face) := by
    have scalar : cell.densityLower / 4 ≤
        Data.Gaussian.Norm.Basic.normSq ((readings.sample coefficients).faceCoefficient face) := by
      simpa only [Norm.Basic.normSq_eq_canonical] using pointwise face
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      scalar (surface.mesh.faceArea_positive proper face).le
  have lower := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ weighted
  apply le_trans ?_ lower
  apply le_of_eq
  rw [FiniteSum.Fin.sumFin_mul_right, surface.mesh.areaSum_eq, surface.mesh.partition.area_eq, surface.parent_eq, boxEq]

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Geometry.Rational in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
open Purelib.Data.Rat in
/-- The retained cell energy minus its coefficient error bounds the rectangle boundary energy.

Composes the affine-energy lower bound with the surface's original budgeted boundary certificate, preserving the exact
cell-box identity and mesh depth. -/
theorem cell_energy_sub_error_le_rectangleBoundary (readings : PrimitiveBoxSurface.Readings surface)
    (coefficients : Coefficients genus) (cell : Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) (boxEq :
      cell.box = box) :
    Box.Content.boxContent cell.box * (cell.densityLower / 4) -
        PreparedObservationCoercivity.coefficientNormSq coefficients * target ≤
      (PreparedBoxBoundary.rectangleBoundary (fun point => Polygon.energyPrimitivePoint (surface.budget.basis.value
        coefficients point))
        surface.budget.depth box).im / 4 :=
  (Fraction.Order.Arithmetic.sub_le_sub_right_direct
    (PrimitiveSurfaceLower.InverseRootPolynomial.PrimitiveBoxSurface.Readings.cell_energy_le_affineEnergy readings
    coefficients cell boxEq) _).trans
    (readings.sample_energy_le_rectangleBoundary coefficients)

end InverseRootPolynomial.PrimitiveBoxSurface.Readings

end Purelib.Riemann.Topology.PrimitiveSurfaceLower

