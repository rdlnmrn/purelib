module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Readings.PrimitiveTriangleEnergy
import Purelib.Tactic.Ring

@[expose] public section

/-! Two-differential wedge bounds for the actual shared primitive basis.
Both affine parts use the same coordinate increments and operational root;
their determinant cancels exactly. Every remaining term contains an actual
primitive approximation error. -/

namespace Purelib.Riemann.Periods.PrimitiveTriangleBilinear

open Purelib.Data in
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
open _root_.Purelib.Riemann.Integration (PrimitiveBasis)
open _root_.Purelib.Riemann.Integration.PrimitiveBasis (Coefficients)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Topology.Polygon.Stokes (triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

section
open Purelib.Data
/-- The squared norm of three Gaussian summands is at most four times the sum of their squared norms. -/
private theorem three_bound (a b c : Gaussian.Basic.Canonical) :
    normSq (a + b + c) ≤ 4 * (normSq a + normSq b + normSq c) := by
  have first := Gaussian.Norm.Bounds.normSq_add_le_two (a + b) c
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at first
  have pair := Gaussian.Norm.Bounds.normSq_add_le_two a b
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at pair
  have second := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.add_le_add_right_direct pair (normSq c))
    (by decide : (0 : Coordinate) ≤ 2)
  have extra := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide : (0 : Coordinate) ≤ 2) (Gaussian.Basic.Canonical.normSq_nonneg c)
  exact (first.trans second).trans
    (Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct (by
      have equal : 4 * (normSq a + normSq b + normSq c) -
          2 * (2 * (normSq a + normSq b) + normSq c) = 2 * normSq c := by ring1
      rw [equal]
      exact extra))

/-- Multiply two separated squared-norm bounds while retaining their two independent coefficient factors. -/
private theorem product_bound {x y : Gaussian.Basic.Canonical} {s t a b : Coordinate}
    (first : normSq x ≤ s * a) (last : normSq y ≤ t * b) :
    normSq (x * y) ≤ s * t * (a * b) := by
  rw [Gaussian.Basic.Canonical.normSq_mul]
  exact ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct first (Gaussian.Basic.Canonical.normSq_nonneg
    y)).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct last ((Gaussian.Basic.Canonical.normSq_nonneg
      x).trans first))).trans_eq
    (by ring1)

/-- Bound the determinant of two approximate multiples of the same pair of increments.

The exact affine determinant cancels. All remaining terms contain an actual approximation error, giving sixteen times
the two mixed affine-error products and the error product. -/
theorem bilinearDeterminant_bound (a b u v x y p q : Gaussian.Basic.Canonical) (s t A B E F : Coordinate)
    (au : normSq (a * u) ≤ s * A) (av : normSq (a * v) ≤ s * B)
    (bu : normSq (b * u) ≤ t * A) (bv : normSq (b * v) ≤ t * B)
    (xe : normSq (x - a * u) ≤ s * E) (yf : normSq (y - a * v) ≤ s * F)
    (pg : normSq (p - b * u) ≤ t * E) (qh : normSq (q - b * v) ≤ t * F) :
    normSq (x * q - y * p) ≤ s * t * (16 * (A * F + B * E + E * F)) := by
  let e := x - a * u
  let f := y - a * v
  let g := p - b * u
  let h := q - b * v
  have decomposition : x * q - y * p =
      ((a * u) * h + e * (b * v) + e * h) -
        ((a * v) * g + f * (b * u) + f * g) := by
    dsimp only [e, f, g, h]
    ring1
  have first := three_bound ((a * u) * h) (e * (b * v)) (e * h)
  have last := three_bound ((a * v) * g) (f * (b * u)) (f * g)
  have firstTerms := add_le_add (add_le_add (product_bound au qh) (product_bound xe bv)) (product_bound xe qh)
  have lastTerms := add_le_add (add_le_add (product_bound av pg) (product_bound yf bu)) (product_bound yf pg)
  have firstPaid := first.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstTerms
    (by decide : (0 : Coordinate) ≤ 4))
  have lastPaid := last.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastTerms
    (by decide : (0 : Coordinate) ≤ 4))
  rw [decomposition]
  have triangle := Gaussian.Norm.Bounds.normSq_sub_le_two
    ((a * u) * h + e * (b * v) + e * h)
    ((a * v) * g + f * (b * u) + f * g)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
  exact triangle.trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstPaid lastPaid)
      (by decide : (0 : Coordinate) ≤ 2)).trans_eq (by ring1))

end

namespace PrimitiveTriangleBudget

variable {polynomial : Polynomial} {siteCount index count : Nat}
  {patch : ContinuedNeighborhood polynomial siteCount} {basis : PrimitiveBasis patch index count}
  {first second third : Canonical}

open Purelib.Riemann in
/-- Compute the wedge-error scale from the four retained affine and error scales. -/
def bilinearSquare (budget : Readings.PrimitiveTriangleEnergy.PrimitiveTriangleBudget basis first second third) :
  Coordinate :=
  16 * (budget.firstAffine * budget.secondError + budget.secondAffine * budget.firstError +
    budget.firstError * budget.secondError)

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Bound the wedge of two actual primitive combinations on one triangle.

Both combinations use the same coordinate increments and operational root. Their coefficient squared norms factor out,
and the remaining bound uses only cached affine and increment-error scales. -/
theorem bilinear_bound (budget : Readings.PrimitiveTriangleEnergy.PrimitiveTriangleBudget basis first second third)
    (left right : Coefficients count)
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (sample : ContinuedNeighborhood.Point patch first) {root : Gaussian.Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    normSq (triangleWedgeArea
      ⟨basis.value left first, basis.value right first⟩
      ⟨basis.value left second, basis.value right second⟩
      ⟨basis.value left third, basis.value right third⟩) ≤
      coefficientNormSq left * coefficientNormSq right *
        Periods.PrimitiveTriangleBilinear.PrimitiveTriangleBudget.bilinearSquare budget := by
  have affine (coefficients : Coefficients count) (point : Gaussian.Basic.Canonical) :
      normSq (((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval first / root) * (point - first)) ≤
        coefficientNormSq coefficients * (basis.coefficientScale * normSq (point - first)) := by
    rw [Gaussian.Basic.Canonical.normSq_mul]
    exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (basis.operational_coefficient_bound coefficients firstInside sample (sample.readingState index) possible)
      (Gaussian.Basic.Canonical.normSq_nonneg _)).trans_eq (by ring1)
  unfold triangleWedgeArea bilinearSquare
  apply bilinearDeterminant_bound
    ((Geometry.EvaluationLower.coefficientPolynomial left).eval first / root)
    ((Geometry.EvaluationLower.coefficientPolynomial right).eval first / root) (second - first) (third - first)
  · rw [budget.firstAffine_eq]; exact affine left second
  · rw [budget.secondAffine_eq]; exact affine left third
  · rw [budget.firstAffine_eq]; exact affine right second
  · rw [budget.secondAffine_eq]; exact affine right third
  · rw [budget.firstError_eq]
    exact basis.operational_increment_bound left firstInside secondInside sample possible
  · rw [budget.secondError_eq]
    exact basis.operational_increment_bound left firstInside thirdInside sample possible
  · rw [budget.firstError_eq]
    exact basis.operational_increment_bound right firstInside secondInside sample possible
  · rw [budget.secondError_eq]
    exact basis.operational_increment_bound right firstInside thirdInside sample possible

end PrimitiveTriangleBudget
end Purelib.Riemann.Periods.PrimitiveTriangleBilinear
