module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Composition
import Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Homography

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Pulling finite CCL comparisons back to the original coordinate

Raw-parser predicates are stated at the current affine tail, whereas the
winding boxes live in the original polynomial coordinate.  This module
precomposes every Hermitian comparison with a finite decoder homography and
clears its denominator by a positive squared norm.  It also supplies the
explicit adjugate chart used to recover the unique parser tail.
-/

namespace Purelib.Geometry.Projective.Homography

/-- An invertible forward homography has a nonzero adjugate denominator at every affine image in its domain. -/
theorem adjugate_denominator_homographic_ne
    (matrix : GaussianMatrix) (input : Data.Gaussian.Basic.Canonical)
    (determinantNonzero : BoundaryAdjugate.determinant matrix ≠ 0)
    (denominatorNonzero : Homography.Basic.denominator matrix input ≠ 0) :
    Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix) (Homography.Basic.homographic matrix input) ≠ 0 :=
      by
  have productDenominator :
      Homography.Basic.denominator (Coordinates2.Matrix.mul (BoundaryAdjugate.adjugate matrix) matrix) input ≠ 0 := by
    rw [BoundaryAdjugate.adjugate_mul]
    simpa only [Homography.Basic.denominator,
      Data.Gaussian.Basic.zero_mul,
      Data.Gaussian.Basic.zero_add,
      Data.Gaussian.Basic.add_zero] using determinantNonzero
  exact (Composition.denominator_mul_ne_iff (BoundaryAdjugate.adjugate matrix) matrix input
    denominatorNonzero).1 productDenominator

/-- Applying a decoder and then its adjugate recovers the affine input. -/
theorem homographic_adjugate_forward_inverse
    (matrix : GaussianMatrix) (input : Data.Gaussian.Basic.Canonical)
    (determinantNonzero : BoundaryAdjugate.determinant matrix ≠ 0)
    (denominatorNonzero : Basic.denominator matrix input ≠ 0) :
    Basic.homographic (BoundaryAdjugate.adjugate matrix) (Basic.homographic matrix input) = input := by
  have inverseDenominator := adjugate_denominator_homographic_ne matrix input
    determinantNonzero denominatorNonzero
  calc
    Basic.homographic (BoundaryAdjugate.adjugate matrix) (Basic.homographic matrix input) =
        Basic.homographic (Coordinates2.Matrix.mul (BoundaryAdjugate.adjugate matrix) matrix) input :=
      (Composition.homographic_mul (BoundaryAdjugate.adjugate matrix) matrix input denominatorNonzero
        inverseDenominator).symm
    _ = input := by
      rw [BoundaryAdjugate.adjugate_mul]
      unfold Basic.homographic Basic.numerator Basic.denominator
      rw [Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.add_zero]
      calc
        BoundaryAdjugate.determinant matrix * input * (BoundaryAdjugate.determinant matrix)⁻¹ =
            input * (BoundaryAdjugate.determinant matrix * (BoundaryAdjugate.determinant matrix)⁻¹) := by
          rw [Data.Gaussian.Basic.mul_comm
              (BoundaryAdjugate.determinant matrix) input,
            Data.Gaussian.Basic.mul_assoc]
        _ = input := by
          rw [Data.Gaussian.Field.inv_eq,
            Data.Gaussian.Field.mul_inv _ determinantNonzero,
            Data.Gaussian.Basic.mul_one]

/-- The inverse chart's nonzero denominator forces the recovered forward denominator to be nonzero. -/
theorem denominator_inverse_tail_ne
    (matrix : GaussianMatrix) (input : Data.Gaussian.Basic.Canonical)
    (determinantNonzero : BoundaryAdjugate.determinant matrix ≠ 0)
    (inverseDenominator : Homography.Basic.denominator (BoundaryAdjugate.adjugate matrix) input ≠ 0) :
    Homography.Basic.denominator matrix (Homography.Basic.homographic (BoundaryAdjugate.adjugate matrix) input) ≠ 0 :=
      by
  have productDenominator :
      Homography.Basic.denominator (Coordinates2.Matrix.mul matrix (BoundaryAdjugate.adjugate matrix)) input ≠ 0 := by
    rw [BoundaryAdjugate.mul_adjugate]
    simpa only [Homography.Basic.denominator,
      Data.Gaussian.Basic.zero_mul,
      Data.Gaussian.Basic.zero_add,
      Data.Gaussian.Basic.add_zero] using determinantNonzero
  exact (Composition.denominator_mul_ne_iff matrix (BoundaryAdjugate.adjugate matrix) input
    inverseDenominator).1 productDenominator

/-- Decoding the adjugate tail returns the original affine input. -/
theorem homographic_adjugate_inverse
    (matrix : GaussianMatrix) (input : Data.Gaussian.Basic.Canonical)
    (determinantNonzero : BoundaryAdjugate.determinant matrix ≠ 0)
    (inverseDenominator : Basic.denominator (BoundaryAdjugate.adjugate matrix) input ≠ 0) :
    Basic.homographic matrix (Basic.homographic (BoundaryAdjugate.adjugate matrix) input) = input := by
  have forwardDenominator := denominator_inverse_tail_ne matrix input
    determinantNonzero inverseDenominator
  calc
    Basic.homographic matrix (Basic.homographic (BoundaryAdjugate.adjugate matrix) input) =
        Basic.homographic (Coordinates2.Matrix.mul matrix (BoundaryAdjugate.adjugate matrix)) input :=
      (Composition.homographic_mul matrix (BoundaryAdjugate.adjugate matrix) input inverseDenominator
        forwardDenominator).symm
    _ = input := by
      rw [BoundaryAdjugate.mul_adjugate]
      unfold Basic.homographic Basic.numerator Basic.denominator
      rw [Data.Gaussian.Basic.zero_mul,
        Data.Gaussian.Basic.zero_add,
        Data.Gaussian.Basic.add_zero]
      calc
        BoundaryAdjugate.determinant matrix * input * (BoundaryAdjugate.determinant matrix)⁻¹ =
            input * (BoundaryAdjugate.determinant matrix * (BoundaryAdjugate.determinant matrix)⁻¹) := by
          rw [Data.Gaussian.Basic.mul_comm
              (BoundaryAdjugate.determinant matrix) input,
            Data.Gaussian.Basic.mul_assoc]
        _ = input := by
          rw [Data.Gaussian.Field.inv_eq,
            Data.Gaussian.Field.mul_inv _ determinantNonzero,
            Data.Gaussian.Basic.mul_one]
end Purelib.Geometry.Projective.Homography

end
