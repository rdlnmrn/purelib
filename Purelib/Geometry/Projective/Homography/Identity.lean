module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-! Identity homographies retain the original Gaussian point and a nonzero denominator. -/

public section

namespace Purelib.Geometry.Projective.Homography

/-- The affine denominator of the Gaussian identity matrix never vanishes. -/
theorem identityMatrix_denominator_ne (value :
  Data.Gaussian.Basic.Canonical) :
    Homography.Basic.denominator Coordinates2.Matrix.identityMatrix value ≠ 0 := by
  unfold Homography.Basic.denominator Coordinates2.Matrix.identityMatrix
  rw [Data.Gaussian.Basic.zero_mul,
    Data.Gaussian.Basic.zero_add]
  intro oneZero
  have realOneZero := congrArg
    Data.Gaussian.Basic.re oneZero
  exact Fraction.Field.zero_ne_one realOneZero.symm

/-- The homography defined by the identity matrix fixes every Gaussian rational. -/
theorem homographic_identityMatrix (value : Data.Gaussian.Basic.Canonical)
  :
    Homography.Basic.homographic Coordinates2.Matrix.identityMatrix value = value := by
  unfold Homography.Basic.homographic Homography.Basic.numerator Homography.Basic.denominator
    Coordinates2.Matrix.identityMatrix
  rw [Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.add_zero,
    Data.Gaussian.Basic.zero_mul,
    Data.Gaussian.Basic.zero_add, Data.Gaussian.Field.inv_eq,
    Data.Gaussian.Field.inv_one_direct,
    Data.Gaussian.Basic.mul_one]

end Purelib.Geometry.Projective.Homography
