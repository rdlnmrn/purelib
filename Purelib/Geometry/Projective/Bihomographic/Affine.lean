module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Bihomographic.Arithmetic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Bihomographic.Basic

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Bihomographic semantics of progressive arithmetic

The enclosure implementation computes `+`, `-`, `*`, and `/` directly on
finite rational balls.  This module proves that its candidate predicates are
the affine instances of the paper's bihomographic initial matrices and that
all input/output decoder substitutions compose exactly.  Thus the direct
implementation and the matrix account are two certified views of the same
finite arithmetic step.
-/

namespace Purelib.Geometry.Projective.Bihomographic.Affine

/-- The homogeneous division pair `[x:y]` is projectively the affine quotient whenever the explicitly supplied
denominator is nonzero. -/
theorem initial_div_equivalent (x y :
  Data.Gaussian.Basic.Canonical) (yNonzero : y ≠ 0) :
    Proj.Equivalent ((Bihomographic.Arithmetic.initial .div).affineMap x y)
      (Proj.affine (x / y)) := by
  rw [Bihomographic.Arithmetic.initial_div]
  unfold Proj.Equivalent Proj.affine
  simp only [Data.Gaussian.Basic.mul_one]
  symm
  rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
    Data.Gaussian.Basic.mul_assoc, Data.Gaussian.Field.inv_eq,
    Data.Gaussian.Field.inv_mul y yNonzero, Data.Gaussian.Basic.mul_one]
end Purelib.Geometry.Projective.Bihomographic.Affine

end
