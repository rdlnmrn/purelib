module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Gaussian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib
open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Line.Hermitian

namespace Proj

/-- Squared Euclidean weight of a homogeneous coordinate pair.

The exact squared norms of the retained numerator and denominator are added in their original rational carrier. -/
@[expose] def weight (x : GaussianLine) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq x.p + Data.Gaussian.Norm.Basic.normSq x.q

/-- The Hermitian scalar product used in the rational quadrance estimates.

The two retained coordinate products use conjugation of the first pair and the original Gaussian addition and
multiplication operations. -/
@[expose] def hermitian (x y : GaussianLine) : Gaussian.Basic.Canonical :=
  Data.Gaussian.Basic.conj x.p * y.p + Data.Gaussian.Basic.conj x.q * y.q

/-- The alternating product in the numerator of `chordalSq`.

The original ordered homogeneous pairs determine the signed cross product without normalization or a choice of
representative. -/
@[expose] def cross (x y : GaussianLine) : Gaussian.Basic.Canonical :=
  x.p * y.q - y.p * x.q

/-- The sum of the coordinate squared norms is nonnegative.

Each retained coordinate has nonnegative squared norm, so their exact original sum has the same bound. -/
theorem weight_nonneg (x : GaussianLine) : 0 ≤ (Proj.weight x) :=
  add_nonneg (Gaussian.Norm.Basic.normSq_nonneg x.p) (Gaussian.Norm.Basic.normSq_nonneg x.q)

/-- A valid homogeneous pair has strictly positive weight.

One retained homogeneous coordinate has strictly positive squared norm. The other coordinate contributes a nonnegative
squared norm, so the same original sum is strictly positive in either validity case. -/
theorem weight_pos {x : GaussianLine} (valid :
  (Geometry.Projective.Line.Gaussian.Proj.HasNonzeroCoordinate x)) :
    0 < (Proj.weight x) := by
  rcases valid with hp | hq
  · exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (Gaussian.Norm.Basic.normSq_pos hp)
      (Gaussian.Norm.Basic.normSq_nonneg x.q)
  · exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Gaussian.Norm.Basic.normSq_nonneg x.p)
      (Gaussian.Norm.Basic.normSq_pos hq)

/-- The two-dimensional complex Lagrange identity.

The identity expands the retained Hermitian and alternating products in the original Gaussian coordinates, with the
exact product of homogeneous weights on the right. -/
theorem normSq_hermitian_add_normSq_cross (x y : GaussianLine) :
    Data.Gaussian.Norm.Basic.normSq ((Proj.hermitian x) y) + Data.Gaussian.Norm.Basic.normSq ((Proj.cross x) y)
      =
      (Proj.weight x) * (Proj.weight y) := by
  simp only [Proj.hermitian, Proj.cross, Proj.weight, Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.conj,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im]
  ring1

/-- The Hermitian product squared norm is bounded by the product of the two weights.

The Lagrange identity leaves the nonnegative squared norm of the alternating product as the remainder. Both original
homogeneous pairs remain fixed. -/
theorem normSq_hermitian_le_weight_mul (x y : GaussianLine) :
    Data.Gaussian.Norm.Basic.normSq ((Proj.hermitian x) y) ≤ (Proj.weight x) * (Proj.weight y) := by
  rw [← Proj.normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_right (Gaussian.Norm.Basic.normSq_nonneg ((Proj.cross x) y))

/-- Determinant expansion through a third homogeneous coordinate pair.

The original cross and Hermitian products retain the order of all three inputs. Scalar coordinate expansion verifies the
exact Gaussian identity. -/
theorem cross_mul_weight (x y z : GaussianLine) :
    (Proj.cross x) z * ⟨(Proj.weight y), 0⟩ =
      (Proj.cross x) y * (Proj.hermitian y) z + (Proj.cross y) z * (Proj.hermitian y) x := by
  apply Gaussian.Basic.ext <;>
    simp only [Proj.cross, Proj.weight, Proj.hermitian, Data.Gaussian.Norm.Basic.normSq,
      Data.Gaussian.Basic.conj,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
    ring1

end Proj

/-- Scaling a homogeneous pair multiplies its weight by the scalar squared norm.

Both retained homogeneous coordinates are multiplied by the same original Gaussian scalar. Multiplicativity of each
squared norm gives the common scalar factor. -/
theorem Proj.weight_scale (scalar : Gaussian.Basic.Canonical) (x : GaussianLine) :
    (Proj.weight (Geometry.Projective.Line.Gaussian.Proj.scale scalar x)) = Data.Gaussian.Norm.Basic.normSq scalar *
      (Proj.weight x) := by
  simp only [Geometry.Projective.Line.Gaussian.Proj.scale, Proj.weight, Gaussian.Norm.Basic.normSq_mul]
  ring1
end Purelib.Geometry.Projective.Line.Hermitian
