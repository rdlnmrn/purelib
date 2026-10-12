module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Chordal.Equivalence

/-- `χ²` is unchanged by a nonzero rescaling of the left homogeneous coordinate pair. -/
theorem chordalSq_scale_left (scalar :
  Data.Gaussian.Basic.Canonical) (scalarNonzero : scalar ≠ 0)
    (x y : Line.GaussianLine) : Chordal.Basic.chordalSq (Proj.scale scalar x) y =
      Chordal.Basic.chordalSq x y := by
  have normNonzero : Data.Gaussian.Norm.Basic.normSq scalar ≠ 0 :=
    fun normZero => scalarNonzero (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp normZero)
  have crossIdentity :
      (Proj.cross (Proj.scale scalar x)) y = scalar * (Proj.cross x) y := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Proj.cross, Proj.scale, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
      ring1
  rw [Chordal.Basic.chordalSq_eq_cross, Chordal.Basic.chordalSq_eq_cross, crossIdentity,
    Data.Gaussian.Norm.Basic.normSq_mul,
    Proj.weight_scale]
  rw [show (Data.Gaussian.Norm.Basic.normSq scalar * (Proj.weight x)) * (Proj.weight y) =
    Data.Gaussian.Norm.Basic.normSq scalar * ((Proj.weight x) * (Proj.weight y)) by ring1]
  exact Fraction.Field.mul_div_mul_left_direct
    (Data.Gaussian.Norm.Basic.normSq scalar) (Data.Gaussian.Norm.Basic.normSq ((Proj.cross x) y))
      ((Proj.weight x) * (Proj.weight y)) normNonzero

/-- `χ²` is unchanged by a nonzero rescaling of the right homogeneous coordinate pair. -/
theorem chordalSq_scale_right (scalar :
  Data.Gaussian.Basic.Canonical) (scalarNonzero : scalar ≠ 0)
    (x y : Line.GaussianLine) : Chordal.Basic.chordalSq x (Proj.scale scalar y) =
      Chordal.Basic.chordalSq x y := by
  rw [Chordal.Basic.chordalSq_comm, chordalSq_scale_left scalar scalarNonzero,
    Chordal.Basic.chordalSq_comm]

/-- Replacing the left valid homogeneous pair by an equivalent valid pair preserves chordal quadrance. -/
theorem chordalSq_eq_of_equivalent_left {x y :
  Line.GaussianLine}
    (xValid : (Proj.HasNonzeroCoordinate x)) (yValid : (Proj.HasNonzeroCoordinate y))
    (equivalent : x.Equivalent y) (z : Line.GaussianLine) :
    Chordal.Basic.chordalSq x z = Chordal.Basic.chordalSq y z := by
  rcases Proj.exists_nonzero_scale_of_equivalent xValid yValid equivalent with
    ⟨scalar, scalarNonzero, rfl⟩
  exact chordalSq_scale_left scalar scalarNonzero y z

/-- Replacing the right valid homogeneous pair by an equivalent valid pair preserves chordal quadrance. -/
theorem chordalSq_eq_of_equivalent_right {x y :
  Line.GaussianLine}
    (xValid : (Proj.HasNonzeroCoordinate x)) (yValid : (Proj.HasNonzeroCoordinate y))
    (equivalent : x.Equivalent y) (z : Line.GaussianLine) :
    Chordal.Basic.chordalSq z x = Chordal.Basic.chordalSq z y := by
  rw [Chordal.Basic.chordalSq_comm z x, Chordal.Basic.chordalSq_comm z y]
  exact chordalSq_eq_of_equivalent_left xValid yValid equivalent z
end Purelib.Geometry.Projective.Chordal.Equivalence

end
