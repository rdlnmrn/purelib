module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

namespace Purelib.Geometry.Projective.Chordal.Probe

/-- Exact rational squared chordal distance to the projective point at infinity. -/
def chordalOmegaProbe (point : GaussianLine) :
  Fraction.Rational :=
  Basic.chordalSq point (Proj.omega : GaussianLine)

/-- Squared chordal quadrance from the terminal point is nonnegative. -/
theorem chordalOmegaProbe_nonnegative (point :
  GaussianLine) :
    0 ≤ chordalOmegaProbe point :=
  Basic.chordalSq_nonneg point (Proj.omega : GaussianLine)

/-- A valid homogeneous point has terminal-point probe at most one. -/
theorem chordalOmegaProbe_le_one {point :
  GaussianLine}
    (valid : Proj.HasNonzeroCoordinate point) :
    chordalOmegaProbe point ≤ 1 :=
  Basic.chordalSq_le_one valid
    Proj.omega_hasNonzeroCoordinate

/-- The terminal-point probe is denominator squared norm divided by homogeneous weight. -/
public theorem chordalSq_omega_eq_weight (point :
  GaussianLine) :
    chordalOmegaProbe point =
      Basic.normSq point.q / Proj.weight point := by
  unfold chordalOmegaProbe
  rw [Basic.chordalSq_eq_cross]
  simp only [Proj.cross, Proj.omega,
    Data.Gaussian.Basic.mul_zero,
    Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.zero_sub,
    Basic.normSq_neg, Proj.weight, Basic.normSq_one,
      Basic.normSq_zero]
  congr 1
  ring1

/-- The two mixed coordinate-product squared norms are bounded by the weight product. -/
public theorem crossProductNorms_le_weightProduct (left right :
  GaussianLine) :
    Basic.normSq (left.q * right.p) + Basic.normSq (right.q *
      left.p) ≤
      Proj.weight left * Proj.weight right := by
  rw [Basic.normSq_mul, Basic.normSq_mul]
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Basic.normSq left.p * Basic.normSq right.p +
        Basic.normSq left.q * Basic.normSq right.q :=
      add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Basic.normSq_nonneg left.p) (Basic.normSq_nonneg right.p))
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          (Basic.normSq_nonneg left.q) (Basic.normSq_nonneg right.q))
    _ = Proj.weight left *
          Proj.weight right -
        (Basic.normSq left.q * Basic.normSq right.p +
          Basic.normSq right.q * Basic.normSq left.p) := by
      dsimp only [Proj.weight]
      ring1

end Purelib.Geometry.Projective.Chordal.Probe

end
