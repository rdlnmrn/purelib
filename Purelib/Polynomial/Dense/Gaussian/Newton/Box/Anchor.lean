module
public import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
public import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Newton updates at a retained box anchor

The original fixed rational anchor determines the normalized Newton
update, its Gaussian readback and the same squared displacement.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Executable Newton point based at the fixed rational anchor.

The original box anchor is passed to the normalized Newton update. Its
working Gaussian result is read back through the same value operation,
retaining the original polynomial and fixed rational anchor. -/
@[expose] public def anchorNewtonCenter (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (small : Box) :
  Gaussian.Basic.Canonical :=
  Gaussian.Basic.value
    (Dense.Gaussian.Newton.Basic.newtonCenter p small.anchor)

/-- The retained box-anchor Newton center is the anchor minus its normalized Newton quotient.

Reading the retained normalized Newton update subtracts the original
polynomial value divided by its derivative value from the same anchor.
The Gaussian derivative is the original dense derivative specialization. -/
@[simp] public theorem anchorNewtonCenter_eq
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (small : Box) :
    anchorNewtonCenter p small =
      small.anchor - p.eval small.anchor /
        (Dense.Gaussian.GCD.derivative p).eval small.anchor := by
  change Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p small.anchor) =
    small.anchor - p.eval small.anchor / (Dense.Derivative.derivative p).eval small.anchor
  exact Dense.Gaussian.Newton.Basic.value_newtonCenter p small.anchor

/-- For nonzero anchor derivative, the squared Newton displacement is residual quadrance divided by derivative
quadrance.

At a nonzero derivative value, the original Newton displacement is the
negative quotient of polynomial and derivative values at the same anchor.
Its norm square is therefore the same residual quadrance multiplied by
the inverse derivative quadrance. -/
public theorem normSq_anchorNewtonCenter_sub_anchor
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {small : Box}
    (derivativeNonzero :
      (Dense.Gaussian.GCD.derivative p).eval small.anchor ≠ 0) :
    Gaussian.Norm.Basic.normSq (anchorNewtonCenter p small - small.anchor) =
      Gaussian.Norm.Basic.normSq (p.eval small.anchor) *
        (Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval small.anchor))⁻¹ := by
  have displacement : anchorNewtonCenter p small - small.anchor =
      -(p.eval small.anchor /
        (Dense.Gaussian.GCD.derivative p).eval small.anchor) := by
    rw [anchorNewtonCenter_eq]
    rw [Gaussian.Basic.sub_eq_add_neg,
      Gaussian.Basic.sub_eq_add_neg]
    ring1
  rw [displacement, Gaussian.Norm.Basic.normSq_neg,
    Gaussian.Field.normSq_div _ _ derivativeNonzero]

end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
