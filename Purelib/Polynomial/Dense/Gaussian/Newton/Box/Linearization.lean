module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization

/-- The affine first-order term, centered at the exact rational Newton point
of the fixed source anchor. -/
def newtonLinearization (p :
  CoefficientPolynomial) (source : Box) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Linear.Affine.affineCoordinate ((Dense.Gaussian.GCD.derivative p).eval source.anchor)
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)

/-- The remaining finite coefficient program. -/
def newtonError (p :
  CoefficientPolynomial) (source : Box) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  p.normalize - newtonLinearization p source

/-- The affine term and its coefficientwise Newton error restore the exact
normalized finite coefficient list in degree at least two. -/
theorem newtonLinearization_add_error_eq_normalize
    {p : CoefficientPolynomial} (degreeAtLeastTwo : 2 ≤
      p.natDegree)
    (source : Box)
    (derivativeNonzero :
      (Dense.Gaussian.GCD.derivative p).eval source.anchor ≠ 0) :
    newtonLinearization p source +
      newtonError p source = p.normalize := by
  let slope := (Dense.Gaussian.GCD.derivative p).eval source.anchor
  let center := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source
  have polynomialNonzero : p.isZero = false :=
    Dense.Gaussian.Degree.Linear.isZero_false_of_natDegree_pos
      ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)
  rw [newtonError, newtonLinearization,
    Dense.Gaussian.Linear.Affine.affineCoordinate_eq_linear derivativeNonzero center]
  exact Dense.Basic.DensePolynomial.linear_add_sub_linear_of_normalized
    (Dense.Basic.DensePolynomial.normalize_normalize p) (by simpa using polynomialNonzero)
    (by simpa using degreeAtLeastTwo) derivativeNonzero

/-- The Newton-centered affine program is exactly the ordinary first-order
Taylor expression at the source anchor. -/
theorem newtonLinearization_eval
    (p : CoefficientPolynomial) (source : Box) (z :
      Gaussian.Basic.Canonical)
    (derivativeNonzero :
      (Dense.Gaussian.GCD.derivative p).eval source.anchor ≠ 0) :
    (newtonLinearization p source).eval z =
      p.eval source.anchor +
        (Dense.Gaussian.GCD.derivative p).eval source.anchor *
          (z - source.anchor) := open Purelib.Algebra.Field in by
  let slope := (Dense.Gaussian.GCD.derivative p).eval source.anchor
  let value := p.eval source.anchor
  rw [newtonLinearization, Dense.Gaussian.Linear.Affine.affineCoordinate_eval]
  rw [Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter_eq]
  change slope * (z - (source.anchor - value / slope)) =
    value + slope * (z - source.anchor)
  calc
    slope * (z - (source.anchor - value / slope)) =
        slope * (z - source.anchor) + slope * (value / slope) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
        ring1
    _ = slope * (z - source.anchor) + value := by
      rw [Gaussian.Basic.mul_comm slope (value / slope),
        ExplicitField.div_mul_cancel value derivativeNonzero]
    _ = value + slope * (z - source.anchor) :=
      Gaussian.Basic.add_comm _ _
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization

end
