module

-- Public edge equations retain their Gaussian and rational polynomial owners.
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
public import Purelib.Polynomial.Dense.Rational.Linear.Translated
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Translated
import Purelib.Polynomial.Dense.Rational.Constants.RawLinear

/-!
# Translated coordinates on finite box edges

Affine substitution into the retained translated Gaussian coordinate produces
two exact rational coefficient tables. The fixed edge position supplies a
constant component and the varying coordinate supplies a translated monic one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.Translated

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Path.Box
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- The real component of the translated coordinate polynomial on a horizontal edge.

The exact dense coefficient representation is the coordinate minus the center's real component; the edge endpoints do
not affect this component polynomial. -/
public theorem translated_horizontal_real
    (c : Canonical) (y a b : Fraction.Rational) :
    (Sides.horizontalEdge (Linear.Translated.translatedCoordinate c) y a b).realPart =
      Rational.Linear.Translated.affineVariable c.re := by
  change Components.realPart (Substitution.Affine.composeLine (Linear.Translated.translatedCoordinate c)
      (Cast.Imaginary.horizontalBase y) Purelib.Data.Gaussian.Constants.horizontalDirection) =
        Rational.Linear.Translated.affineVariable c.re
  rw [Substitution.Affine.Translated.composeLine_translatedCoordinate c
    (Cast.Imaginary.horizontalBase y) Purelib.Data.Gaussian.Constants.horizontalDirection (by
      intro equal
      have real := congrArg (fun z : Canonical => z.re) equal
      change (1 : Fraction.Rational) = 0 at real
      exact (Ne.symm Fraction.Field.zero_ne_one) real)]
  apply DensePolynomial.ext
  change [1, (0 : Fraction.Rational) - c.re] = [1, -c.re]
  rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct, _root_.zero_add]
  exact Eq.refl _

/-- The imag component of the translated coordinate polynomial on a horizontal edge.

The exact dense coefficient representation is the line height minus the center's imaginary component; the edge endpoints
do not affect this component polynomial. -/
public theorem translated_horizontal_imag
    (c : Canonical) (y a b : Fraction.Rational) :
    (Sides.horizontalEdge (Linear.Translated.translatedCoordinate c) y a b).imagPart =
      Rational.Constants.RawLinear.rawConstant (y - c.im) := by
  change Components.imagPart (Substitution.Affine.composeLine (Linear.Translated.translatedCoordinate c)
      (Cast.Imaginary.horizontalBase y) Purelib.Data.Gaussian.Constants.horizontalDirection) =
        Rational.Constants.RawLinear.rawConstant (y - c.im)
  rw [Substitution.Affine.Translated.composeLine_translatedCoordinate c
    (Cast.Imaginary.horizontalBase y) Purelib.Data.Gaussian.Constants.horizontalDirection (by
      intro equal
      have real := congrArg (fun z : Canonical => z.re) equal
      change (1 : Fraction.Rational) = 0 at real
      exact (Ne.symm Fraction.Field.zero_ne_one) real)]
  rfl

/-- The real component of the translated coordinate polynomial on a vertical edge.

The exact dense coefficient representation is the line position minus the center's real component; the edge endpoints do
not affect this component polynomial. -/
public theorem translated_vertical_real
    (c : Canonical) (x a b : Fraction.Rational) :
    (Sides.verticalEdge (Linear.Translated.translatedCoordinate c) x a b).realPart =
      Rational.Constants.RawLinear.rawConstant (x - c.re) := by
  change Components.realPart (Substitution.Affine.composeLine (Linear.Translated.translatedCoordinate c)
      (Cast.Winding.verticalBase x) Purelib.Data.Gaussian.Constants.imaginaryUnit) =
        Rational.Constants.RawLinear.rawConstant (x - c.re)
  rw [Substitution.Affine.Translated.composeLine_translatedCoordinate c
    (Cast.Winding.verticalBase x) Purelib.Data.Gaussian.Constants.imaginaryUnit (by
      intro equal
      have imaginary := congrArg (fun z : Canonical => z.im) equal
      change (1 : Fraction.Rational) = 0 at imaginary
      exact (Ne.symm Fraction.Field.zero_ne_one) imaginary)]
  apply DensePolynomial.ext
  exact Eq.refl _

/-- The imag component of the translated coordinate polynomial on a vertical edge.

The exact dense coefficient representation is the coordinate minus the center's imaginary component; the edge endpoints
do not affect this component polynomial. -/
public theorem translated_vertical_imag
    (c : Canonical) (x a b : Fraction.Rational) :
    (Sides.verticalEdge (Linear.Translated.translatedCoordinate c) x a b).imagPart =
      Rational.Linear.Translated.affineVariable c.im := by
  change Components.imagPart (Substitution.Affine.composeLine (Linear.Translated.translatedCoordinate c)
      (Cast.Winding.verticalBase x) Purelib.Data.Gaussian.Constants.imaginaryUnit) =
        Rational.Linear.Translated.affineVariable c.im
  rw [Substitution.Affine.Translated.composeLine_translatedCoordinate c
    (Cast.Winding.verticalBase x) Purelib.Data.Gaussian.Constants.imaginaryUnit (by
      intro equal
      have imaginary := congrArg (fun z : Canonical => z.im) equal
      change (1 : Fraction.Rational) = 0 at imaginary
      exact (Ne.symm Fraction.Field.zero_ne_one) imaginary)]
  apply DensePolynomial.ext
  change [1, (0 : Fraction.Rational) - c.im] = [1, -c.im]
  rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct, _root_.zero_add]
  exact Eq.refl _

end Purelib.Polynomial.Dense.Gaussian.Path.Box.Translated
