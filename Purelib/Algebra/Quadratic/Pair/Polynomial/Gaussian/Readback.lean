module

public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian

/-!
# Cached scalar readbacks of original quadratic expressions

The original denominator guard and selected generator equation remain
retained. Construction consumes a certified scalar pair directly when its
coefficient factors have already been computed by the original source.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Algebra.Quadratic.Pair
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- Retain an original expression using its supplied cached scalar pair and original selected generator.

The readback certificate concerns this exact expression and point. The
original domain guard and power identity are preserved, and the numerical
channel uses the original Gaussian pair interpretation without evaluating
the expression's coefficient tables again. -/
@[expose] def retainValue {radicand : Coefficients} (original : Expression radicand)
    (point : Canonical) (generator : CoherentNamed) (defined : original.Defined point)
    (identity : PowerIdentity generator 2 (radicand.eval point)) (value : Pair Canonical (-radicand.eval point))
    (readback : value = original.evaluate point) : Denotation original point generator :=
  ⟨original, rfl, defined, identity, value, readback, Gaussian.denote id generator value, rfl⟩

/-- The retained original denotation consumes precisely the supplied scalar pair cache. -/
theorem retainValue_value {radicand : Coefficients} (original : Expression radicand)
    (point : Canonical) (generator : CoherentNamed) (defined : original.Defined point)
    (identity : PowerIdentity generator 2 (radicand.eval point)) (value : Pair Canonical (-radicand.eval point))
    (readback : value = original.evaluate point) :
    (retainValue original point generator defined identity value readback).value = value := rfl

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

end
