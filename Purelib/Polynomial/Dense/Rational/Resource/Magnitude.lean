module

public import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Data.Rat.Resource.List

import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Resource
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field

/-!
# Magnitude envelopes of retained rational coefficient lists
-/

namespace Purelib.Polynomial.Dense.Rational.Resource.Magnitude

open Purelib.Data.Rat
open Purelib.Polynomial

open Purelib
open Purelib.Algebra.Polynomial.DensePolynomial

public section

/-- The maximum rational resource magnitude of all coefficients and zero.

The finite fold retains a bound for every displayed coefficient, including the empty-list case. -/
@[expose] def coefficientMagnitude (polynomial : Dense.Rational.NormalizedPolynomial) : Nat :=
  polynomial.coeffs.foldl
    (fun bound value => max bound (Fraction.Resource.Model.rationalModel.magnitude value))
    (Fraction.Resource.Model.rationalModel.magnitude 0)

/-- Every displayed coefficient lies within the computed coefficient-magnitude bound. -/
theorem polynomial_within_coefficientMagnitude (polynomial : Dense.Rational.NormalizedPolynomial) :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel polynomial
      (Dense.Rational.Resource.Magnitude.coefficientMagnitude polynomial) := open Purelib in by
  intro candidate member
  exact Purelib.Data.Rat.Resource.List.member_le_foldl_max polynomial.coeffs _ member

/-- The resource magnitude of zero is bounded by the polynomial coefficient magnitude. -/
theorem zero_le_coefficientMagnitude (polynomial : Dense.Rational.NormalizedPolynomial) :
    Fraction.Resource.Model.rationalModel.magnitude 0 ≤ Dense.Rational.Resource.Magnitude.coefficientMagnitude
      polynomial :=
  open Purelib in Purelib.Data.Rat.Resource.List.foldl_max_le_final polynomial.coeffs _

end

end Purelib.Polynomial.Dense.Rational.Resource.Magnitude
