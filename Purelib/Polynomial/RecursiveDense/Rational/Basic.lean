module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Basic
public import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib

section
public section

/-!
# Indexed recursively dense rational polynomials

A zero-arity polynomial retains a scalar. Each successor arity retains a
finite descending sequence of polynomials in the preceding variables.
The mutually indexed coefficient owner supports exact Boolean zero tests
and inner-first Horner evaluation at the original rational coordinate tuple.
-/

namespace Purelib.Polynomial.RecursiveDense.Rational.Basic
/-- Univariate dense polynomials over the constructive rationals. -/
abbrev DensePolynomial :=
  Dense.Basic.DensePolynomial Fraction.Rational

/- Finite recursively dense polynomials in exactly the displayed number of
variables.  `Coefficients` is a project-owned finite list constructor so the
kernel sees the mutual recursion directly, without a nested inductive. -/
set_option genInjectivity false in
mutual
  /-- A rational polynomial represented recursively by its finite number of variables.

Arity zero stores a scalar; each successor arity stores a finite descending coefficient sequence of polynomials in the
preceding variables. -/
  inductive Expression : Nat → Type
    /-- Store a rational constant in zero variables. -/ | constant : Fraction.Rational →
      Expression 0
    /-- Add an outer variable with the supplied descending coefficient sequence. -/ | next {arity : Nat} :
      Purelib.Polynomial.RecursiveDense.Rational.Basic.Coefficients arity →
      Expression (arity + 1)

  /-- A finite descending sequence of recursively dense polynomial coefficients.

The explicit list constructors make mutual structural recursion visible to the kernel. -/
  inductive Coefficients : Nat → Type
    /-- The empty coefficient sequence at the given arity. -/ | nil {arity : Nat} :
      Purelib.Polynomial.RecursiveDense.Rational.Basic.Coefficients arity
    /-- Prepend a polynomial coefficient of the same arity to a finite sequence. -/ | cons {arity : Nat} :
      Expression arity → Purelib.Polynomial.RecursiveDense.Rational.Basic.Coefficients arity →
        Purelib.Polynomial.RecursiveDense.Rational.Basic.Coefficients arity
end

constructive_injectivity Expression

constructive_injectivity Coefficients

namespace Coefficients

/-- Forget the recursive list wrapper after its finiteness has been made
kernel-visible. -/
@[expose] def toList {arity : Nat} :
    Coefficients arity → List (Expression arity)
  | .nil => []
  | .cons coefficient remaining => coefficient :: remaining.toList

end Coefficients

namespace Coefficients

/-- Build a recursive coefficient sequence from an ordinary finite list. -/
@[expose] def ofList {arity : Nat} :
    List (Expression arity) → Coefficients arity
  | [] => .nil
  | coefficient :: remaining =>
      .cons coefficient (Purelib.Polynomial.RecursiveDense.Rational.Basic.Coefficients.ofList remaining)

end Coefficients

/-- A rational point with exactly the displayed finite number of
coordinates. -/
@[expose] def Point : Nat → Type
  | 0 => Unit
  | arity + 1 => Purelib.Polynomial.RecursiveDense.Rational.Basic.Point arity × Fraction.Rational

/- Exact finite zero tests: every recursively displayed coefficient must
vanish.  Representation-only leading zero coefficients do not affect them. -/
mutual

/-- Test whether all recursively stored scalar coefficients are zero.

The finite recursive traversal ignores representational leading zeros and returns a Boolean. -/
  @[expose] def Expression.isZero : {arity : Nat} → Expression arity → Bool
    | _, .constant coefficient => decide (coefficient = 0)
    | _, .next coefficients => coefficients.isZero

/-- Test that every polynomial in a finite coefficient sequence is zero.

The empty sequence passes; each nonempty sequence combines the current coefficient test with the remaining sequence. -/
  @[expose] def Coefficients.isZero {arity : Nat} : Coefficients arity → Bool
    | .nil => true
    | .cons coefficient remaining =>
        coefficient.isZero && remaining.isZero

end

/- Horner evaluation, inner coordinates first and the last coordinate
outermost. -/
mutual

/-- Evaluate a recursively dense polynomial at a point of the same arity.

Inner coordinates evaluate coefficients first; the final coordinate supplies the outer Horner variable. -/
  @[expose] def Expression.eval : {arity : Nat} →
      Expression arity → Point arity → Fraction.Rational
    | _, .constant coefficient, _ => coefficient
    | _, .next coefficients, (inner, outer) =>
        coefficients.eval inner outer 0

/-- Evaluate a descending coefficient sequence by accumulated Horner evaluation.

Each step multiplies the accumulator by the outer coordinate and adds the current coefficient evaluated at the inner
point. -/
  @[expose] def Coefficients.eval {arity : Nat} : Coefficients arity →
      Point arity → Fraction.Rational → Fraction.Rational → Fraction.Rational
    | .nil, _, _, value => value
    | .cons coefficient remaining, inner, outer, value =>
        remaining.eval inner outer
          (value * outer + coefficient.eval inner)

end
end Purelib.Polynomial.RecursiveDense.Rational.Basic

end
