module
import Purelib.Polynomial.RecursiveDense.Rational.Avoidance
public import Purelib.Polynomial.RecursiveDense.Rational.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial

@[expose] public section

/-!
# Rational rotations, Lemma 59: finite polynomial identity transfer

The paper's several-variable rational-point lemma is exposed here with its
literal hypotheses.  Its proof recursively uses only finite coefficient
lists and, in each remaining variable, the `degree + 1` displayed rational
points needed to rule out the product of two nonzero specializations.
-/

namespace Purelib.Polynomial.Multivariate.IdentityTransfer.PolynomialIdentity

/-- The finite recursively dense rational polynomial type, indexed by its displayed number of variables. -/
abbrev CoefficientExpression := RecursiveDense.Rational.Basic.Expression
/-- The exact rational coordinate tuple for the displayed number of variables. -/
abbrev Point := RecursiveDense.Rational.Basic.Point

/-- Lemma 59, with zero understood by the exact recursive coefficient test:
if `h` is nonzero and `g` vanishes at every rational point where `h` is
nonzero, then `g` is zero. -/
theorem lemmaFiftyNine {arity : Nat} (g h : CoefficientExpression arity)
    (hNonzero : h.isZero = false)
    (vanishes : ∀ point : Multivariate.IdentityTransfer.PolynomialIdentity.Point arity,
      h.eval point ≠ 0 → g.eval point = 0) :
    g.isZero = true :=
  RecursiveDense.Rational.Avoidance.isZero_of_vanishes_where_second_nonzero
    g h hNonzero vanishes

end Purelib.Polynomial.Multivariate.IdentityTransfer.PolynomialIdentity
