import mathlib.RFAP.FiniteMultivariatePolynomial

/-!
# Rational rotations, Lemma 59: finite polynomial identity transfer

The paper's several-variable rational-point lemma is exposed here with its
literal hypotheses.  Its proof recursively uses only finite coefficient
lists and, in each remaining variable, the `degree + 1` displayed rational
points needed to rule out the product of two nonzero specializations.
-/

namespace RationalRotations.PolynomialIdentity

abbrev Polynomial := RFAP.FiniteMultivariatePolynomial.Polynomial
abbrev Point := RFAP.FiniteMultivariatePolynomial.Point

/-- Lemma 59, with zero understood by the exact recursive coefficient test:
if `h` is nonzero and `g` vanishes at every rational point where `h` is
nonzero, then `g` is zero. -/
theorem lemmaFiftyNine {arity : Nat} (g h : Polynomial arity)
    (hNonzero : h.isZero = false)
    (vanishes : ∀ point : Point arity,
      h.eval point ≠ 0 → g.eval point = 0) :
    g.isZero = true :=
  RFAP.FiniteMultivariatePolynomial.isZero_of_vanishes_where_second_nonzero
    g h hNonzero vanishes

end RationalRotations.PolynomialIdentity
