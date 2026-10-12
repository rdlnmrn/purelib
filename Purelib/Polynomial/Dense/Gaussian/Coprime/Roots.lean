module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Roots

/-! ## Pairwise separation witnesses for exact and track sites -/

/-- Two displayed exact roots of coprime factors are distinct. -/
theorem exactPoints_ne
    {p q : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (coprime :
      Dense.Gaussian.Coprime.Basic.CoprimeCertificate p q)
    {left right : Gaussian.Basic.Canonical}
    (leftRoot : p.eval left = 0) (rightRoot : q.eval right = 0) :
    left ≠ right := by
  intro equal
  subst right
  rcases coprime.eval_ne_zero left with leftNonzero | rightNonzero
  · exact leftNonzero leftRoot
  · exact rightNonzero rightRoot

end Purelib.Polynomial.Dense.Gaussian.Coprime.Roots

end
