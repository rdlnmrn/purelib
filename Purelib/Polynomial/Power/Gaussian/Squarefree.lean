module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Bezout
public import Purelib.Polynomial.Squarefree.Bezout.Evaluation

open Purelib.Data

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Polynomial.Power.Gaussian.Squarefree

open Purelib.Data.Gaussian

/-- Every displayed nonzero parameter gives a squarefree power polynomial,
with no discriminant, completed roots, or carrier-level argument. -/
def squarefree {parameter : Gaussian.Basic.Canonical}
  (parameterNonzero : parameter ≠ 0)
    (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) :=
  Squarefree.Bezout.Evaluation.squarefreeOfEvalBezout (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
    degree)
    (Power.Gaussian.Bezout.polynomial_nonzero parameter degree)
    (Power.Gaussian.Bezout.bezoutLeft parameter) (Power.Gaussian.Bezout.bezoutRight parameter degree)
    (Power.Gaussian.Bezout.bezout_identity parameterNonzero degree)
end Purelib.Polynomial.Power.Gaussian.Squarefree

end
