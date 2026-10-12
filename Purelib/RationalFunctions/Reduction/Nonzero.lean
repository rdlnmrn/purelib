module

import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Reduction.Basic
import Purelib.RationalFunctions.Reduction.Factorization
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Common finite outer square for a reduced rational function

The two nonzero reduced cofactors share one coefficient-computed rational
square.  Their constructive polynomial windings give the quotient's degree
difference directly, including constant and linear cofactors.
-/

namespace Purelib.RationalFunctions.Reduction.Nonzero

open Purelib.Polynomial in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- A retained rational-function reduction with a nonzero reduced numerator.

The reduction already contains nonzeroness of the original denominator. Its factorization supplies nonzeroness of the
reduced denominator as well. -/
structure NonzeroReducedInput
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The retained cancellation result for the indexed original polynomial pair. -/ reduction :
    Reduction.Basic.ReducedPair numerator denominator
  /-- The numerator cofactor in the retained reduction is nonzero. -/ numeratorReducedNonzero :
    reduction.numeratorReduced.isZero = false

constructive_injectivity NonzeroReducedInput

namespace NonzeroReducedInput

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- The denominator cofactor in the retained reduction is nonzero. -/
theorem denominatorReducedNonzero
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) :
    input.reduction.denominatorReduced.isZero = false :=
  input.reduction.denominatorReduced_nonzero
end NonzeroReducedInput

end Purelib.RationalFunctions.Reduction.Nonzero

end
