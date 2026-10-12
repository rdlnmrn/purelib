module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree

set_option genInjectivity false in
/-- A nonzero normalized squarefree polynomial, which may be constant. -/
structure Part where
  /-- The retained Gaussian-rational polynomial. -/ polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- Its coefficient representation is already normalized. -/ normalized : polynomial.normalize = polynomial
  /-- The retained polynomial is nonzero. -/ nonzero : polynomial.isZero = false
  /-- The squarefree certificate for this exact polynomial. -/ squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial

constructive_injectivity Part

namespace Part.Factor

/-- Forget the positive-degree field of a certified squarefree factor.

The same polynomial, normalization, nonzero proof and squarefree certificate are retained. -/
def toPart (factor :
  Dense.Gaussian.Squarefree.Decomposition.Basic.Factor) : Part :=
  { polynomial := factor.polynomial
    normalized := factor.normalized
    nonzero := factor.nonzero
    squarefree := factor.squarefree }

end Part.Factor

namespace Part

/-- Promote a squarefree part using a supplied positive-degree proof.

All existing polynomial data and certificates are reused unchanged. -/
def toFactor (part : Part)
  (degreePositive : 0 < part.polynomial.natDegree) :
    Dense.Gaussian.Squarefree.Decomposition.Basic.Factor :=
  { polynomial := part.polynomial
    normalized := part.normalized
    nonzero := part.nonzero
    degreePositive := degreePositive
    squarefree := part.squarefree }

end Part

end Purelib.Polynomial.Dense.Gaussian.Squarefree

end
