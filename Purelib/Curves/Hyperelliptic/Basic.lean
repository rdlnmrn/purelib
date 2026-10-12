module

import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Basic

/-- The two finite degree cases that give genus `g`. -/
inductive HyperellipticDegreeShape
    (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (genus : Nat) : Type
  /-- The defining polynomial has odd degree twice the genus plus one. -/ | odd (degree_eq : polynomial.natDegree = 2 *
    genus + 1)
  /-- The defining polynomial has even degree twice the genus plus two. -/ | even (degree_eq : polynomial.natDegree = 2
    * genus + 2)

set_option genInjectivity false in
/-- Executable squarefree input data for a genus-`g` hyperelliptic curve. -/
structure HyperellipticCurve (genus : Nat) where
  /-- The executable Gaussian polynomial defining the equation y squared equals f(x). -/ polynomial :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The defining polynomial is not the zero polynomial. -/ nonzero : polynomial.isZero = false
  /-- The retained executable squarefree certificate for the defining polynomial. -/ squarefree :
    Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial
  /-- The polynomial degree has one of the two displayed shapes for this genus. -/ degreeShape :
    HyperellipticDegreeShape polynomial genus

constructive_injectivity Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve

end Purelib.Curves.Hyperelliptic.Basic

end
