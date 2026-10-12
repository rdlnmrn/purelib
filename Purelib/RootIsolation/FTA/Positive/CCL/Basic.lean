module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

section
public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Positive.CCL.Basic

open Purelib.Polynomial
open Purelib.RootIsolation

set_option genInjectivity false in
/-- A positive-degree result retains an exact CCL terminal or a higher-degree active root family.

The linear constructor stores the original polynomial's exact terminal and
degree-one evidence. The higher constructor retains its complete adapter result
and the same polynomial's lower degree bound. -/
inductive PositiveResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- An exact finite CCL terminal for the original degree-one polynomial. -/ | terminal (state :
    Roots.CCL.Terminal p) (degree : p.natDegree = 1)
  /-- The original coupled degree-sized active root family for a polynomial of degree at least two. -/ | higher (result
    : FTA.Squarefree.AdapterResult p) (degree : 2 ≤ p.natDegree)

constructive_injectivity PositiveResult

end Purelib.RootIsolation.FTA.Positive.CCL.Basic

end
