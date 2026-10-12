module
import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Positive.Build
public import Purelib.RootIsolation.FTA.Positive.CCL.Basic
import Purelib.RootIsolation.FTA.Positive.Input
public import Purelib.RootIsolation.Roots.CCL.Terminal.Build
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Positive.CCL.Build

/-- Integrate exact linear terminals with the box/CCL family constructor. -/
def provePositive {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput p) : FTA.Positive.CCL.Basic.PositiveResult p :=
  match FTA.Positive.Build.provePositive input with
  | .linear root degree => .terminal (Roots.CCL.Terminal.Build.terminalOfExactRoot root) degree
  | .higher boxes degree => .higher ⟨boxes⟩ degree

/-- Degree-greater-than-one specialization of the unified result. -/
def provePositiveDegreeGtOne
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : FTA.Positive.CCL.Basic.PositiveResult p :=
  .higher (FTA.Squarefree.Build.Box.proveDegreeGtOne squarefree degree) degree

end Purelib.RootIsolation.FTA.Positive.CCL.Build

end
