module
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.FTA.Squarefree.Input

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box-only finite constructive FTA

This is the paper-facing numerical layer over the explicit constructive
fraction and Gaussian representations.  The squarefree certificate is finite
dense extended-Euclid data.  Both axis eliminants are computed internally by
the fraction-free separated Sylvester construction.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

/-- Standalone choice-free box-only finite RFAP. -/
def prove {p :
  CoefficientPolynomial} (input :
  FTA.Squarefree.Input p) : FTA.Squarefree.BoxResult p where
  isolation := input.isolation
  ownership := fun track supported =>
    Exact.Ownership.Prepare.selectOutputOwner
      input.degreeAtLeastTwo input.squarefree input.elimination
      input.isolation track supported
  maximality := input.familyCardLe

/-- Degree-greater-than-one specialization with an explicit finite
squarefree certificate.  A later irreducibility wrapper may compute this
certificate, but the trusted numerical theorem needs no sparse or
infinite-root interface. -/
def proveDegreeGtOne
    {p : CoefficientPolynomial} (squarefree :
      Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : FTA.Squarefree.BoxResult p :=
  prove { squarefree := squarefree, degreeAtLeastTwo := degree }
end Purelib.RootIsolation.FTA.Squarefree.Build.BoxFTA

end
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

namespace Purelib.RootIsolation.FTA.Squarefree.Build.Box

/-- Choice-free degree-many box isolation equipped with finite CCL requests. -/
def prove {p :
  CoefficientPolynomial}
    (input : RootIsolation.FTA.Squarefree.Input p) : FTA.Squarefree.AdapterResult p :=
  ⟨FTA.Squarefree.Build.BoxFTA.prove input⟩

/-- Degree-greater-than-one specialization from explicit finite squarefree
Bézout data. -/
def proveDegreeGtOne {p :
  CoefficientPolynomial}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : FTA.Squarefree.AdapterResult p :=
  prove ⟨squarefree, degree⟩
end Purelib.RootIsolation.FTA.Squarefree.Build.Box

end

