module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

public section

/-!
# Owners of the reciprocal cap's actual regular-factor model

The retained polynomial model determines each operational root through its
sheet-consistent finite Newton samples. The attached winding owner names that
same channel. The actual collar fiber selects the endpoint; the quotient
coordinate then matches its reciprocal root to this regular model root.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Data)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

set_option genInjectivity false in
/-- The retained regular-factor root channel at one original reciprocal cap coordinate.

Its nominal parent is the cached inverse-root model on the original collar box. -/
structure Point (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) where
  /-- The retained root channel of the exact original inverse-root model at this coordinate. -/ channel :
    InverseModelRootChannels.RootChannel data.model point

constructive_injectivity Point

namespace Point

/-- Construct the root channel from the retained model bound at a point inside its original collar box. -/
@[expose] def build (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) (inside :
  collar.box.Contains point) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data point :=
  ⟨RootChannel.build data.model data.model_small point inside⟩

/-- Read the square-root certificate from the retained original regular-factor root channel. -/
@[expose] def certificate {data : ReciprocalInnerInverse.Data curve collar} {point : InverseRootPolynomial.Gaussian}
  (owned : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data point) :
    CertifiedSquareRoot.Certificate (data.polynomial.eval point) := owned.channel.certificate

end Point

/-- Reuse the actual collar endpoint and the retained regular model. -/
@[expose] def atFiber (data : ReciprocalInnerInverse.Data curve collar) {source : InverseRootPolynomial.Gaussian} (fiber
  : ReciprocalCollarTransport.Fiber collar source) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data (collar.sidePoint source) :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point.build data _ (by
    rw [collar.box_eq, collar.sidePoint_eq]
    exact ReciprocalExteriorCollar.chord_contains curve fiber.boundary.1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
