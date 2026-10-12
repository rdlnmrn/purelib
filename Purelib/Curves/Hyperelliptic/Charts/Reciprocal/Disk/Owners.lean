module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
public import Purelib.Riemann.Normalization.InverseModelRootAgreement
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse

open Purelib.Geometry.Rational.Box

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Retained regular-factor owners at actual reciprocal disk points

Pointwise certified views reuse the cap polynomial's cached coefficients.
Their operational roots agree with the existing inner-cap roots wherever
both are defined. Inverse outer-boundary points need no guessed sheet label.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

set_option genInjectivity false in
/-- The retained regular cap-model root channel at an original point of the full reciprocal disk.

Its pointwise model view reuses the original cached polynomial and retains its exact disk containment evidence. -/
structure DiskPoint (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) where
  /-- The original point lies in the curve polynomial's coefficient-certified reciprocal disk. -/ inside :
    Reciprocal.Bounds.InDisk curve.polynomial point
  /-- The retained root channel of the original cap polynomial's pointwise disk model. -/ channel :
    InverseModelRootChannels.RootChannel
    (Data.diskPointModel data point inside) point

constructive_injectivity DiskPoint

namespace DiskPoint

/-- Construct the original cap-model root channel on its exact pointwise disk view. -/
def build (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) (inside :
  Reciprocal.Bounds.InDisk curve.polynomial point) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint data point :=
  ⟨inside, RootChannel.build
    (Data.diskPointModel data point inside) le_rfl point
    (Data.pointBox_contains point)⟩

/-- Read the square-root certificate from the retained original disk-model root channel. -/
def certificate {data : ReciprocalInnerInverse.Data curve collar} {point : InverseRootPolynomial.Gaussian} (owned :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint data point) :
    CertifiedSquareRoot.Certificate (data.polynomial.eval point) := owned.channel.certificate

/-- The exterior view retains the very root used by the inner cap, despite the different domain certificate and possibly
different residual bounds. -/
def innerEquivalent {data : ReciprocalInnerInverse.Data curve collar} {point : InverseRootPolynomial.Gaussian} (outer :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint data point) (inner : Owners.Point data point) :
    Gaussian.Equivalence.NamedEquivalent outer.certificate.value.name inner.certificate.value.name :=
  InverseModelRootAgreement.equivalent_of_value outer.channel inner.channel rfl

end DiskPoint

/-- The actual inverse of the fixed affine boundary lies in the certified disk. The cached cap model therefore supplies
its regular-factor root. -/
def atInverseBoundary (data : ReciprocalInnerInverse.Data curve collar) {source : InverseRootPolynomial.Gaussian}
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint data source⁻¹ :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners.DiskPoint.build data source⁻¹
    (ReciprocalExteriorCollar.inverse_inDisk curve boundary)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
