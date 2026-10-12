module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryWinding
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Riemann.Paths

open Purelib.Riemann.Topology

@[expose] public section

/-!
# A complete cap boundary with operational root return

The entire side and lap preparation is retained once. The return certificate
refers to its actual terminal owner, and the same parent bank feeds every
joined-area request. No second preparation supplies a substitute endpoint.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

set_option genInjectivity false in
/-- Keep the cached preparation type abstract when forming dependent return fields, so the record's recursors do not
unfold the numerical preparation. -/
structure ClosedPreparation (preparedType : Type u)
    (finishName : preparedType → Gaussian.Name.Basic.Named)
    (startName : Gaussian.Name.Basic.Named) where
  /-- The exact cached complete boundary preparation. -/ covered : preparedType
  /-- The operational equivalence from this actual preparation's final root name to its retained starting root name. -/
    returned : Gaussian.Equivalence.NamedEquivalent (finishName covered) startName

constructive_injectivity ClosedPreparation

/-- The retained complete cap-boundary preparation with operational return of its actual terminal root owner. -/
abbrev Data (cap : ReciprocalInnerInverse.Data curve collar)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor))
    (differential : Differentials.Basic.Differential genus) :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary.ClosedPreparation (PathCover.Data cap (Boundary.path collar) owner
    differential)
    (fun covered => OwnerTraceReadings.ownerName (PreparedPathGluing.finishOwner covered.prepared.traced.prepared))
    (OwnerTraceReadings.ownerName owner)

/-- Add the proved return to an already retained complete preparation. -/
def ofCovered {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differentials.Basic.Differential genus}
    (covered : PathCover.Data cap (Boundary.path collar) owner differential) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data cap owner differential :=
  ⟨covered, Boundary.rootReturn covered⟩

/-- One continuing root, one parent cache, and certified closure for either parity. Every area request consumes
`covered` from this retained result. -/
def build (cap : ReciprocalInnerInverse.Data curve collar)
    (owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor))
    (differential : Differentials.Basic.Differential genus) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data
      cap owner differential :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary.ofCovered (PathCover.Data.build cap (Boundary.path collar)
    (Boundary.within collar) owner differential)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
