module

public import Purelib.Riemann.Topology.SquareRootContinuationChain.Exact
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Exact
import Purelib.Geometry.Rational.Box.Refinement

/-! # Original exact-seed windows and retained target certificates

An unchanged original seed square supplies candidate containment for a
separately retained target Owner/certificate. Its actual refinement and the
original box readback preserve both owners. The original target root's exact
square and membership then give operational comparison without re-isolation.
-/

public section

namespace Purelib.Riemann.Topology.SquareRootContinuationChain.Owner.Exact.Seed

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Riemann.Topology
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)

/-- Every actual candidate of the retained target certificate stays in the identical original exact-seed square.

The supplied certificate is the unchanged factory of the supplied original
Owner, whose actual initial box refines the source seed's original box. No
new root certificate or channel is constructed by this containment theorem.
-/
theorem retained_candidate_inside {center parameter candidate : Canonical} (seed : Seed center)
    (owner : SquareRootContinuationChain.Owner parameter) (certificate : CertifiedSquareRoot.Certificate parameter)
    (certificate_eq : certificate = owner.certificate owner.parameterNonzero)
    (refines : owner.track.initial.box.Refines seed.owner.track.initial.box)
    {state : certificate.value.name.process.State}
    (possible : certificate.value.name.process.Possible state candidate) :
    (Box.Square.Centered.Affine.centeredSquare center seed.separation.radius seed.separation.positive.le).Contains
      candidate := by
  have inside := CertifiedSquareRoot.Sampling.candidate_in_initial_box owner certificate_eq possible
  have original := refines.contains inside
  rewrite [seed.box_eq] at original
  exact original

/-- Compare a retained original target certificate with an exact target root in the unchanged source seed square.

The source seed, supplied target Owner and complete target certificate remain
separate retained inputs. Actual target-to-source box refinement supplies all
candidate containment; the original independently specified exact target root
provides only its square and membership. The existing paid square comparison
constructs operational agreement on the actual target certificate name.
-/
def retained_agrees_exact {center parameter : Canonical} (seed : Seed center)
    (owner : SquareRootContinuationChain.Owner parameter) (certificate : CertifiedSquareRoot.Certificate parameter)
    (certificate_eq : certificate = owner.certificate owner.parameterNonzero)
    (refines : owner.track.initial.box.Refines seed.owner.track.initial.box)
    (root : Canonical) (square : root ^ 2 = parameter)
    (inside : (Box.Square.Centered.Affine.centeredSquare center seed.separation.radius
      seed.separation.positive.le).Contains root) : NamedEquivalent certificate.value.name (Named.exact root) :=
  CertifiedSquareRoot.Sampling.Exact.agrees certificate seed.separation root square inside
    (fun possible => retained_candidate_inside seed owner certificate certificate_eq refines possible)

end Purelib.Riemann.Topology.SquareRootContinuationChain.Owner.Exact.Seed
