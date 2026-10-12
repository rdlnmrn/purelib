module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.RootContinuation.RootOwnerCommonRefinement
public import Purelib.Riemann.RootContinuation.IntersectedRootContinuation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Power.Gaussian

@[expose] public section

/-!
# Continuation congruence with the two ordinary move bounds

Operationally equal source roots remain equal after any move accepted by both
source boxes.  A computed common source refinement and the existing cleared
box intersection replace the five extra reconditioning-clearance hypotheses.
The conclusion applies to arbitrary retained target owners, including the
reserve-aware query owners used by prepared integration.
-/

namespace Purelib.Riemann.RootContinuation.RootContinuationCongruence

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original root parameters. -/
abbrev Gaussian := Basic.Canonical
/-- The original winding-one quadratic root owner indexed by its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original operational equivalence certificate between retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent

/-- Transport equivalence to two retained target root owners refining the original equivalent source owners.

Both original parameter-movement allowances and target-to-source box refinements remain explicit. A common source
refinement supplies the intersection comparison while preserving the two target names. -/
def retainedOwnersEquivalent {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second : Owner source)
    (equivalent : NamedEquivalent (ownerRootName first.parameterNonzero first)
      (ownerRootName second.parameterNonzero second))
    (firstSmall : normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) < second.track.initial.clearance.bound)
    (firstTarget secondTarget : Owner target)
    (firstRefines : firstTarget.track.initial.box.Refines first.track.initial.box)
    (secondRefines : secondTarget.track.initial.box.Refines second.track.initial.box) :
    NamedEquivalent (ownerRootName targetNonzero firstTarget) (ownerRootName targetNonzero secondTarget) :=
  let common := RootOwnerCommonRefinement.acquire first second equivalent
  IntersectedRootContinuation.ownersEquivalent targetNonzero first second common.owner
    common.strictFirst common.strictSecond firstSmall secondSmall firstTarget secondTarget firstRefines secondRefines

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Advancing two equivalent original root owners to the same nonzero target preserves their operational name
equivalence.

Each advance uses its own retained source contour allowance and original track; the comparison keeps the two resulting
owners and their separate refinement witnesses. -/
def advanceEquivalent {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second : Owner source)
    (equivalent : NamedEquivalent (ownerRootName first.parameterNonzero first)
      (ownerRootName second.parameterNonzero second))
    (firstSmall : normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) < second.track.initial.clearance.bound) :
    NamedEquivalent (ownerRootName targetNonzero (first.advance targetNonzero (by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using firstSmall)))
      (ownerRootName targetNonzero (second.advance targetNonzero (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using secondSmall))) :=
  retainedOwnersEquivalent targetNonzero first second equivalent firstSmall secondSmall
    (first.advance targetNonzero (by simpa only [Norm.Basic.normSq_eq_canonical] using firstSmall)) (second.advance
      targetNonzero (by simpa only [Norm.Basic.normSq_eq_canonical] using secondSmall))
    (SquareRootContinuation.continuedTrack_initial_refines_source targetNonzero first.track.initial (by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using firstSmall))
    (SquareRootContinuation.continuedTrack_initial_refines_source targetNonzero second.track.initial (by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using secondSmall))

/-- The two original continued root names remain operationally equivalent after the same permitted parameter movement.

The input names are equivalent at the source, and movement satisfies both original contour allowances at the nonzero
target. -/
def continuedEquivalent {source target : Gaussian} (targetNonzero : target ≠ 0)
    (first second : Owner source)
    (equivalent : NamedEquivalent (ownerRootName first.parameterNonzero first)
      (ownerRootName second.parameterNonzero second))
    (firstSmall : normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : normSq (source - target) < second.track.initial.clearance.bound) :
    NamedEquivalent (continuedRootName targetNonzero first firstSmall)
      (continuedRootName targetNonzero second secondSmall) :=
  advanceEquivalent targetNonzero first second equivalent firstSmall secondSmall

end Purelib.Riemann.RootContinuation.RootContinuationCongruence
