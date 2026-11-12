module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Changed-parameter inverse-root sources on the retained transported owner

A genuine original Point.Step supplies the exact changed-radicand owner.
The existing observation and aligned-seed constructors prepare a new local
inverse-root neighborhood from that very owner, with an independently
computed positive radius. Its seed and all actual point candidates stay in
the original source seed box. Equal-radicand square identities and that
original signed box then compare its actual queries with retained target
Steps, without an assumed independently shifted-query agreement.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} (step : Step source increment)

/-- Construct a changed-polynomial observation site and aligned inverse-root neighborhood from the retained Step owner.

The existing owner-backed alignment prepares and samples that same original
transported occurrence. Both the observation radius and continued radius
are computed anew; the old physical patch radius is not reused as a bound.
-/
def neighborhood (modelCount : Nat) : ContinuedNeighborhood (Paths.polynomial (parameter + increment)) modelCount :=
  let site := ObservationNeighborhood.ofPoint (Paths.polynomial (parameter + increment)) modelCount point
    step.owner.parameterNonzero
  ContinuedNeighborhood.ofOwner site step.owner

/-- The complete new neighborhood is the existing owner-backed factory at the exact original transported occurrence. -/
theorem neighborhood_eq (modelCount : Nat) :
    step.neighborhood modelCount = ContinuedNeighborhood.ofOwner
      (ObservationNeighborhood.ofPoint (Paths.polynomial (parameter + increment)) modelCount point
        step.owner.parameterNonzero) step.owner := by
  rfl

/-- The new observation site is the original finite factory at the identical physical point and changed polynomial. -/
theorem neighborhood_site (modelCount : Nat) :
    (step.neighborhood modelCount).base.site =
      ObservationNeighborhood.ofPoint (Paths.polynomial (parameter + increment)) modelCount point
        step.owner.parameterNonzero := by
  rfl

/-- The new neighborhood retains the complete target Step owner across its exact physical-center index. -/
theorem neighborhood_origin (modelCount : Nat) : HEq (step.neighborhood modelCount).origin step.owner := by
  rfl

/-- The retained new origin has exactly the target Step owner's initial root box. -/
theorem neighborhood_origin_box (modelCount : Nat) :
    (step.neighborhood modelCount).origin.track.initial.box = step.owner.track.initial.box := by
  rfl

/-- The changed-parameter local neighborhood remains centered at the identical original physical point. -/
theorem neighborhood_center (modelCount : Nat) :
    (step.neighborhood modelCount).base.site.center = point := by
  rfl

/-- The actual changed-parameter seed box refines the original source patch's signed root box.

The new aligned seed refines the Step owner, which refines the retained
source point owner and its original seed box. These are root-box
refinements; they assert no relation between the two physical radii.
-/
theorem neighborhood_seed_refines (modelCount : Nat) :
    (step.neighborhood modelCount).base.seed.owner.track.initial.box.Refines
      patch.base.seed.owner.track.initial.box := by
  have retained := (step.neighborhood modelCount).owner_refines
  rewrite [step.neighborhood_origin_box modelCount] at retained
  exact (retained.trans step.refines).trans source.refines

/-- Every actual target Step candidate stays in the original source patch's signed seed box. -/
theorem target_candidate_inside {state : step.root.value.name.process.State} {candidate : Canonical}
    (possible : step.root.value.name.process.Possible state candidate) :
    patch.base.seed.owner.track.initial.box.Contains candidate :=
  source.refines.contains (step.refines.contains
    (CertifiedSquareRoot.Sampling.candidate_in_initial_box step.owner step.root_eq possible))

/-- Every actual candidate on the new source neighborhood stays in the same original signed seed box. -/
theorem neighborhood_candidate_inside (modelCount : Nat) {queryPoint : Canonical}
    (sample : ContinuedNeighborhood.Point (step.neighborhood modelCount) queryPoint)
    (state : sample.certificate.value.name.process.State) {candidate : Canonical}
    (possible : sample.certificate.value.name.process.Possible state candidate) :
    patch.base.seed.owner.track.initial.box.Contains candidate :=
  (step.neighborhood_seed_refines modelCount).contains (sample.candidate_inside state possible)

/-- Compare a genuine new-neighborhood query with an actual target Step at the identical physical input.

Both input owners and certificates remain independent. The original signed
seed box contains every candidate of each process, so its positive root-sum
floor and the two exact changed-radicand square identities construct the
existing operational comparison with both consumer start indices preserved.
No query, root observation or desired comparison is a supplied hypothesis.
-/
def neighborhood_agrees (modelCount : Nat) {queryPoint : Canonical}
    {querySource : ContinuedNeighborhood.Point patch queryPoint} (queryStep : Step querySource increment)
    (sample : ContinuedNeighborhood.Point (step.neighborhood modelCount) queryPoint) :
    NamedEquivalent queryStep.root.value.name sample.certificate.value.name := by
  apply SquareRootProvenance.equivalent_of_sum_lower queryStep.root.square sample.certificate.square
    (4 * patch.rootLower) (Order.Arithmetic.mul_pos_direct (by decide +kernel) patch.rootLower_positive)
  intro firstIndex lastIndex
  have firstPossible := Process.Sampling.witnessAt_possible
    queryStep.root.value.name.process queryStep.root.value.name.state firstIndex
  have lastPossible := Process.Sampling.witnessAt_possible
    sample.certificate.value.name.process sample.certificate.value.name.state lastIndex
  exact patch.root_sum_lower (queryStep.target_candidate_inside firstPossible)
    (step.neighborhood_candidate_inside modelCount sample _ lastPossible)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end
