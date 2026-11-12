module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Norm.Basic

/-! # Same-point comparison of independently retained parameter steps

Two original continued Point owners may come from different physical
patches and seed boxes. An actual signed source comparison, exact point
incidence and each existing Step's own contour payment derive agreement of
its unchanged target Owner and cached certificate. The existing common
source-refinement/intersection construction is reused; neither original
point acquisition nor parameter advancement is executed again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {parameter increment firstPoint lastPoint : Canonical} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
    {firstSource : ContinuedNeighborhood.Point firstPatch firstPoint}
    {lastSource : ContinuedNeighborhood.Point lastPatch lastPoint}

/-- Transport actual signed source agreement to two already retained steps at exactly the same physical point.

The original source and target Owners are separate inputs. Both actual
Step.admitted payments derive their own strict source-to-target contour
bounds; both Step.refines fields provide the original target-box
inclusions. The existing retainedOwnersEquivalent construction acquires a
common source refinement and compares these same targets. Exact point
transport changes indices only and does not recreate either Step.
-/
def equivalent_of_source_eq (first : Step firstSource increment) (last : Step lastSource increment)
    (point_eq : firstPoint = lastPoint)
    (sourceEquivalent : NamedEquivalent firstSource.certificate.value.name lastSource.certificate.value.name) :
    NamedEquivalent first.root.value.name last.root.value.name := by
  cases point_eq
  have sourceOwners : NamedEquivalent (ownerRootName firstSource.owner.parameterNonzero firstSource.owner)
      (ownerRootName lastSource.owner.parameterNonzero lastSource.owner) := sourceEquivalent
  have firstSmall := movement_lt_contour firstSource increment first.admitted
  have lastSmall := movement_lt_contour lastSource increment last.admitted
  rewrite [Norm.Basic.normSq_eq_canonical] at firstSmall lastSmall
  have compared := RootContinuationCongruence.retainedOwnersEquivalent first.owner.parameterNonzero
    firstSource.owner lastSource.owner sourceOwners firstSmall lastSmall first.owner last.owner
    first.refines last.refines
  have firstName : ownerRootName first.owner.parameterNonzero first.owner = first.root.value.name := by
    rewrite [first.root_eq]
    rfl
  have lastName : ownerRootName last.owner.parameterNonzero last.owner = last.root.value.name := by
    rewrite [last.root_eq]
    rfl
  exact NamedEquivalent.transport firstName lastName compared

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end
