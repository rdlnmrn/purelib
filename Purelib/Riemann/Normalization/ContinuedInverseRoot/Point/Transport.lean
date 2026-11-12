module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Exact transports of complete continued Point factories

Only equal nominal count, patch and point indices are eliminated. These
laws retain the original Point.acquire result and its Owner together with
all cached fields; no geometric coordinate coincidence supplies an Owner
identity without the identical original acquisition factory.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- Exact nominal index transports preserve the whole identical Point acquisition factory. -/
theorem acquire_heq_of_eq {polynomial : CoefficientPolynomial} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood polynomial firstCount} {lastPatch : ContinuedNeighborhood polynomial lastCount}
    {firstPoint lastPoint : Canonical} (sameCount : firstCount = lastCount) (samePatch : HEq firstPatch lastPatch)
    (samePoint : firstPoint = lastPoint) (firstInside : firstPatch.box.Contains firstPoint)
    (lastInside : lastPatch.box.Contains lastPoint) :
    HEq (acquire firstPatch firstPoint firstInside) (acquire lastPatch lastPoint lastInside) := by
  cases sameCount
  cases (eq_of_heq samePatch)
  cases samePoint
  rfl

/-- Point-coordinate transport retains the complete original Point heterogeneously. -/
theorem castPoint_heq {polynomial : CoefficientPolynomial} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {first last : Canonical}
    (same : first = last) (sample : Point patch last) : HEq (castPoint same sample) sample := by
  cases same
  rfl

/-- Casting the identical acquisition factory gives the original acquisition at the equal endpoint index. -/
theorem castPoint_acquire {polynomial : CoefficientPolynomial} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {first last : Canonical} (same : first = last)
    (firstInside : patch.box.Contains first) (lastInside : patch.box.Contains last) :
    castPoint same (acquire patch last lastInside) = acquire patch first firstInside := by
  cases same
  rfl

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
