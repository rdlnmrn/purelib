module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Reobservation

/-! # The whole common request of actual jointly reobserved Legendre coefficients

The original Joint scalar factory retains the exact increment-fourth request,
not only its tolerance. Its already paid minimum with a spatial request is
therefore ONE identical positive request at every original physical query.
Exact Reading transport preserves every actual selected arithmetic cache.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} {step : Step source increment} {nonzero : increment ≠ 0}
    {sourceAdditional targetAdditional : AccuracyRequest}

/-- The retained original core uses exactly the whole increment-fourth request from its actual factory. -/
theorem core_accuracy (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.accuracy = Sampling.incrementRequest increment nonzero := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_accuracy]
  rfl

/-- The actual independently paid arithmetic minimum is the SAME whole common request at every original query. -/
theorem minimum_accuracy (retained : Joint step nonzero sourceAdditional targetAdditional) (spatial : AccuracyRequest) :
    spatial.minimum retained.core.accuracy = spatial.minimum (Sampling.incrementRequest increment nonzero) :=
  congrArg (fun primary => spatial.minimum primary) retained.core_accuracy

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

end
