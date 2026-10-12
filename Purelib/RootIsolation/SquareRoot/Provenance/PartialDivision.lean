module
import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation.Gaussian

section
@[expose] public section

/-!
# Algebraic provenance regressions

Cover the repeated-zero root, both independently isolated sheets of `Z² - 2`,
retained winding ownership, approximate nonzero candidates on an operationally
zero channel, coefficient-derived observation bounds, and compatibility with
ordinary/manual division. Tests use the proved isolation interface without
kernel-recomputing a large root-isolation trace.
-/

namespace Purelib.RootIsolation.SquareRoot.Provenance.PartialDivision

open Purelib.Riemann.RootContinuation.SquareRootSidecar
open Purelib.Riemann.RootContinuation.SquareRootProvenance

/-- The quotient prepared from a nonzero square-root sidecar is equivalent to an accepted partial-division result.

Both constructions retain the same numerator and denominator channel; the readiness certificate identifies the finite
refinement state and accepted output. -/
def preparation_agrees_with_ready {channel numerator
  : Name.Coherent.CoherentNamed}
    (sidecar : Sidecar channel) (nonzero : sidecar.parameter ≠ 0)
    {state : Approximation.Gaussian.Name.Coherent.Refinement.State channel} {output : Name.Coherent.CoherentNamed}
    (ready : Approximation.Gaussian.Division.Partial.Ready numerator channel state output) :
    Equivalence.NamedEquivalent
      ((prepared_of_square sidecar.square nonzero).quotient numerator).name output.name :=
  (prepared_of_square sidecar.square nonzero).quotient_respects_ready ready
end Purelib.RootIsolation.SquareRoot.Provenance.PartialDivision

end
