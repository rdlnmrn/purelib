module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Integration.PreparedSwitchedRefinements.Centered

/-! # The same retained initial period spine as a centered closed chain

The actual period walk supplies its original closed state, root thread and
primitive cover. Its initial factory equation pays the absence of stationary
switches; the conversion consumes the stored state without extracting or
preparing its grid walk again.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (SwitchedPathChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient : Box}
    {grid : ClearGrid curve.polynomial ambient} {base : Canonical}
    {owner : Owner (curve.polynomial.eval base)} {source : Differential genus}

/-- Recover the exact closed centered spine of the retained initial period state, with the same original parents. -/
def initialChain (prepared : PeriodWalk grid base owner source) :
    CenteredPathChain prepared.initial.state.parents
      (start := prepared.initial.state.start) (finish := prepared.initial.state.start) :=
  SwitchedPathChain.closedCentered prepared.initial.state.chain (by
    rewrite [prepared.initial_eq]
    exact prepared.closed.initial_switchCount source) prepared.initial.closed

/-- The centered initial spine follows precisely the retained initial closed lifted path. -/
private theorem packaged_initialChain_path (prepared : PeriodWalk grid base owner source) :
    prepared.initialChain.path = (prepared.initial.state.closedLift prepared.initial.closed).path :=
  SwitchedPathChain.closedCentered_path prepared.initial.state.chain _ prepared.initial.closed

/-- The centered initial spine follows precisely the retained initial closed lifted path. -/
theorem initialChain_path (prepared : PeriodWalk grid base owner source) :
    prepared.initialChain.path = (prepared.initial.state.closedLift prepared.initial.closed).path :=
  packaged_initialChain_path prepared

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end
