module
import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.OneSided.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

@[expose] public section

/-!
# One-sided rational refinement processes

These processes expose improving rational evidence without postulating a
hidden endpoint.  A lower process only promises increasing lower bounds, and
an upper process only promises decreasing upper bounds.  In particular,
neither structure contains an accuracy request or a convergence claim.

A `LocatedPair` is deliberately stronger: it supplies a finite request which
puts one lower observation and one upper observation within an explicitly
requested positive rational gap.  Only at that boundary do the observations
become an ordinary two-sided `BoundProcess`.
-/

namespace Purelib.Approximation
namespace LowerProcess
namespace Refines
end Refines
end LowerProcess

namespace UpperProcess
namespace Refines
end Refines
end UpperProcess

/-! ## One-sided views of a fixed rational-bound request -/

namespace BoundProcess

/-- Repeating one explicitly chosen positive request exposes the lower endpoints of a two-sided bound process as
ordinary one-sided evidence. This view promises only monotonicity; repeating the same request need not produce strict
progress. -/
def lowerRequestProcess (process : Approximation.BoundProcess) (epsilon :
  Fraction.Rational)
    (positive : 0 < epsilon) : Approximation.LowerProcess :=
  LowerProcess.ofBoundRefinement process.State process.bound process.initial
    (fun state => process.request state epsilon positive)
    (fun state => process.request_refines state epsilon positive)
    process.refinesInitial

/-- Repeating one explicitly chosen positive request exposes the upper endpoints of a two-sided bound process as
ordinary one-sided evidence. -/
def upperRequestProcess (process : Approximation.BoundProcess) (epsilon :
  Fraction.Rational)
    (positive : 0 < epsilon) : Approximation.UpperProcess :=
  UpperProcess.ofBoundRefinement process.State process.bound process.initial
    (fun state => process.request state epsilon positive)
    (fun state => process.request_refines state epsilon positive)
    process.refinesInitial

end BoundProcess
namespace PairedObservation
namespace Refines
end Refines

end PairedObservation
namespace LocatedPair
end LocatedPair

end Purelib.Approximation

end
