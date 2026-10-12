module

public import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.CauchyIndex.Endpoint
import Purelib.Data.Sign.Stability

/-!
# Formal Cauchy events in a positive half-plane

A fixed positive real coordinate and stable imaginary signs determine the
exact doubled event reading from the two endpoint sign jumps.
-/

namespace Purelib.Data.Sign.CauchyIndex.HalfPlane

/-- A fixed positive real sign identifies the Cauchy event with its endpoint jump difference.

The retained imaginary center sign is stable against both endpoint imaginary
signs. The finite sign table then determines the same doubled integer reading. -/
public theorem sign_eventIndex2_positive
    (center lower upper : Sign)
    (lowerStable : Sign.Stable center lower)
    (upperStable : Sign.Stable center upper) :
    Sign.eventIndex2 .positive center
        .positive lower .positive upper =
      (Sign.jump .positive lower : Int) -
        Sign.jump .positive upper := by
  revert lowerStable upperStable
  cases center <;> cases lower <;> cases upper <;> decide

end Purelib.Data.Sign.CauchyIndex.HalfPlane
