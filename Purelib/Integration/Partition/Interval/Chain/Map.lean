module

public import Purelib.Integration.Partition.Interval.Chain

/-! # Endpoint maps of retained interval chains

One scalar endpoint function transports every original interval and its
exact endpoint incidence, preserving the complete original order.
-/

public section

namespace Purelib.Integration.Partition.Interval.Chain

open Purelib.Data.Rat

/-- Apply the same scalar endpoint function to every original interval of an exact endpoint chain.

The original order and repeated occurrences are retained. This operation
uses endpoint incidence only; orientation and monotonicity are separate.
-/
theorem map (function : Fraction.Rational → Fraction.Rational)
    {start finish : Fraction.Rational} {intervals : List Interval} :
    Chain start finish intervals → Chain (function start) (function finish)
      (intervals.map (fun interval => ⟨function interval.start, function interval.finish⟩))
  | .nil point => .nil (function point)
  | .cons remaining => .cons (map function remaining)

end Purelib.Integration.Partition.Interval.Chain

end
