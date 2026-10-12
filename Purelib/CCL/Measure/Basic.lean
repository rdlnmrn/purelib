module
public import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Compatibility

@[expose] public section

/-!
# Shared finite CCL measure coordinates
-/

namespace Purelib.CCL.Measure

open Purelib.Data.Rat in
/-- The canonical quotient-free rational coordinate type. -/
abbrev Coordinate := Fraction.Rational

end Purelib.CCL.Measure

end
