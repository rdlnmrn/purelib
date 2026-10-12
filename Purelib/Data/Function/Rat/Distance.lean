module
public import Purelib.Geometry.Projective.Line.Basic

public import Purelib.CCL.Measure.Basic
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Data.Rat
open Purelib.CCL.Measure (Coordinate)

section
@[expose] public section

/-!
# Powered-Lp observations from finite CCL prefixes

A rational probe of a projective CCL realization can be raised to any
displayed natural-powered magnitude.  When that transformed probe carries an
explicit chordal sensitivity bound, the existing finite-cylinder machinery
gives a certified rational enclosure of its finite powered-Lp expectation.
No eventual decoded point or infinite stream is selected.
-/

namespace Purelib.Data.Function.Rat

/-- Raise the rational magnitude of each probe value to a natural power.

Magnitude is measured by rational separation from zero. The displayed exponent
includes zero, for which the resulting value is one. -/
def poweredProbe
    (probe : Geometry.Projective.Line.GaussianLine → Coordinate) (exponent : Nat) :
    Geometry.Projective.Line.GaussianLine → Coordinate :=
  fun point =>
    Distance.rationalSeparation (probe point) 0 ^ exponent

end Purelib.Data.Function.Rat

end

section
section
@[expose] public section

/-!
# Centered powered deviations from finite CCL prefixes

Natural-powered rational separation from a displayed center remains an
ordinary rational probe.  An explicit chordal sensitivity certificate for
that transformed probe therefore yields static and progressive finite
enclosures of the exact powered deviation of every supplied realization
family.
-/

namespace Purelib.Data.Function.Rat

/-- Raise each function value's rational deviation from a fixed center to a natural power.

The input domain is arbitrary. The center and exponent are supplied explicitly, and each value is computed from its
rational separation from that center. -/
def poweredDeviationProbe (probe : Proj → Coordinate) (center : Coordinate)
    (exponent : Nat) : Proj → Coordinate :=
  fun point =>
    Distance.rationalSeparation (probe point) center ^ exponent
namespace PrefixFamilyProcess
end PrefixFamilyProcess

end Purelib.Data.Function.Rat

end

end
