module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Polynomial.Dense.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Explicit finite branch data for the cyclic quartic

This file supplies four audited rational winding boxes for
`y² = x⁴ - 1`.  Their centres are the exact Gaussian-rational roots
`-1`, `1`, `-i`, and `i`.  Every box has horizontal radius `1/4` and vertical
radius `1/2`; the narrow horizontal direction keeps the four interiors
separated while the lower boundary places the canonical connectors in the
balanced corridor between the horizontal and vertical branch points.
Factorwise boundary clearance and an exact quadrupled winding calculation
turn the boxes into a
degree-complete shrinking branch family.  Thus the period programs below use
the explicit-data theorem path and do not execute the generic global root
isolator while elaborating the example.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

/-- Local continuation depth on every restricted working segment. -/
def workingInnerDepth : Nat := 3
end Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

end

section
@[expose] public section

/-!
# Explicit finite branch data for the cyclic quartic

This file supplies four audited rational winding boxes for
`y² = x⁴ - 1`.  Their centres are the exact Gaussian-rational roots
`-1`, `1`, `-i`, and `i`.  Every box has horizontal radius `1/4` and vertical
radius `1/2`; the narrow horizontal direction keeps the four interiors
separated while the lower boundary places the canonical connectors in the
balanced corridor between the horizontal and vertical branch points.
Factorwise boundary clearance and an exact quadrupled winding calculation
turn the boxes into a
degree-complete shrinking branch family.  Thus the period programs below use
the explicit-data theorem path and do not execute the generic global root
isolator while elaborating the example.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

/-- Squared-diameter target for every cached local quadratic owner. -/
def workingRootDiameter : Fraction.Rational := 5
end Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

end

section
@[expose] public section

/-!
# Explicit finite branch data for the cyclic quartic

This file supplies four audited rational winding boxes for
`y² = x⁴ - 1`.  Their centres are the exact Gaussian-rational roots
`-1`, `1`, `-i`, and `i`.  Every box has horizontal radius `1/4` and vertical
radius `1/2`; the narrow horizontal direction keeps the four interiors
separated while the lower boundary places the canonical connectors in the
balanced corridor between the horizontal and vertical branch points.
Factorwise boundary clearance and an exact quadrupled winding calculation
turn the boxes into a
degree-complete shrinking branch family.  Thus the period programs below use
the explicit-data theorem path and do not execute the generic global root
isolator while elaborating the example.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

open Purelib.RootIsolation in
/-- The retained squared-diameter target, five, is strictly positive. -/
theorem workingRootDiameter_positive : 0 <
  workingRootDiameter := by
  unfold workingRootDiameter
  decide
end Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration

end
