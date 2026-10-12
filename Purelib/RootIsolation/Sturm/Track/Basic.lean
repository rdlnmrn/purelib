module

public import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.Data.Rat.Interval.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Clear one-dimensional nonzero-event states

The original rational polynomial indexes a retained proper rational cell and a certificate that its doubled Sturm count
on those exact endpoints is nonzero.
-/

public section

namespace Purelib.RootIsolation.Sturm.Track.Basic

set_option genInjectivity false in
/-- One proper rational cell carrying a nonzero doubled Sturm count.

The original rational polynomial indexes a retained proper rational cell and a certificate that its doubled Sturm count
on those exact endpoints is nonzero. -/
structure State (polynomial : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- The retained proper rational parameter cell. -/ cell : Data.Rat.Interval.Proper.Cell
  /-- The original polynomial has nonzero doubled Sturm count on the retained cell. -/ countNonzero :
    Sturm.Count.Basic.sturmRootCount2 polynomial
    cell.interval.lower cell.interval.upper ≠ 0

constructive_injectivity State

end Purelib.RootIsolation.Sturm.Track.Basic

end
