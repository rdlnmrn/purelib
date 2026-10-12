module

import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Sign.Interval.Prepare
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Coefficient-finite resolution of constructive Cauchy cells

Adjacent members of a signed remainder chain carry explicit Bézout data.
Their rational clearance bounds force at least one member to have a certified
strict sign on every sufficiently small displayed interval.  A second finite
bound makes an unresolved middle member dominated by the next remainder,
which certifies the cancelling signed-step event.
-/

namespace Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved

set_option genInjectivity false in
/-- A successful executable sign classification retained with its witness. -/
structure ResolvedSign (p :
  Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) where
  /-- The retained strict-sign certificate on the displayed interval. -/ certificate :
    Dense.Rational.Sign.Interval.Basic.Certificate p interval
  /-- The executable sign classifier returned this exact certificate. -/ found :
    Dense.Rational.Sign.Interval.Prepare.certificate? p interval = some certificate

constructive_injectivity ResolvedSign

end Purelib.Polynomial.Dense.Rational.Sign.Interval.Resolved

end
