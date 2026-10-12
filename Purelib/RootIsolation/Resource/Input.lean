module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Input

set_option genInjectivity false in
/-- The exact finite input for measuring raw root-isolation subdivision.

It retains the original polynomial, ambient box, axis-elimination degree and certificate, raw-winding state and
requested diagonal threshold. -/
structure StageThreeInput where
  /-- The original dense Gaussian polynomial being refined. -/ polynomial :
    CoefficientPolynomial
  /-- The original ambient box containing the retained state. -/ ambient : Box
  /-- The retained finite axis-elimination degree bound. -/ degreeBound : Nat
  /-- The original axis-safe-cut certificate at that exact degree bound. -/ elimination :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
    polynomial degreeBound
  /-- The actual retained nonzero-winding state in the original ambient box. -/ state : State.Raw.RawWindingState
    polynomial ambient
  /-- The requested rational squared-diagonal threshold. -/ threshold : Fraction.Rational

constructive_injectivity StageThreeInput

end Purelib.RootIsolation.Resource.Input

end

section
public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Input
namespace StageThreeInput

/-- Compute the original input's finite raw-refinement depth. -/
@[expose] def depth (input : Resource.Input.StageThreeInput)
  : Nat :=
  Subdivision.Raw.Request.refinementDepth input.state input.threshold
end StageThreeInput
end Purelib.RootIsolation.Resource.Input

end

section
public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Input
namespace StageThreeInput

/-- Read the quarter-turn substitution of the original retained polynomial. -/
@[expose] def horizontalPolynomial (input :
  Resource.Input.StageThreeInput) : CoefficientPolynomial :=
  Dense.Gaussian.Substitution.QuarterTurn.quarterTurn input.polynomial

end StageThreeInput
end Purelib.RootIsolation.Resource.Input

end

section
public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Input
namespace StageThreeInput

/-- The standard calculation-size input obtained from the executable
separated-Sylvester axis certificate. -/
@[expose] def ofSeparated {polynomial :
  CoefficientPolynomial} {ambient : Box}
    (nonzero : polynomial.isZero = false)
    (degreePositive : 0 < polynomial.natDegree)
    (state : State.Raw.RawWindingState polynomial ambient)
    (threshold : Fraction.Rational) : Resource.Input.StageThreeInput where
  polynomial := polynomial
  ambient := ambient
  degreeBound := Elimination.Axis.Separated.separatedEliminationDegree polynomial
  elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate
    polynomial nonzero degreePositive
  state := state
  threshold := threshold
end StageThreeInput
end Purelib.RootIsolation.Resource.Input

end
