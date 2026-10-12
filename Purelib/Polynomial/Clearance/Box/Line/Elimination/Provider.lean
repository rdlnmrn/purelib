module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Checked shortcuts for winding-one refinement

Newton iteration supplies candidates, not a convergence assumption.  A
candidate is accepted only after exact finite checks of strict containment,
the requested diagonal bound and winding four.  Eliminant-safe sides supply
the same ambient and boundary clearances as the total extractor.  A bounded
unsuccessful search delegates to the original total track.
-/

namespace Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

set_option genInjectivity false in
/-- Line-clearance constructors indexed by one axis-elimination certificate.

A nonzero eliminant value produces clearance along the corresponding vertical or horizontal line in any supplied ambient
box. -/
structure AxisClearances {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) where
  /-- Construct vertical-line clearance from the nonzero vertical eliminant value. -/ vertical : (ambient :
    Box) → (x : Fraction.Rational) →
    elimination.vertical.eval x ≠ 0 →
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient x
  /-- Construct horizontal-line clearance from the nonzero horizontal eliminant value. -/ horizontal : (ambient :
    Box) → (y : Fraction.Rational) →
    elimination.horizontal.eval y ≠ 0 →
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient y

constructive_injectivity AxisClearances

/-- Construct both axis-line clearances from the retained Bézout certificates.

Each nonzero eliminant value supplies the original coprimality witness for the two coordinate polynomials of that line.
-/
def AxisClearances.canonical {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    AxisClearances elimination where
  vertical ambient x nonzero := Clearance.Box.Line.Bezout.verticalOfCoprime p ambient x
    (elimination.vertical_coprime x nonzero)
  horizontal ambient y nonzero := Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient y
    (elimination.horizontal_coprime y nonzero)
end Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

end
