module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Init.Prelude

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Sheets.Basic

set_option genInjectivity false in
/-- One operationally certified sheet value above a displayed rational base point. The curve equation is equality of
finite CCL observations, so it does not require the generally irrational `y` coordinate to be a rational witness. -/
structure AlgebraicSheetValue {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (point : Data.Gaussian.Basic.Canonical) where
  /-- The coherent named sheet coordinate retained over the exact base point. -/ value : Coherent.CoherentNamed
  /-- The retained sheet coordinate is certified apart from zero. -/ apart : Named.Apart value.name
  /-- The finite sheet label selected for this value. -/ sheet : Fin 2
  /-- Squaring the retained sheet value is equivalent to evaluating the defining polynomial at the exact base point. -/
    curveEquation : Gaussian.Equivalence.NamedEquivalent
    (CoherentNamed.mul value value).name
    (Horner.polynomialEval curve.polynomial
      (Coherence.exact point)).name

constructive_injectivity Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

end Purelib.Curves.Hyperelliptic.Sheets.Basic

end
