module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Riemann.Branches.SquareRootSheets
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Riemann.Branches

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

namespace Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

/-- Automatically construct either algebraic sheet over a displayed rational base point whose radicand is certified
nonzero. The two finite owners come from isolation of `Z^2 - f(x)`; the curve equation is then transported to the actual
CCL Horner evaluation of `f` at `x`. -/
def automatic {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus)
    (point : Data.Gaussian.Basic.Canonical) (radicandNonzero : curve.polynomial.eval point ≠ 0)
    (sheet : Fin 2) : Sheets.Basic.AlgebraicSheetValue curve point := by
  let root := SquareRootSheets.sheet radicandNonzero sheet
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        NamedEquivalent.trans root.square
          (NamedEquivalent.symm
            (Horner.polynomialEval_exact
              curve.polynomial point)) }

end Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

end
