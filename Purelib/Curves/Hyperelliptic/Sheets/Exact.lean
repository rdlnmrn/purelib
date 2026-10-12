module
public import Purelib.Approximation.Gaussian.Name.Apart.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

section
public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

/-- Construct an algebraic sheet value from a nonzero Gaussian rational.

The retained sheet index and polynomial equation determine the exact value
name, its apartness floor, and its operational comparison with evaluation at
the displayed point. -/
@[expose] def exact {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (point value : Data.Gaussian.Basic.Canonical) (nonzero : value ≠ 0) (sheet : Fin 2)
    (equation : value ^ 2 = curve.polynomial.eval point) :
    Sheets.Basic.AlgebraicSheetValue curve point := by
  let valueName := Coherence.exact value
  let pointName := Coherence.exact point
  have productEquivalent : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul valueName valueName).name
      (Named.exact (value * value)) := by
    simpa only [valueName,
      CoherentNamed.mul,
      Coherence.exact] using
      Exact.exactMul_named_equivalent value value
  have evaluationEquivalent :=
    Horner.polynomialEval_exact
      curve.polynomial point
  have productEqual : value * value = curve.polynomial.eval point := by
    simpa only [pow_two] using equation
  exact
    { value := valueName
      apart := exactApart value nonzero
      sheet := sheet
      curveEquation := NamedEquivalent.trans
        productEquivalent
        (NamedEquivalent.trans
          (by
            rw [productEqual]
            exact NamedEquivalent.refl _)
          (NamedEquivalent.symm
            evaluationEquivalent)) }

end Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

end
