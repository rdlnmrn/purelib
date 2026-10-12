module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Product
public import Purelib.Polynomial.Winding.Edge.Product.Check
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Multiplication

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace Purelib.Polynomial.Winding.Box.Product.Check

/-- Four executable local checks in positive boundary orientation. -/
def boxProductFormulaCheck
    (p q : CoefficientPolynomial) (box : Box) : Bool :=
  Winding.Edge.Product.Check.lineProductFormulaCheck p q
      (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
      box.xLower box.xUpper &&
    Winding.Edge.Product.Check.lineProductFormulaCheck p q
      (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
      box.yLower box.yUpper &&
    Winding.Edge.Product.Check.lineProductFormulaCheck p q
      (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
      box.xUpper box.xLower &&
    Winding.Edge.Product.Check.lineProductFormulaCheck p q
      (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
      box.yUpper box.yLower

/-- Four successful oriented edge checks certify the box product formula. -/
theorem boxProductFormula_of_check
    (p q : CoefficientPolynomial) (box : Box)
    (checked : boxProductFormulaCheck p q box = true) :
    Winding.Box.Product.BoxProductFormula p q box := by
  have checks :
      ((Winding.Edge.Product.Check.lineProductFormulaCheck p q
          (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
          box.xLower box.xUpper = true ∧
        Winding.Edge.Product.Check.lineProductFormulaCheck p q
          (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
          box.yLower box.yUpper = true) ∧
        Winding.Edge.Product.Check.lineProductFormulaCheck p q
          (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
          box.xUpper box.xLower = true) ∧
        Winding.Edge.Product.Check.lineProductFormulaCheck p q
          (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
          box.yUpper box.yLower = true := by
    have split {first second : Bool} (accepted : (first && second) = true) :
        first = true ∧ second = true := by
      cases first <;> cases second <;> cases accepted; exact ⟨rfl, rfl⟩
    simp only [boxProductFormulaCheck, -eq_self, -iff_self] at checked
    have outer := split checked
    have middle := split outer.1
    have inner := split middle.1
    exact ⟨⟨inner, middle.2⟩, outer.2⟩
  exact
    { bottom := Winding.Edge.Product.Check.lineProductFormula_of_check _ _ _ _ _ _ checks.1.1.1
      right := Winding.Edge.Product.Check.lineProductFormula_of_check _ _ _ _ _ _ checks.1.1.2
      top := Winding.Edge.Product.Check.lineProductFormula_of_check _ _ _ _ _ _ checks.1.2
      left := Winding.Edge.Product.Check.lineProductFormula_of_check _ _ _ _ _ _ checks.2 }

/-- A successful box product check certifies additivity of the raw winding under multiplication. -/
theorem quadrupledBoxWinding_mul_of_check
    (p q : CoefficientPolynomial) (box : Box)
    (checked : boxProductFormulaCheck p q box = true) :
    Winding.Box.Basic.quadrupledBoxWinding (p * q) box =
      Winding.Box.Basic.quadrupledBoxWinding p box + Winding.Box.Basic.quadrupledBoxWinding q box :=
  Winding.Box.Product.quadrupledBoxWinding_mul_of_formula p q box
    (boxProductFormula_of_check p q box checked)

end Purelib.Polynomial.Winding.Box.Product.Check

end
