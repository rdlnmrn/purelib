module
import Purelib.Data.List.Map
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Atom
public import Purelib.Polynomial.Dense.Rational.Sign.Formula
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula (BoundaryFormula)
open Purelib.Polynomial.Dense.Rational.Sign (PolynomialFormula)

section
@[expose] public section

/-!
# CCL formulas cleared along rational boundary curves

Every Hermitian atom pulled back to a rational curve is compiled to one
explicit univariate rational polynomial.  Its value is the original atom
form multiplied by the positive quadrance of the curve denominator, so all
six parser sign tests are preserved at every displayed non-pole parameter.

This finite compiler lets the event layer feed all atoms of a candidate
one-bit formula into the existing equality/apart gcd profiler.  No affine
point, polynomial root, or limiting value is introduced by the translation.
-/

namespace Purelib.RationalFunctions.Curve.Hermitian.Formula

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Compile a Hermitian atom to its denominator-cleared polynomial with the same sign test. -/
def clearedAtom (curve : Curve.RationalCurve) (atom :
  Projective.Hermitian.Atom) : Dense.Rational.Sign.PolynomialAtom :=
  ⟨Curve.Hermitian.clearedForm curve atom.form, atom.sign⟩

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- A cleared polynomial atom has the same truth value as its Hermitian atom at a non-pole parameter.

Denominator quadrance is strictly positive, so multiplication by this clearing factor preserves the atom's sign test. -/
theorem clearedAtom_holds_iff
    (curve : Curve.RationalCurve) (atom : Projective.Hermitian.Atom) (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedAtom curve atom).Holds parameter ↔
      atom.Holds (curve.point parameter) := by
  unfold Dense.Rational.Sign.PolynomialAtom.Holds Projective.Hermitian.Atom.Holds
    clearedAtom
  rw [Curve.Hermitian.eval_clearedForm curve atom.form parameter denominatorNonzero]
  exact Data.Rat.SignTest.holds_mul_pos_iff atom.sign
    (Data.Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter))
    (atom.form.eval (curve.point parameter))
    (Gaussian.Norm.Basic.normSq_pos denominatorNonzero)

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Compile a finite Hermitian formula along a rational curve to a polynomial-sign formula.

Retain truth, falsity, conjunction and disjunction; replace each atom by its denominator-cleared polynomial with the
original sign test. -/
def clear (curve : Curve.RationalCurve) :
  BoundaryFormula → PolynomialFormula
  | .truth => .truth
  | .falsity => .falsity
  | .atom atom => .atom (clearedAtom curve atom)
  | .and left right => .and (clear curve left)
    (clear curve right)
  | .or left right => .or (clear curve left)
    (clear curve right)

open Purelib.Data in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Clearing a Hermitian formula preserves its truth at every non-pole parameter.

Each atom is multiplied by the same positive denominator quadrance, and the finite Boolean structure is retained. -/
theorem clear_holds_iff
    (curve : Curve.RationalCurve) (formula : BoundaryFormula) (parameter :
      Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clear curve formula).Holds parameter ↔
      formula.Holds (curve.point parameter) := by
  induction formula with
  | truth =>
      change True ↔ True
      exact iff_of_true True.intro True.intro
  | falsity =>
      change False ↔ False
      exact iff_of_false id id
  | atom value =>
      change (clearedAtom curve value).Holds parameter ↔
        value.Holds (curve.point parameter)
      exact clearedAtom_holds_iff curve value parameter denominatorNonzero
  | and left right leftHypothesis rightHypothesis =>
      change
        ((clear curve left).Holds parameter ∧
          (clear curve right).Holds parameter) ↔
        (left.Holds (curve.point parameter) ∧
          right.Holds (curve.point parameter))
      exact and_congr leftHypothesis rightHypothesis
  | or left right leftHypothesis rightHypothesis =>
      change
        ((clear curve left).Holds parameter ∨
          (clear curve right).Holds parameter) ↔
        (left.Holds (curve.point parameter) ∨
          right.Holds (curve.point parameter))
      exact or_congr leftHypothesis rightHypothesis

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
open Purelib.Data.List in
/-- The compiled atom list is exactly the original atom list mapped through denominator clearing. -/
@[simp] theorem clear_atoms
    (curve : Curve.RationalCurve) (formula : BoundaryFormula) :
    (clear curve formula).atoms =
      formula.atoms.map (clearedAtom curve) := by
  induction formula with
  | truth | falsity =>
      change ([] : List Dense.Rational.Sign.PolynomialAtom) = []
      rfl
  | atom value =>
      change [clearedAtom curve value] = [clearedAtom curve value]
      rfl
  | and left right leftHypothesis rightHypothesis =>
      simp only [clear, PolynomialFormula.atoms,
        BoundaryFormula.atoms, Map.map_append,
        leftHypothesis, rightHypothesis, -eq_self, -iff_self]
      rfl
  | or left right leftHypothesis rightHypothesis =>
      simp only [clear, PolynomialFormula.atoms,
        BoundaryFormula.atoms, Map.map_append,
        leftHypothesis, rightHypothesis, -eq_self, -iff_self]
      rfl

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- List the denominator-cleared polynomial conditions occurring in a curve formula. -/
def conditionPolynomials
    (curve : Curve.RationalCurve) (formula : BoundaryFormula) : List
      Dense.Rational.Basic.CoordinatePolynomial :=
  (clear curve formula).polynomials

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
open Purelib.Data.List in
/-- The condition list is the original atom list mapped to its cleared Hermitian forms. -/
@[simp] theorem conditionPolynomials_eq_map
    (curve : Curve.RationalCurve) (formula : BoundaryFormula) :
    conditionPolynomials curve formula =
      formula.atoms.map fun atom => Curve.Hermitian.clearedForm curve atom.form := by
  rw [conditionPolynomials, PolynomialFormula.polynomials,
    clear_atoms,
    Map.map_map]
  rfl
end Purelib.RationalFunctions.Curve.Hermitian.Formula

end
