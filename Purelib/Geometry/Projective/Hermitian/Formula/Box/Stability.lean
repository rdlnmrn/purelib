module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Basic
public import Purelib.Geometry.Projective.Hermitian.Box.Sign
public import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

set_option genInjectivity false in
/-- An atom is stable either because its form has one strict sign throughout the box or because the form is identically
zero there. The latter is the finite equality-owner case: the atom's weak/strict convention decides its truth value once
and for all at zero. -/
inductive AtomStability (atom : Hermitian.Atom) (bounding
  current : Rational.Box) where
  /-- Retain a strict-sign certificate relative to the bounding and current boxes. -/ | strict (certificate :
    Hermitian.Box.Certificate
      atom.form bounding current)
  /-- The atom form is strictly negative throughout the current box. -/ | negative (holds : ∀ value, current.Contains
    value →
      atom.form.eval value < 0)
  /-- The atom form is strictly positive throughout the current box. -/ | positive (holds : ∀ value, current.Contains
    value →
      0 < atom.form.eval value)
  /-- The atom form vanishes throughout the current box. -/ | zero (evaluatesZero : ∀ value, current.Contains value →
      atom.form.eval value = 0)

constructive_injectivity AtomStability

/-- Form-sign stability is independent of the atom's weak/strict sign tag and can therefore be reused by either child
formula. -/
inductive FormStability (form : Hermitian.HermitianForm)
    (current : Rational.Box) where
  /-- The form is strictly negative at every point in the box. -/ | negative (holds : ∀ value, current.Contains value →
    form.eval value < 0)
  /-- The form is strictly positive at every point in the box. -/ | positive (holds : ∀ value, current.Contains value →
    0 < form.eval value)
  /-- The form vanishes at every point in the box. -/ | zero (holds : ∀ value, current.Contains value → form.eval value
    = 0)

/-- Use the retained form sign as stability evidence for any atom with that form. -/
@[expose] def FormStability.toAtom
    {atom : Hermitian.Atom} {bounding current : Rational.Box}
    (stability : FormStability atom.form current) :
    AtomStability atom bounding current :=
  match stability with
  | .negative holds => .negative holds
  | .positive holds => .positive holds
  | .zero holds => .zero holds

/-- Strict sign of the underlying form makes every weak, strict, equality, and disequality atom test constant throughout
the box. -/
theorem atom_holds_iff
    {atom : Hermitian.Atom} {bounding current : Rational.Box}
    (stability : AtomStability atom bounding current)
    {left right : Data.Gaussian.Basic.Canonical} (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    atom.Holds left ↔ atom.Holds right := by
  cases stability with
  | strict certificate =>
      cases certificate.strictSign with
      | negative negative =>
          exact SignTest.holds_iff_of_negative atom.sign
            (negative left leftInside) (negative right rightInside)
      | positive positive =>
          exact SignTest.holds_iff_of_positive atom.sign
            (positive left leftInside) (positive right rightInside)
  | negative negative =>
      exact SignTest.holds_iff_of_negative atom.sign
        (negative left leftInside) (negative right rightInside)
  | positive positive =>
      exact SignTest.holds_iff_of_positive atom.sign
        (positive left leftInside) (positive right rightInside)
  | zero evaluatesZero =>
      unfold Atom.Holds
      rw [evaluatesZero left leftInside, evaluatesZero right rightInside]

set_option genInjectivity false in
/-- Structural evidence that every atom of a finite formula has a fixed sign on the box.

Each atom retains strict-sign or identically-zero evidence; conjunctions and disjunctions retain stability for both
branches. -/
inductive Stable (bounding current :
  Rational.Box) : Formula.BoundaryFormula → Type where
  /-- The constant true formula is stable. -/ | truth : Stable
    bounding current .truth
  /-- The constant false formula is stable. -/ | falsity : Stable
    bounding current .falsity
  /-- Retain the sign stability of this atom. -/ | atom (value : Hermitian.Atom)
      (stability : AtomStability value bounding current) :
      Stable bounding current (.atom value)
  /-- A conjunction is stable when both constituent formulas are stable. -/ | and {left right : Formula.BoundaryFormula}
      (leftStable : Stable bounding current left)
      (rightStable : Stable bounding current right) :
      Stable bounding current (.and left right)
  /-- A disjunction is stable when both constituent formulas are stable. -/ | or {left right : Formula.BoundaryFormula}
      (leftStable : Stable bounding current left)
      (rightStable : Stable bounding current right) :
      Stable bounding current (.or left right)

constructive_injectivity Stable

namespace Stable

/-- A stable formula has the same truth value at every two points in the certified box. -/
theorem holds_iff
    {bounding current : Rational.Box} {formula : Formula.BoundaryFormula}
    (stable : Stable bounding current formula)
    {left right : Data.Gaussian.Basic.Canonical} (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    formula.Holds left ↔ formula.Holds right := by
  induction stable with
  | truth => exact iff_of_true True.intro True.intro
  | falsity => exact iff_of_false id id
  | atom value stability =>
      exact atom_holds_iff stability leftInside rightInside
  | and leftStable rightStable leftHypothesis rightHypothesis =>
      exact and_congr leftHypothesis rightHypothesis
  | or leftStable rightStable leftHypothesis rightHypothesis =>
      exact or_congr leftHypothesis rightHypothesis

end Stable
end Purelib.Geometry.Projective.Hermitian.Formula.Box

end
