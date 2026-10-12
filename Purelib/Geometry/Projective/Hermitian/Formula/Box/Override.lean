module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Box.Sign
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

section
@[expose] public section

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula.Box

set_option genInjectivity false in
/-- One already-resolved atom that may be reused while structurally reinspecting the same finite formula. -/
structure Override (bounding current :
  Rational.Box) where
  /-- The exact atom whose box stability has already been resolved. -/ atom : Hermitian.Atom
  /-- Sign stability for the retained atom on this current box. -/ stability : Formula.Box.AtomStability atom bounding
    current

constructive_injectivity Override

namespace Override

/-- Equality ownership for a form proved identically zero on the current box. -/
def zero
    {bounding current : Rational.Box} (atom : Hermitian.Atom)
    (evaluatesZero : ∀ value, current.Contains value →
      atom.form.eval value = 0) : Override bounding current :=
  ⟨atom, .zero evaluatesZero⟩

end Override

set_option genInjectivity false in
/-- One resolved form sign, reusable for every occurrence and every sign tag of that form. -/
structure FormOverride (current : Rational.Box)
  where
  /-- The exact Hermitian form whose sign has been resolved. -/ form : Hermitian.HermitianForm
  /-- The retained sign certificate for this form on the current box. -/ stability : Formula.Box.FormStability form
    current

constructive_injectivity FormOverride

namespace FormOverride

/-- Cache a form together with its strict positivity throughout the box. -/
def positive
    {current : Rational.Box} (form : Hermitian.HermitianForm)
    (holds : ∀ value, current.Contains value → 0 < form.eval value) :
    FormOverride current :=
  ⟨form, .positive holds⟩

/-- Cache a form together with its vanishing throughout the box. -/
def zero
    {current : Rational.Box} (form : Hermitian.HermitianForm)
    (holds : ∀ value, current.Contains value → form.eval value = 0) :
    FormOverride current :=
  ⟨form, .zero holds⟩

/-- A resolved form sign remains resolved on every displayed subbox. -/
def refine
    {outer inner : Rational.Box} (override : FormOverride
      outer)
    (refines : inner.Refines outer) : FormOverride inner :=
  match override.stability with
  | .negative holds =>
      ⟨override.form, .negative fun value inside =>
        holds value (refines.contains inside)⟩
  | .positive holds =>
      ⟨override.form, .positive fun value inside =>
        holds value (refines.contains inside)⟩
  | .zero holds =>
      ⟨override.form, .zero fun value inside =>
        holds value (refines.contains inside)⟩

/-- Restricting a cached sign certificate preserves the original form. -/
@[simp] theorem refine_form
    {outer inner : Rational.Box} (override : FormOverride
      outer)
    (refines : inner.Refines outer) :
    (override.refine refines).form = override.form := by
  rcases override with ⟨form, stability⟩
  cases stability <;> rfl

end FormOverride

/-- Find the first cached form equal to the target and transport its sign certificate.

Return `none` exactly when the finite search finds no matching form. -/
def findFormOverride
    {current : Purelib.Geometry.Rational.Box} (overrides : List
      (FormOverride current))
    (target : Purelib.Geometry.Projective.Hermitian.HermitianForm) :
    Option (Purelib.Geometry.Projective.Hermitian.Formula.Box.FormStability target current) :=
  match overrides with
  | [] => none
  | entry :: remaining =>
      if equal : entry.form = target then
        some (equal ▸ entry.stability)
      else
        findFormOverride remaining target

/-- Look up an exact atom match in a finite list of resolved boundaries. -/
def findOverride
    {bounding current : Purelib.Geometry.Rational.Box} (overrides : List
      (Override bounding current))
    (target : Purelib.Geometry.Projective.Hermitian.Atom) : Option
      (Purelib.Geometry.Projective.Hermitian.Formula.Box.AtomStability target bounding current) :=
  match overrides with
  | [] => none
  | entry :: remaining =>
      if equal : entry.atom = target then
        some (equal ▸ entry.stability)
      else
        findOverride remaining target

/-- Reuse a resolved equality boundary when present; otherwise execute the ordinary strict-margin comparison. -/
def atomStability?
    {bounding current : Rational.Box} (overrides : List
      (Override bounding current))
    (refines : current.Refines bounding) (sample : Data.Gaussian.Basic.Canonical)
    (sampleInside : current.Contains sample) (atom : Hermitian.Atom) :
    Option (Formula.Box.AtomStability atom bounding current) :=
  match findOverride overrides atom with
  | some stability => some stability
  | none =>
      match Hermitian.Box.certificate?
          atom.form bounding current refines sample sampleInside with
      | none => none
      | some certificate => some (.strict certificate)
end Purelib.Geometry.Projective.Hermitian.Formula.Box

end
