module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse

/-! # Dependent folds on the original cap-comparison bank

The original indexed bank supplies its head data and literal tail. A
dependent algebra consumes those same owners. Structural recursion remains
abstract in the result family, including when the result is a function on
separately retained request or observation caches.
-/

public section

universe u v

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus}
    {motive : {parents : List (Parent curve differential)} → Bank cap differential count parents → Type u}

/-- Fold the literal bank with a dependent algebra preserving each original head and tail owner.

The result family stays abstract during structural recursion. A function
result delays actual tail traversal until the supplied head algebra
invokes the original tail function; no parent or preparation is rebuilt.
-/
def fold (empty : motive .nil)
    (step : {parent : Parent curve differential} → {parents : List (Parent curve differential)} →
      (data : ParentData cap differential count parent) → (rest : Bank cap differential count parents) →
        (Unit → motive rest) → motive (.cons data rest)) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) → motive bank
  | _, .nil => empty
  | _, .cons data rest => step data rest (fun _ => fold empty step rest)
termination_by structural _ bank => bank

/-- The empty bank returns the algebra's original empty value. -/
theorem fold_nil (empty : motive .nil)
    (step : {parent : Parent curve differential} → {parents : List (Parent curve differential)} →
      (data : ParentData cap differential count parent) → (rest : Bank cap differential count parents) →
        (Unit → motive rest) → motive (.cons data rest)) :
    fold empty step .nil = empty := by rfl

/-- A cons bank applies the algebra to the same head, literal tail and delayed original tail fold. -/
theorem fold_cons (empty : motive .nil)
    (step : {parent : Parent curve differential} → {parents : List (Parent curve differential)} →
      (data : ParentData cap differential count parent) → (rest : Bank cap differential count parents) →
        (Unit → motive rest) → motive (.cons data rest))
    {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents) :
    fold empty step (.cons data rest) = step data rest (fun _ => fold empty step rest) := by rfl

/-- An observation of a cons fold reads the same head algebra and its delayed original tail.

The equality retains the chosen observation's result type. It does not
first compare values in a possibly dependent function-valued motive.
-/
theorem fold_cons_observe (empty : motive .nil)
    (step : {parent : Parent curve differential} → {parents : List (Parent curve differential)} →
      (data : ParentData cap differential count parent) → (rest : Bank cap differential count parents) →
        (Unit → motive rest) → motive (.cons data rest))
    {parent : Parent curve differential} {parents : List (Parent curve differential)}
    (data : ParentData cap differential count parent) (rest : Bank cap differential count parents)
    {Value : Sort v} (observe : motive (.cons data rest) → Value) :
    observe (fold empty step (.cons data rest)) =
      observe (step data rest (fun _ => fold empty step rest)) := by rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

end
