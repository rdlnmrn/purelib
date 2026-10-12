module

import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Check
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
Finite source comparison for reloaded integration data.  Local numerical
validity and equality to a fixed source remain distinct.  Each checker
consumes already available source data and returns the restored value with
its source equation, or the exact unequal finite views.  No generator or
completed object is consulted by these comparisons.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Check

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the original path model as its ordered list of executable cell views. -/
def modelView (model : Basic.PathModel) : List Check.CellView
  := model.cells.map Check.cellView

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Equal original cell-view lists give equality of the original ordered cell lists. -/
private theorem cells_injective (first second : List
  Basic.CellModel)
    (equal : first.map Check.cellView = second.map Check.cellView) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> cases equal; rfl
  | cons head tail ih =>
      cases second with
      | nil => cases equal
      | cons otherHead otherTail =>
          have pair := List.cons.inj equal
          rw [Check.cellView_injective head otherHead pair.1, ih otherTail pair.2]

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Equal executable path views identify the exact original path models. -/
theorem modelView_injective (first second : Basic.PathModel)
    (equal : modelView first = modelView second) : first = second := by
  cases first
  cases second
  cases cells_injective _ _ equal
  rfl

open Purelib.Integration.Polynomial.Gaussian.Cell in
set_option genInjectivity false in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Retained unequal executable path views certifying a restored model differs from its original source.

The exact actual and expected readback equalities keep both model owners and their ordered cell data. -/
structure ModelMismatch (restored source : Basic.PathModel)
  where
  /-- The retained restored model's ordered executable cell views. -/ actual : List Check.CellView
  /-- The retained original source model's ordered executable cell views. -/ expected : List Check.CellView
  /-- The actual views read back the exact restored model. -/ actual_eq : actual = modelView restored
  /-- The expected views read back the exact original source model. -/ expected_eq : expected = modelView source
  /-- The retained actual and expected view lists are unequal. -/ different : actual ≠ expected

constructive_injectivity ModelMismatch

open Purelib.Integration.Polynomial.Gaussian.Path
/-- A retained path-view mismatch proves the restored model differs from the original source. -/
theorem ModelMismatch.not_source {restored source :
  Basic.PathModel}
    (failure : ModelMismatch restored source) : restored ≠ source := by
  intro equal
  exact failure.different (failure.actual_eq.trans ((congrArg modelView equal).trans failure.expected_eq.symm))

/-- Check a restored path model against its original source using decidable executable-view equality.

Success returns the same restored model with exact source identity; failure retains both view lists and their certified
inequality. -/
def model (source restored : Basic.PathModel) :
    Except (ModelMismatch restored source) {value : Basic.PathModel // value = source} :=
  let actual := modelView restored
  let expected := modelView source
  if equal : actual = expected then .ok ⟨restored, modelView_injective restored source equal⟩
  else .error ⟨actual, expected, rfl, rfl, equal⟩
end Purelib.Integration.Polynomial.Gaussian.Path.Check

end
