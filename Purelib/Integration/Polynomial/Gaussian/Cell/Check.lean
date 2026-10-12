module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)

section
@[expose] public section

/-!
Finite source comparison for reloaded integration data.  Local numerical
validity and equality to a fixed source remain distinct.  Each checker
consumes already available source data and returns the restored value with
its source equation, or the exact unequal finite views.  No generator or
completed object is consulted by these comparisons.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Check

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The executable parameter, reading and error data of an original local polynomial observation.

The view omits proof fields while retaining all observation data needed to recover equality at fixed polynomial and
allowance indices. -/
structure LocalView where
  /-- The original observation's rational parameter. -/ parameter : Fraction.Rational
  /-- The original Gaussian integrand reading. -/ reading : Basic.Canonical
  /-- The original Gaussian observation error. -/ error : Basic.Canonical
deriving DecidableEq

constructive_injectivity LocalView

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The executable endpoint, polynomial, allowance and observation data of an original integration cell.

The ordered coefficient and observation lists retain their original values; decidable view equality certifies exact cell
identity. -/
structure CellView where
  /-- The original cell's start coordinate. -/ start : Basic.Canonical
  /-- The original cell's finish coordinate. -/ finish : Basic.Canonical
  /-- The original polynomial coefficient list in its retained order. -/ coefficients : List Basic.Canonical
  /-- The original cell's local error allowance. -/ allowance : Fraction.Rational
  /-- The original ordered observation views. -/ observations : List LocalView
deriving DecidableEq

constructive_injectivity CellView

section
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending
/-- Read the original local observation's parameter, integrand reading and error. -/
def localView {polynomial :
  CoefficientPolynomial}
  {allowance : Fraction.Rational}
    (value : Basic.LocalObservation polynomial allowance) : LocalView :=
  ⟨value.parameter, value.integrandReading, value.error⟩

/-- At fixed original polynomial and allowance, equal executable observation views give equal observations.

The constructor equivalence identifies the original parameter, integrand
reading and error. Substituting those exact values keeps both supplied
polynomial residual and allowance witnesses at their original indices. -/
theorem localView_injective {polynomial :
  CoefficientPolynomial} {allowance : Fraction.Rational}
    (first second : Basic.LocalObservation polynomial allowance)
    (equal : localView first = localView second) : first = second := by
  cases first with
  | mk parameter reading error decomposition bound =>
    cases second with
    | mk otherParameter otherReading otherError otherDecomposition otherBound =>
      change LocalView.mk parameter reading error =
        LocalView.mk otherParameter otherReading otherError at equal
      rcases (LocalView.mk.injEq parameter reading error
        otherParameter otherReading otherError).mp equal with
        ⟨parameterEq, readingEq, errorEq⟩
      cases parameterEq
      cases readingEq
      cases errorEq
      rfl

/-- Equal ordered executable view lists give equal original indexed observation lists. -/
theorem localViews_injective {polynomial :
  CoefficientPolynomial} {allowance : Fraction.Rational}
    (first second : List (Basic.LocalObservation polynomial allowance))
    (equal : first.map localView = second.map localView) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> cases equal; rfl
  | cons head tail ih =>
      cases second with
      | nil => cases equal
      | cons otherHead otherTail =>
          have pair := List.cons.inj equal
          rw [localView_injective head otherHead pair.1, ih otherTail pair.2]

end

section
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Read the original integration cell's exact executable fields and ordered observation views. -/
def cellView (cell : Basic.CellModel) : CellView :=
  ⟨cell.start, cell.finish, cell.polynomial.coefficients, cell.localAllowance,
    cell.observations.map localView⟩

/-- Equal executable cell views give equality of the exact original integration cells.

The constructor equivalence identifies both original endpoints, the ordered
polynomial coefficients, allowance and observation views. Their scalar
identities recover the same indexed observations and retained order proofs. -/
theorem cellView_injective (first second : Basic.CellModel)
    (equal : cellView first = cellView second) : first = second := by
  cases first with
  | mk start finish polynomial allowance nonnegative observations =>
    cases second with
    | mk otherStart otherFinish otherPolynomial otherAllowance otherNonnegative otherObservations =>
      cases polynomial with
      | mk coefficients =>
        cases otherPolynomial with
        | mk otherCoefficients =>
          change CellView.mk start finish coefficients allowance
            (observations.map localView) =
            CellView.mk otherStart otherFinish otherCoefficients otherAllowance
              (otherObservations.map localView) at equal
          rcases (CellView.mk.injEq start finish coefficients allowance
            (observations.map localView) otherStart otherFinish otherCoefficients
            otherAllowance (otherObservations.map localView)).mp equal with
            ⟨startEq, finishEq, polynomialEq, allowanceEq, observationsEq⟩
          cases startEq
          cases finishEq
          cases polynomialEq
          cases allowanceEq
          cases localViews_injective observations otherObservations observationsEq
          rfl

end

set_option genInjectivity false in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Retained unequal executable views certifying that the restored cell differs from the original source.

Both views carry exact source/readback equalities and the failed equality witness, preserving the two input owners. -/
structure CellMismatch (restored source : Basic.CellModel)
  where
  /-- The retained executable view of the restored cell. -/ actual : CellView
  /-- The retained executable view of the original source cell. -/ expected : CellView
  /-- The actual view is exactly the restored cell's view. -/ actual_eq : actual = cellView restored
  /-- The expected view is exactly the original source cell's view. -/ expected_eq : expected = cellView source
  /-- The retained restored and source views are unequal. -/ different : actual ≠ expected

constructive_injectivity CellMismatch

open Purelib.Integration.Polynomial.Gaussian.Cell
/-- A retained cell-view mismatch proves the restored cell is not the original source cell. -/
theorem CellMismatch.not_source {restored source :
  Basic.CellModel}
    (failure : CellMismatch restored source) : restored ≠ source := by
  intro equal
  exact failure.different (failure.actual_eq.trans ((congrArg cellView equal).trans failure.expected_eq.symm))

/-- Check the restored cell against the original source using decidable executable-view equality.

Success returns that restored cell with its exact original-source identity; failure retains both views and a certified
mismatch. -/
def cell (source restored : Basic.CellModel) :
    Except (CellMismatch restored source) {value : Basic.CellModel // value = source} :=
  let actual := cellView restored
  let expected := cellView source
  if equal : actual = expected then
    .ok ⟨restored, cellView_injective restored source equal⟩
  else .error ⟨actual, expected, rfl, rfl, equal⟩
end Purelib.Integration.Polynomial.Gaussian.Cell.Check

end
