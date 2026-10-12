module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Rat.Fraction
import Init.Prelude

open Purelib

open Purelib.Data.Rat

public section

/-!
Finite source comparison for reloaded integration data.  Local numerical
validity and equality to a fixed source remain distinct.  Each checker
consumes already available source data and returns the restored value with
its source equation, or the exact unequal finite views.  No generator or
completed object is consulted by these comparisons.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Geometric.Control.Check

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.CCL.Progressive.IntegrationReplay (Control)

/-- The pair of rational error-scale and center-bound values determining a finite source control. -/
abbrev ControlView := Fraction.Rational × Fraction.Rational

/-- Read the finite error-scale and center-bound pair from the original control. -/
@[expose] def controlView (control : Control) : Approximation.Gaussian.Sequence.Geometric.Control.Check.ControlView :=
  (control.errorScale, control.centerBound)

/-- Equality of both finite numerical control fields determines equality of the original controls. -/
theorem controlView_injective (first second : Control)
    (equal : Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView first =
      Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView second) : first = second := by
  cases first
  cases second
  have scaleEq := congrArg Prod.fst equal
  have centerEq := congrArg Prod.snd equal
  dsimp only [Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView] at scaleEq centerEq
  cases scaleEq
  cases centerEq
  rfl

set_option genInjectivity false in
/-- An exact mismatch between a restored control and its claimed source.

Both finite views and their readback equalities are retained together with a proof that they differ. -/
structure ControlMismatch (restored source : Control) where
  /-- The retained numerical view of the restored control. -/ actual :
    Approximation.Gaussian.Sequence.Geometric.Control.Check.ControlView
  /-- The retained numerical view of the claimed source control. -/ expected :
    Approximation.Gaussian.Sequence.Geometric.Control.Check.ControlView
  /-- The actual view is exactly the restored control's numerical pair. -/ actual_eq : actual =
    Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView restored
  /-- The expected view is exactly the source control's numerical pair. -/ expected_eq : expected =
    Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView source
  /-- The two retained finite numerical views differ. -/ different : actual ≠ expected

constructive_injectivity ControlMismatch

/-- A certified numerical control mismatch excludes equality with the claimed source. -/
theorem ControlMismatch.not_source {restored source : Control}
    (failure : Approximation.Gaussian.Sequence.Geometric.Control.Check.ControlMismatch restored source) : restored ≠
      source := by
  intro equal
  exact failure.different (failure.actual_eq.trans ((congrArg
    Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView equal).trans failure.expected_eq.symm))

/-- Check a restored finite control against its retained source.

Success returns the restored value with its source equality; failure retains the exact unequal numerical views and their
readback proofs. -/
@[expose] def control (source restored : Control) :
    Except (Approximation.Gaussian.Sequence.Geometric.Control.Check.ControlMismatch restored source) {value : Control //
      value = source} :=
  let actual := Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView restored
  let expected := Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView source
  if equal : actual = expected then .ok ⟨restored,
    Approximation.Gaussian.Sequence.Geometric.Control.Check.controlView_injective restored source equal⟩
  else .error ⟨actual, expected, rfl, rfl, equal⟩

end Purelib.Approximation.Gaussian.Sequence.Geometric.Control.Check

end
