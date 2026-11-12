module

public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Data.Vector.Basic
import Purelib.Data.Fin.Two
import Purelib.Tactic.QuotientFreeOmega

/-! # The original six Legendre differential specifications

The finite table retains the original value, first and second differential
owners in that order. Its three bounded inclusions keep differential
coordinates distinct from cycle coordinates and permit one materialized
arithmetic bank to share its denominator preparation across all six forms.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Specification.Table

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)

/-- The original six forms in value, first and second order, each retaining coordinates zero and one. -/
@[expose] def forms (parameter : Canonical) : Data.Vector (OddPowerDifferential (Paths.polynomial parameter)) 6 :=
  .cons (valueSpecification parameter 0) (.cons (valueSpecification parameter 1)
    (.cons (firstDerivativeSpecification parameter 0) (.cons (firstDerivativeSpecification parameter 1)
      (.cons (secondDerivativeSpecification parameter 0) (.cons (secondDerivativeSpecification parameter 1) .nil)))))

/-- Include the original value differential coordinate in the retained six-form table. -/
@[expose] def valueIndex (coordinate : Fin 2) : Fin 6 :=
  ⟨coordinate.val, Nat.lt_trans coordinate.isLt (by decide +kernel)⟩

/-- Include the original first derivative differential coordinate in the retained six-form table. -/
@[expose] def firstIndex (coordinate : Fin 2) : Fin 6 :=
  ⟨2 + coordinate.val, by have bound := coordinate.isLt; omega0⟩

/-- Include the original second derivative differential coordinate in the retained six-form table. -/
@[expose] def secondIndex (coordinate : Fin 2) : Fin 6 :=
  ⟨4 + coordinate.val, by have bound := coordinate.isLt; omega0⟩

/-- Select the original value or first entry for an adjacent-derivative Taylor row and differential coordinate.

Order zero is the value-to-first row; order one is the first-to-second
row. Both coordinates remain the original differential coordinates, and
selection retains the original six-form table without constructing a form.
-/
@[expose] def baseIndex (order coordinate : Fin 2) : Fin 6 :=
  Fin.cases (valueIndex coordinate)
    (Fin.cases (firstIndex coordinate) (fun index => Fin.elim0 index)) order

/-- Select the original independent derivative entry of that same adjacent-derivative Taylor row. -/
@[expose] def slopeIndex (order coordinate : Fin 2) : Fin 6 :=
  Fin.cases (firstIndex coordinate)
    (Fin.cases (secondIndex coordinate) (fun index => Fin.elim0 index)) order

/-- Each included value entry is the identical original value specification. -/
theorem forms_value (parameter : Canonical) (coordinate : Fin 2) :
    forms parameter (valueIndex coordinate) = valueSpecification parameter coordinate := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- Each included first derivative entry is the identical original first derivative specification. -/
theorem forms_first (parameter : Canonical) (coordinate : Fin 2) :
    forms parameter (firstIndex coordinate) = firstDerivativeSpecification parameter coordinate := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- Each included second derivative entry is the identical original second derivative specification. -/
theorem forms_second (parameter : Canonical) (coordinate : Fin 2) :
    forms parameter (secondIndex coordinate) = secondDerivativeSpecification parameter coordinate := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    rfl
  · subst coordinate
    rfl

end Purelib.Curves.Legendre.Periods.Jets.Specification.Table
