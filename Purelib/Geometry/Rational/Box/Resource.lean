module
public import Purelib.Data.Rat.Fraction.Resource.Model
public import Purelib.Geometry.Rational.Box.Basic

import Init.Prelude
import Purelib.Data.Nat.Order
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Endpoint magnitudes of rational boxes

The coordinate predicate bounds each of the four retained endpoints. Their displayed maximum supplies an initial bound
without changing the box or its coordinate representations.
-/

namespace Purelib.Geometry.Rational.Box.Resource

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry

/-! ## Persistent box records through repeated refinement -/

/-- All four endpoint coordinate magnitudes are bounded by the supplied natural number.

The conjunction concerns the canonical representation magnitude of each retained endpoint, with one common natural
bound. -/
@[expose] public def BoxWithin (box : Rational.Box) (bound : Nat) : Prop :=
  Fraction.Resource.Model.coordinateMagnitude box.xLower ≤ bound ∧
    Fraction.Resource.Model.coordinateMagnitude box.xUpper ≤ bound ∧
    Fraction.Resource.Model.coordinateMagnitude box.yLower ≤ bound ∧
    Fraction.Resource.Model.coordinateMagnitude box.yUpper ≤ bound

/-- The maximum representation magnitude of the four rational endpoints.

The nested maximum uses the four endpoints of the supplied box without changing their rational representations. -/
@[expose] public def boxMagnitude (box : Rational.Box) : Nat :=
  max (Fraction.Resource.Model.coordinateMagnitude box.xLower)
    (max (Fraction.Resource.Model.coordinateMagnitude box.xUpper)
      (max (Fraction.Resource.Model.coordinateMagnitude box.yLower)
        (Fraction.Resource.Model.coordinateMagnitude box.yUpper)))

/-- The computed endpoint magnitude bounds every endpoint of the box.

Each endpoint is one of the retained maximum arguments. The corresponding natural maximum inequalities establish the
four components of BoxWithin. -/
public theorem box_within_boxMagnitude (box : Rational.Box) :
    Geometry.Rational.Box.Resource.BoxWithin box (Geometry.Rational.Box.Resource.boxMagnitude box) := by
  simp only [BoxWithin, boxMagnitude, Data.Nat.Order.max_eq_natMax]
  exact ⟨Data.Nat.Order.le_max_left _ _,
    Nat.le_trans (Data.Nat.Order.le_max_left _ _) (Data.Nat.Order.le_max_right _ _),
    Nat.le_trans (Data.Nat.Order.le_max_left _ _)
      (Nat.le_trans (Data.Nat.Order.le_max_right _ _) (Data.Nat.Order.le_max_right _ _)),
    Nat.le_trans (Data.Nat.Order.le_max_right _ _)
      (Nat.le_trans (Data.Nat.Order.le_max_right _ _) (Data.Nat.Order.le_max_right _ _))⟩

end Purelib.Geometry.Rational.Box.Resource
