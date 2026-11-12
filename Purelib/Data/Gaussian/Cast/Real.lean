module

public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Certified real-axis coefficient readback

Inspection reads an exact Gaussian coefficient as its original rational real
coordinate when the imaginary coordinate is zero. Finite list inspection
retains every original key and all nonreal coefficients; it performs no
numerical sampling or branch selection.
-/

public section

namespace Purelib.Data.Gaussian.Cast

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

/-- Real-axis inclusion preserves the original unit coefficient. -/
theorem ofCoordinate_one : CoordinateTaylor.ofCoordinate 1 = 1 := rfl

/-- Real-axis inclusion preserves the original coordinate's negation. -/
theorem ofCoordinate_neg (value : Rational) :
    CoordinateTaylor.ofCoordinate (-value) = -CoordinateTaylor.ofCoordinate value := by
  apply Basic.ext
  · rfl
  · change (0 : Rational) = -0
    exact (_root_.neg_zero : -(0 : Rational) = 0).symm

/-- Exact real-axis inclusion identifies rational coordinates only when they are equal. -/
theorem ofCoordinate_injective : Function.Injective CoordinateTaylor.ofCoordinate :=
  fun _ _ equal => congrArg Basic.re equal

set_option genInjectivity false in
/-- An exact real-axis reading or the original coefficient's proved nonzero imaginary coordinate. -/
inductive RealView (value : Canonical) where
  /-- Retain the rational coordinate and its exact equality to the original Gaussian coefficient. -/
  | real (coordinate : Rational) (value_eq : value = CoordinateTaylor.ofCoordinate coordinate)
  /-- Prove that the original Gaussian coefficient is outside the real axis. -/
  | complex (imaginary_ne : value.im ≠ 0)

constructive_injectivity RealView

/-- Inspect exact retained coordinates to read the real axis or its proved violated condition. -/
@[expose] def inspectReal (value : Canonical) : RealView value :=
  if real : value.im = 0 then .real value.re (Basic.ext rfl real)
  else .complex real

/-- A real-axis inspection has a retained exact rational reading. -/
@[expose] def RealView.Complete {value : Canonical} : RealView value → Prop
  | .real _ _ => True
  | .complex _ => False

/-- Decide completeness using the actual retained real-axis inspection constructor. -/
instance RealView.completeDecidable {value : Canonical} (view : RealView value) : Decidable view.Complete :=
  match view with
  | .real _ _ => isTrue True.intro
  | .complex _ => isFalse (fun impossible => impossible)

set_option genInjectivity false in
/-- Every exact coefficient inspection in a finite original keyed list. -/
inductive RealListView {I : Type} : List (I × Canonical) → Type where
  /-- The empty original list has no nonreal coefficient. -/
  | nil : RealListView []
  /-- Retain the current original coefficient's inspection and the complete original tail's inspections. -/
  | cons {first : I × Canonical} {remaining : List (I × Canonical)}
      (head : RealView first.2) (tail : RealListView remaining) : RealListView (first :: remaining)

constructive_injectivity RealListView

/-- Inspect every actual keyed coefficient once, retaining all exact readings and all nonreal conditions. -/
@[expose] def inspectRealList {I : Type} : (entries : List (I × Canonical)) → RealListView entries
  | [] => .nil
  | first :: remaining => .cons (inspectReal first.2) (inspectRealList remaining)

/-- Every retained coefficient inspection has an exact rational reading. -/
@[expose] def RealListView.Complete {I : Type} : {entries : List (I × Canonical)} → RealListView entries → Prop
  | [], .nil => True
  | _ :: _, .cons head tail => head.Complete ∧ tail.Complete

/-- Decide real-axis completeness from the entire actual retained coefficient inspection tree. -/
instance RealListView.completeDecidable {I : Type} :
    {entries : List (I × Canonical)} → (view : RealListView entries) → Decidable view.Complete
  | [], .nil => isTrue True.intro
  | _ :: _, .cons head tail =>
      letI := completeDecidable tail
      inferInstanceAs (Decidable (head.Complete ∧ tail.Complete))

/-- Read the original keys and exact rational coordinates from a complete retained coefficient inspection. -/
@[expose] def RealListView.coordinates {I : Type} :
    {entries : List (I × Canonical)} → (view : RealListView entries) → view.Complete → List (I × Rational)
  | [], .nil, _ => []
  | first :: _, .cons (.real coordinate _) tail, complete =>
      (first.1, coordinate) :: coordinates tail complete.2
  | _ :: _, .cons (.complex _) _, complete => False.elim complete.1

/-- The exact rational coordinate list reconstructs every original keyed Gaussian coefficient. -/
theorem RealListView.coordinates_eq {I : Type} {entries : List (I × Canonical)}
    (view : RealListView entries) (complete : view.Complete) :
    entries = (view.coordinates complete).map (fun entry => (entry.1, CoordinateTaylor.ofCoordinate entry.2)) := by
  induction entries with
  | nil => cases view; rfl
  | cons first remaining ih =>
      cases view with
      | cons head tail =>
          cases head with
          | real coordinate same =>
              change first :: remaining = (first.1, CoordinateTaylor.ofCoordinate coordinate) :: _
              have first_eq : first = (first.1, CoordinateTaylor.ofCoordinate coordinate) := by
                cases first with
                | mk key coefficient => exact congrArg (fun value => (key, value)) same
              exact congrArg₂ List.cons first_eq (ih tail complete.2)
          | complex different => exact False.elim complete.1

end Purelib.Data.Gaussian.Cast

end
