module

public import Purelib.Data.Presentation
public import Purelib.Geometry.Gaussian.UnitCircle.Basic

namespace Purelib.Geometry.Gaussian.UnitCircle.Presentation

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Basic

/-- A Gaussian rational is admissible as a unit vertex when its squared norm is one. -/
@[expose] public def Valid (code : Canonical) : Prop := Norm.Basic.normSq code = 1

set_option genInjectivity false in
/-- The result of checking a Gaussian rational for exact unit quadrance. -/
public inductive Check (code : Canonical) where
  /-- The point has exact unit quadrance. -/ | valid (unit : Valid code)
  /-- The point does not have exact unit quadrance. -/ | notUnit (notUnit : ¬ Valid code)

/-- Decide exact unit quadrance, retaining a proof in either branch. -/
@[expose] public def check (code : Canonical) : Check code :=
  if unit : Norm.Basic.normSq code = 1 then .valid unit else .notUnit unit

/-- Decide admissibility through the same typed quadrance checker. -/
@[expose] public def recognize (code : Canonical) : Decidable (Valid code) :=
  match check code with
  | .valid unit => .isTrue unit
  | .notUnit notUnit => .isFalse notUnit

/-- Decide the exact unit-quadrance predicate. -/
public instance (code : Canonical) : Decidable (Valid code) := recognize code

/-- A Gaussian rational with an exact unit-quadrance certificate. -/
public abbrev Display := {code : Canonical // Valid code}

/-- Construct the original unit vertex from accepted coordinates. -/
@[expose] public def read (display : Display) : UnitVertex :=
  ⟨display.val, display.property⟩

/-- Quote an original unit vertex by its retained point and certificate. -/
@[expose] public def quote (vertex : UnitVertex) : Display :=
  ⟨vertex.value, vertex.unit⟩

/-- Two displays are the same precisely when their retained Gaussian points agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the two retained finite Gaussian rational coordinates. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Decide the equality of two valid unit-vertex displays. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Reading the quotation of an original vertex recovers that original vertex. -/
public theorem read_quote (vertex : UnitVertex) : read (quote vertex) = vertex :=
  UnitVertex.eq_of_value_eq rfl

/-- Quoting a displayed vertex after reading it recovers the original display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Display equality is exactly equality of the original unit vertices. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    exact UnitVertex.eq_of_value_eq same
  · intro same
    exact congrArg UnitVertex.value same

/-!
## Unit vertices

* **Object and expressions:** a code is an original Gaussian rational
  `Canonical`, consisting of its two retained canonical rational coordinates.
* **Recognition:** `check` computes `Norm.Basic.normSq` and decides its equality
  to one. `Check.notUnit` retains a proof that the condition fails.
* **Equality:** `compare` decides coordinate equality. `same_iff_read_eq`
  identifies this with equality of the original `UnitVertex`, not equality of
  angles, parametrizations or enclosing polygons.
* **Constructions and operations:** `read` constructs the original owner and
  `quote` projects its existing value and unit proof; both round trips hold.
* **Termination and dependencies:** the quadrance is a finite rational expression;
  its equality decision and Gaussian coordinate equality are the original finite
  decisions. Proof-system, construction-admission and native-runtime accounts
  are inherited separately and are not certified by this presentation.
* **Examples and non-examples:** the original indexed polygon vertices are
  admitted; the Gaussian zero and the point `(1, 1)` have nonunit quadrance.
-/
/-- The explicit presentation of original unit vertices by their retained coordinates. -/
@[expose] public def unitVertex : Purelib.Data.Presentation Canonical where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Geometry.Gaussian.UnitCircle.Presentation
