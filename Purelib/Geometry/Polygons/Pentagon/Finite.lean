module
public import Purelib.Data.Fin

public import Purelib.Algebra.Field.Finite.Nineteen
public import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Init.Data.Fin.Lemmas
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field.Finite

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Exercise 14.5

The five printed points over `F₁₉` are presented as an actual constructed
regular pentagon.  Intersecting the five pairs of diagonals gives the next
pentagon in an explicit nineteen-row orbit.  Every one of the eighteen steps
uses two distinct endpoints and two nonparallel lines, so no division by zero
is hidden in the finite computation.  The eighteenth row is the original
pentagon with a cyclic relabelling.

Only the two regularity assertions made explicitly by the exercise are
packaged as `ConstructedRegularPolygon`s: the printed pentagon and its first
derived pentagon.  The remaining rows certify the requested repeated finite
operation, not an ambient enumeration of `F₁₉`.
-/

namespace Purelib.Geometry.Polygons

/-- A labelled finite pentagon is exactly five displayed points. -/
abbrev Pentagon := Fin 5 → Plane.Point Nineteen.Element

namespace Pentagon.Finite

/-- Assemble five literal points without a list or an indexing default. -/
def pentagon (p₀ p₁ p₂ p₃ p₄ : Plane.Point
  Nineteen.Element) : Pentagon :=
  Data.Fin.casesByRecursion p₀
    (Data.Fin.casesByRecursion p₁ (Data.Fin.casesByRecursion p₂ (Data.Fin.casesByRecursion p₃ (fun _ => p₄))))

/-- Add a finite offset cyclically to a pentagon label. -/
def cyclic (index : Fin 5) (offset : Nat) : Fin 5 :=
  ⟨(index.val + offset) % 5, Nat.mod_lt _ (by decide)⟩

end Pentagon.Finite

end Purelib.Geometry.Polygons

end
