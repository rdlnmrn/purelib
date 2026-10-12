module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Map

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval)

open Purelib.Data.Rat

open Purelib.Polynomial

@[expose] public section

/-! A proper retained interval has an actual neighbor or meets the certified
frame endpoint. Absence is proved by coordinate equality, not a timeout. -/
namespace Purelib.Polynomial.Geometry.Grid.FramedAxisNeighbors

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}
  {entries : List Alpha} {ordered : entries.Pairwise (fun first second => key first < key second)}

set_option genInjectivity false in
/-- A retained next axis interval or exact evidence that the current upper endpoint is the frame boundary.

The next interval belongs to the original adjacent-interval bank and starts at the current interval's upper coordinate.
-/
inductive Successor (entries : List Alpha)
    (ordered : entries.Pairwise (fun first second => key first < key second))
    (current : Interval key) (upper : Fraction.Rational) where
  /-- The original adjacent interval starting at the current upper coordinate. -/ | next (endpoint :
    Geometry.Grid.AxisNeighbors.AtEndpoint (Interval.adjacent entries ordered) (key
    current.upper) false)
  /-- The current upper coordinate equals the retained upper frame coordinate. -/ | exterior (equal : key current.upper
    = upper)

constructive_injectivity Successor

set_option genInjectivity false in
/-- A retained previous axis interval or exact evidence that the current lower endpoint is the frame boundary.

The previous interval belongs to the original adjacent-interval bank and ends at the current interval's lower
coordinate. -/
inductive Predecessor (entries : List Alpha)
    (ordered : entries.Pairwise (fun first second => key first < key second))
    (current : Interval key) (lower : Fraction.Rational) where
  /-- The original adjacent interval ending at the current lower coordinate. -/ | previous (endpoint :
    Geometry.Grid.AxisNeighbors.AtEndpoint (Interval.adjacent entries ordered) (key
    current.lower) true)
  /-- The current lower coordinate equals the retained lower frame coordinate. -/ | exterior (equal : key current.lower
    = lower)

constructive_injectivity Predecessor

/-- Locate the next retained interval or certify equality with the upper frame boundary.

The current interval belongs to the original strictly ordered axis, whose retained upper frame coordinate bounds every
entry. -/
def Successor.build (current : Interval key) (member : current ∈
  Interval.adjacent entries ordered)
    (upper : Fraction.Rational) (frame : upper ∈ entries.map key)
    (bounds : ∀ entry ∈ entries, key entry ≤ upper) : Successor entries ordered
      current upper :=
  open Purelib in match Geometry.Grid.AxisNeighbors.neighbors (key current.upper) entries ordered
      (Data.List.Map.mem_map_of_mem (Interval.endpoints_mem _ _ member).2) with
  | .first after _ => .next after
  | .interior _ after => .next after
  | .last _ maximum => .exterior (by
      obtain ⟨last, belongs, equal⟩ := Data.List.Map.mem_map.mp frame
      exact le_antisymm (bounds current.upper (Interval.endpoints_mem _ _ member).2)
        (equal.symm.trans_le (maximum last belongs)))
  | .singleton only => False.elim (by
      have equal := only current.lower (Interval.endpoints_mem _ _ member).1
      exact (ne_of_lt current.ordered) equal)

/-- Locate the previous retained interval or certify equality with the lower frame boundary.

The current interval belongs to the original strictly ordered axis, whose retained lower frame coordinate bounds every
entry. -/
def Predecessor.build (current : Interval key) (member : current ∈
  Interval.adjacent entries ordered)
    (lower : Fraction.Rational) (frame : lower ∈ entries.map key)
    (bounds : ∀ entry ∈ entries, lower ≤ key entry) : Predecessor entries ordered
      current lower :=
  open Purelib in match Geometry.Grid.AxisNeighbors.neighbors (key current.lower) entries ordered
      (Data.List.Map.mem_map_of_mem (Interval.endpoints_mem _ _ member).1) with
  | .last before _ => .previous before
  | .interior before _ => .previous before
  | .first _ minimum => .exterior (by
      obtain ⟨first, belongs, equal⟩ := Data.List.Map.mem_map.mp frame
      exact le_antisymm ((minimum first belongs).trans_eq equal)
        (bounds current.lower (Interval.endpoints_mem _ _ member).1))
  | .singleton only => False.elim (by
      have equal := only current.upper (Interval.endpoints_mem _ _ member).2
      exact (ne_of_lt current.ordered) equal.symm)

end Purelib.Polynomial.Geometry.Grid.FramedAxisNeighbors
