module

public import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Exact contact of two original adjacent axis intervals

Closed containment at one rational coordinate leaves three finite cases:
the intervals coincide, the first ends where the second starts, or the
second ends where the first starts. The selected case retains the original
interval payloads; no new coordinate lookup or line certificate is built.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.AxisNeighbors

open Purelib.Data.List
open Purelib.Data.Rat

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- Increasing lower endpoints force the original order of separated intervals. -/
private theorem before_of_lower_lt {intervals : List (ClearGrid.Interval key)}
    (separated : intervals.Pairwise ClearGrid.Interval.Before)
    {first second : ClearGrid.Interval key}
    (firstMember : first ∈ intervals) (secondMember : second ∈ intervals)
    (strict : key first.lower < key second.lower) : ClearGrid.Interval.Before first second := by
  induction intervals with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with same | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with same | secondMember
        · subst second
          exact (lt_irrefl _ strict).elim
        · exact (List.pairwise_cons.mp separated).1 second secondMember
      · rcases Membership.mem_cons.mp secondMember with same | secondMember
        · subst second
          have before := (List.pairwise_cons.mp separated).1 first firstMember
          exact (not_lt_of_ge (head.ordered.le.trans before) strict).elim
        · exact ih (List.pairwise_cons.mp separated).2 firstMember secondMember

/-- A finite contact choice retaining equality of the actual intervals or their touching endpoint readings.

None means the same original interval. Some false means first-upper and
second-lower; some true means first-lower and second-upper. The same closed
coordinate is retained in every case, including endpoints and repetitions.
-/
@[expose] def Contact (first second : ClearGrid.Interval key) (coordinate : Fraction.Rational) : Type :=
  {choice : Option Bool //
    match choice with
    | none => first = second
    | some false => key first.upper = coordinate ∧ key second.lower = coordinate
    | some true => key first.lower = coordinate ∧ key second.upper = coordinate}

/-- Classify two actual adjacent intervals at a common closed coordinate.

The branch decisions inspect only the two stored lower readings. Strict
original axis order supplies equality of the entire interval in the first
case, and exact endpoint contact in either remaining case.
-/
def contactAt {entries : List Alpha}
    (ordered : entries.Pairwise (fun first second => key first < key second))
    {first second : ClearGrid.Interval key}
    (firstMember : first ∈ ClearGrid.Interval.adjacent entries ordered)
    (secondMember : second ∈ ClearGrid.Interval.adjacent entries ordered)
    (coordinate : Fraction.Rational)
    (firstInside : key first.lower ≤ coordinate ∧ coordinate ≤ key first.upper)
    (secondInside : key second.lower ≤ coordinate ∧ coordinate ≤ key second.upper) :
    Contact first second coordinate :=
  if same : key first.lower = key second.lower then
    ⟨none, eq_of_lower ordered firstMember secondMember same⟩
  else if before : key first.lower < key second.lower then
    let separated := before_of_lower_lt (ClearGrid.Interval.adjacent_pairwise entries ordered)
      firstMember secondMember before
    ⟨some false, le_antisymm (separated.trans secondInside.1) firstInside.2,
      le_antisymm secondInside.1 (firstInside.2.trans separated)⟩
  else
    let reverse : key second.lower < key first.lower :=
      lt_of_le_of_ne (le_of_not_gt before) (fun reverse => same reverse.symm)
    let separated := before_of_lower_lt (ClearGrid.Interval.adjacent_pairwise entries ordered)
      secondMember firstMember reverse
    ⟨some true, le_antisymm firstInside.1 (secondInside.2.trans separated),
      le_antisymm (separated.trans firstInside.1) secondInside.2⟩

namespace Contact

variable {first second : ClearGrid.Interval key} {coordinate : Fraction.Rational}
variable (contact : Contact first second coordinate)

/-- The no-contact flag identifies the complete original interval payloads. -/
theorem same (selected : contact.val = none) : first = second := by
  have retained := contact.property
  rewrite [selected] at retained
  exact retained

/-- The forward contact flag retains both actual touching endpoint readings. -/
theorem forward (selected : contact.val = some false) :
    key first.upper = coordinate ∧ key second.lower = coordinate := by
  have retained := contact.property
  rewrite [selected] at retained
  exact retained

/-- The reverse contact flag retains both actual touching endpoint readings. -/
theorem backward (selected : contact.val = some true) :
    key first.lower = coordinate ∧ key second.upper = coordinate := by
  have retained := contact.property
  rewrite [selected] at retained
  exact retained

end Contact
end Purelib.Polynomial.Geometry.Grid.AxisNeighbors

end
