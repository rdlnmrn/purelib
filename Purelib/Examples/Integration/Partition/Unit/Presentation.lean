module

public import Purelib.Integration.Partition.Unit.Presentation

/-! Construct normalized unit partitions from finite rational cut displays. -/

namespace Purelib.Examples.Integration.Partition.Unit.Presentation

open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- The canonical rational one third. -/
@[expose] public def third : Fraction.Rational := Fraction.normalize ⟨1, 3, by decide⟩

/-- The canonical rational two thirds. -/
@[expose] public def twoThirds : Fraction.Rational := Fraction.normalize ⟨2, 3, by decide⟩

/-- The empty cut display. -/
@[expose] public def empty : Unit.Presentation.Display :=
  ⟨[], ⟨List.Pairwise.nil, fun _ impossible => by nomatch impossible⟩⟩

/-- The ordered display with cuts at one-third and two-thirds. -/
@[expose] public def ordered : Unit.Presentation.Display :=
  ⟨[third, twoThirds], by
    constructor
    · apply List.Pairwise.cons
      · intro cut member
        cases member with
        | head => decide
        | tail _ impossible => nomatch impossible
      · exact List.Pairwise.cons (fun _ impossible => by nomatch impossible) List.Pairwise.nil
    · intro cut member
      cases member with
      | head => decide
      | tail _ later =>
        cases later with
        | head => decide
        | tail _ impossible => nomatch impossible⟩

/-- The original cached partition obtained from the ordered display. -/
@[expose] public def partition : Unit.Normalized := Unit.Presentation.read ordered

/-- The partition retains exactly the two displayed cuts. -/
public theorem retainedCuts : partition.cuts = [third, twoThirds] :=
  Unit.Presentation.read_cuts ordered

end Purelib.Examples.Integration.Partition.Unit.Presentation
