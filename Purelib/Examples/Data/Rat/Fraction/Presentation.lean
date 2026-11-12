module

public import Purelib.Data.Rat.Fraction.Presentation

/-! Finite fraction displays and their canonical readbacks. -/

namespace Purelib.Examples.Data.Rat.Fraction.Presentation

open Purelib.Data.Rat.Fraction

/-- The positive-denominator display one half. -/
@[expose] public def half : Presentation.Display := ⟨(1, 2), by decide⟩

/-- A different positive-denominator display of the same rational. -/
@[expose] public def twoQuarters : Presentation.Display := ⟨(2, 4), by decide⟩

/-- The canonical rational read from the original half display. -/
@[expose] public def halfValue : Rational := Presentation.read half

/-- The two different displays read to the same original rational owner. -/
public theorem sameReadback : Presentation.read half = Presentation.read twoQuarters :=
  (Presentation.same_iff_read_eq half twoQuarters).mp (by decide)

end Purelib.Examples.Data.Rat.Fraction.Presentation
