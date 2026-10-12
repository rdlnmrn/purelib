module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
section
@[expose] public section

/-!
# Finite rational L1 error

The exact integral of pointwise rational separation gives a finite analogue
of L1 distance.  It supports the metric-style inequalities and controls
expectation error by direct finite summation.  Indicator distance is exactly
the probability or content of an executable symmetric difference.

No function-space completion, equivalence class, convergence mode, or limit
is constructed.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution
end Distribution

open Purelib.Data.Rat in
/-- Select payloads whose two rational observations have separation at least the supplied threshold. -/
def separationAtLeast {α : Type} (threshold : Fraction.Rational)
    (left right : α → Fraction.Rational) : α → Bool :=
  fun item => decide
    (threshold ≤ Distance.rationalSeparation (left item) (right item))

/-- Select payloads on which the two Boolean events disagree. -/
def symmetricDifferenceEvent {α : Type}
    (first second : α → Bool) : α → Bool :=
  fun item => first item != second item

open Purelib.Data.Rat in
/-- The rational separation of two event indicators is the indicator of their symmetric difference. -/
theorem indicator_rationalSeparation
    {α : Type} (first second : α → Bool) (item : α) :
    Distance.rationalSeparation
        (Distribution.indicator first item)
        (Distribution.indicator second item) =
      Distribution.indicator (symmetricDifferenceEvent first second) item := by
  cases firstSelected : first item <;>
    cases secondSelected : second item <;>
    simp only [Distance.rationalSeparation, Distribution.indicator,
      symmetricDifferenceEvent, firstSelected, secondSelected] <;>
    decide

namespace Content
end Content

namespace Distribution
end Distribution

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite uniform-integrability tail budgets

The absolute tail of one rational observable is an executable threshold event
and an exact rational integral.  A second-moment bound controls this tail by
`poweredL2 / threshold`.  A displayed finite family with one common
second-moment ceiling therefore has one uniform rational tail budget.

This retains the quantitative finite content used in uniform-integrability
arguments without quantifying over an infinite family or taking a limit as
the threshold tends to infinity.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat in
/-- Select payloads whose rational observation has magnitude at least the supplied threshold. -/
def absoluteTailEvent {α : Type} (threshold : Fraction.Rational)
    (value : α → Fraction.Rational) : α → Bool :=
  fun item => decide (threshold ≤ Distance.rationalSeparation (value item) 0)

end Distribution

end Purelib.Measure

end
