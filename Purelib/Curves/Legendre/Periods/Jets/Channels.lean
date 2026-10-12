module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Periods.Jets.Basic
import Init.Prelude

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Data.Fin

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

/-- The six actual productive channels, in value/first/second and then `a`/`b` order. -/
def channels {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : List Coherent.CoherentNamed :=
  [jet.valueName 0, jet.valueName 1,
    jet.firstName 0, jet.firstName 1,
    jet.secondName 0, jet.secondName 1]

/-- The retained synchronized period jet exposes exactly six productive channels. -/
@[simp] theorem channels_length {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : jet.channels.length = 6 := rfl

/-- Each original value-period output belongs to the retained six-channel table. -/
theorem valueName_mem_channels {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.valueName coordinate ∈ jet.channels := by
  rcases Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.head _
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.tail _ (List.Mem.head _)

/-- Each original first-derivative output belongs to the retained six-channel table. -/
theorem firstName_mem_channels {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.firstName coordinate ∈ jet.channels := by
  rcases Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Each original second-derivative output belongs to the retained six-channel table. -/
theorem secondName_mem_channels {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.secondName coordinate ∈ jet.channels := by
  rcases Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  · subst coordinate
    simp only [channels, -eq_self, -iff_self]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

end Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

end
