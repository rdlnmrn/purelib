module

public import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Integration.Program.Gaussian.Basic

/-! # The six original synchronized integral programmes

These views read the retained value, first and second programmes directly.
They introduce no numerical request, output-name sampling or new cycle.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Curves.Legendre.Periods.Jets.Specification

variable {parameter : Canonical} {frame : Paths.Frame parameter}

/-- Read one original integral programme in the retained six-form table order. -/
@[expose] def programme (jet : SynchronizedPeriodJet frame) (channel : Fin 6) : RefinementProgram :=
  Fin.cases (jet.value 0).integral
    (Fin.cases (jet.value 1).integral
      (Fin.cases (jet.first 0).integral
        (Fin.cases (jet.first 1).integral
          (Fin.cases (jet.second 0).integral
            (Fin.cases (jet.second 1).integral (fun index => Fin.elim0 index)))))) channel

/-- The two value-table entries are the identical original certified programmes. -/
theorem programme_value (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.programme (Table.valueIndex coordinate) = (jet.value coordinate).integral := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) coordinate <;> rfl

/-- The two first-table entries are the identical original certified programmes. -/
theorem programme_first (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.programme (Table.firstIndex coordinate) = (jet.first coordinate).integral := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) coordinate <;> rfl

/-- The two second-table entries are the identical original certified programmes. -/
theorem programme_second (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.programme (Table.secondIndex coordinate) = (jet.second coordinate).integral := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) coordinate <;> rfl

/-- Each base row reads its actual value or first programme on that SAME jet. -/
theorem programme_base (jet : SynchronizedPeriodJet frame) (order coordinate : Fin 2) :
    jet.programme (Table.baseIndex order coordinate) =
      Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) (jet.value coordinate).integral
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) (jet.first coordinate).integral
          (fun index => Fin.elim0 index)) order := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact jet.programme_value coordinate
  · exact jet.programme_first coordinate

/-- Each slope row reads its actual first or second programme on that SAME jet. -/
theorem programme_slope (jet : SynchronizedPeriodJet frame) (order coordinate : Fin 2) :
    jet.programme (Table.slopeIndex order coordinate) =
      Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) (jet.first coordinate).integral
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) (jet.second coordinate).integral
          (fun index => Fin.elim0 index)) order := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact jet.programme_first coordinate
  · exact jet.programme_second coordinate

end Purelib.Curves.Legendre.Periods.Jets.Basic.SynchronizedPeriodJet

end
