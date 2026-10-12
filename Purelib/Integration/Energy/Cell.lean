module

import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite positive-energy certificates for the second bilinear relation

The second Riemann bilinear relation is used only through finite rational
data.  A request displays finitely many surface cells, a nonnegative area and
density lower bound on each cell, and one cell on which both bounds are
strictly positive.  Their finite energy sum must dominate the automatically
computed period-matrix enclosure budget and must be bounded above by the
displayed normalized quadratic form.

Consequently positivity is derived from cell energy and finite summation; it
is not accepted as a direct positivity assertion about a completed matrix.
-/

namespace Purelib.Integration.Energy

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retained nonnegative rational lower bounds for a cell's area and density. -/
structure Cell where
  /-- The retained rational lower bound for cell area. -/ areaLower : Fraction.Rational
  /-- The retained rational lower bound for cell density. -/ densityLower : Fraction.Rational
  /-- The retained area lower bound is nonnegative. -/ areaLower_nonnegative : 0 <= areaLower
  /-- The retained density lower bound is nonnegative. -/ densityLower_nonnegative : 0 <= densityLower

constructive_injectivity Cell

namespace Cell.mk

end Cell.mk

namespace Cell.mk

end Cell.mk

namespace Cell

open Purelib
open Purelib.Data.Rat
/-- Multiply the exact retained area and density lower bounds. -/
def contribution (cell : Cell) : Fraction.Rational
  :=
  cell.areaLower * cell.densityLower

/-- The retained cell energy contribution is nonnegative. -/
theorem contribution_nonnegative (cell : Cell) :
    0 <= cell.contribution :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    cell.areaLower_nonnegative cell.densityLower_nonnegative

/-- Strictly positive retained area and density bounds make the cell contribution strictly positive. -/
theorem contribution_positive (cell : Cell)
    (areaPositive : 0 < cell.areaLower)
    (densityPositive : 0 < cell.densityLower) :
    0 < cell.contribution :=
  Fraction.Order.Arithmetic.mul_pos_direct areaPositive densityPositive

end Cell

section
open Purelib
open Purelib.Algebra
open Purelib.Data.Rat
namespace Cell

/-- Sum the original indexed finite family of cell energy contributions. -/
def cellEnergy {cellCount : Nat} (cells : Fin cellCount ->
  Cell) : Fraction.Rational :=
  FiniteSum.Fin.sumFin fun index =>
    (cells index).contribution

end Cell

namespace Cell

/-- The total retained cell energy is nonnegative. -/
theorem cellEnergy_nonnegative {cellCount : Nat}
    (cells : Fin cellCount -> Cell) : 0 <= Integration.Energy.Cell.cellEnergy cells := by
  calc
    0 = FiniteSum.Fin.sumFin
          (fun _ : Fin cellCount => (0 : Fraction.Rational)) :=
      FiniteSum.Fin.sumFin_zero.symm
    _ <= Integration.Energy.Cell.cellEnergy cells :=
      FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
        (fun index => (cells index).contribution_nonnegative)

end Cell

end

namespace Cell

open Purelib in
open Purelib.Algebra in
/-- One specified cell with positive area and density makes the entire retained finite-family energy positive. -/
theorem cellEnergy_positive_of_cell {cellCount : Nat}
    (cells : Fin cellCount -> Cell) (positiveCell : Fin cellCount)
    (areaPositive : 0 < (cells positiveCell).areaLower)
    (densityPositive : 0 < (cells positiveCell).densityLower) :
    0 < Integration.Energy.Cell.cellEnergy cells := by
  have selectedPositive : 0 < (cells positiveCell).contribution :=
    contribution_positive _ areaPositive densityPositive
  have selected_le_energy :
      (cells positiveCell).contribution <= Integration.Energy.Cell.cellEnergy cells := by
    calc
      (cells positiveCell).contribution =
          FiniteSum.Fin.sumFin (fun index =>
            if index = positiveCell then (cells index).contribution else 0) :=
        (FiniteSum.Fin.sumFin_ite_eq positiveCell
          (fun index => (cells index).contribution)).symm
      _ <= Integration.Energy.Cell.cellEnergy cells :=
        FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun index => by
          by_cases equal : index = positiveCell
          · rw [if_pos equal]
          · rw [if_neg equal]
            exact (cells index).contribution_nonnegative)
  exact selectedPositive.trans_le selected_le_energy

end Cell

end Purelib.Integration.Energy

end
