module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.Int
import Purelib.Data.Vector.Basic
public import Purelib.Topology.Surface.CellularHomology
import Purelib.Tactic.Ring

/-!
# Genus-one coefficient readbacks

The original homology representative has two structural integer entries,
one for each displayed handle cycle. Its intersection and standard cycles
are read directly from those retained coordinates.
-/

public section

namespace Purelib.Topology.Surface.CellularHomology.GenusOne.Basic
open Purelib
open Purelib.Algebra
open Purelib.Topology.Surface
open scoped Purelib.Data.Nat

/-- Integral first homology of the standard genus-one cell model.

Its two retained coordinates are the coefficients of the displayed a- and b-cycles. -/
abbrev Homology := CellularHomology.FirstHomology 1

/-! ## Symplectic and Picard--Lefschetz formulas -/

/-- Genus-one intersection is the determinant of the two coefficient pairs.

The original genus-one handle sum has exactly one displayed summand. Its empty remainder contributes zero, leaving the
two retained coefficient cross-products. -/
theorem intersection_genus_one (left right : Homology) :
    CellularHomology.intersection left right =
      CellularHomology.aCoefficient left 0 *
          CellularHomology.bCoefficient right 0 -
        CellularHomology.bCoefficient left 0 *
          CellularHomology.aCoefficient right 0 := by
  unfold CellularHomology.intersection
  rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_empty]
  ring1

/-- The a-coefficient of a constructed genus-one vector is its zeroth entry. -/
@[simp] theorem aCoefficient_vectorOfFn (entries : Fin 2 -> Int) :
    CellularHomology.aCoefficient (genus := 1)
        (Data.Vector.Basic.vectorOfFn entries) 0 =
      entries 0 := by
  unfold CellularHomology.aCoefficient
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- The b-coefficient of a constructed genus-one vector is its first entry. -/
@[simp] theorem bCoefficient_vectorOfFn (entries : Fin 2 -> Int) :
    CellularHomology.bCoefficient (genus := 1)
        (Data.Vector.Basic.vectorOfFn entries) 0 =
      entries 1 := by
  unfold CellularHomology.bCoefficient
  rw [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Read the a-coefficient as coordinate zero of the retained vector. -/
@[simp] theorem aCoefficient_eq_zero (cycle : Homology) :
    CellularHomology.aCoefficient cycle 0 = cycle 0 := rfl

/-- Read the b-coefficient as coordinate one of the retained vector. -/
@[simp] theorem bCoefficient_eq_one (cycle : Homology) :
    CellularHomology.bCoefficient cycle 0 = cycle 1 := rfl

/-- The genus-one a-cycle is the explicit vector with coordinates one and zero.

The original vector constructor materializes the retained a-block followed by its b-block. At genus one these closed
entries are one and zero in their original order. -/
theorem aCycle_coordinates :
    CellularHomology.aCycle (0 : Fin 1) =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 => if coordinate = 0 then 1 else 0 := by
  rfl

/-- The genus-one b-cycle is the explicit vector with coordinates zero and one.

The original vector constructor materializes the retained a-block followed by its b-block. At genus one these closed
entries are zero and one in their original order. -/
theorem bCycle_coordinates :
    CellularHomology.bCycle (0 : Fin 1) =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 => if coordinate = 0 then 0 else 1 := by
  rfl

end Purelib.Topology.Surface.CellularHomology.GenusOne.Basic
