module
import Purelib.Data.Fin.Two
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.Topology.Surface.CellularHomology.GenusOne.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data.Fin

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

open Purelib.Topology.Surface.CellularHomology

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.Topology.Surface.CellularHomology.GenusOne.Action

/-- Act on integral genus-one homology by an integral two-by-two matrix.

Coordinates are column vectors, so matrix multiplication composes actions in the displayed order. -/
def actMatrix (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) (cycle : GenusOne.Basic.Homology) : GenusOne.Basic.Homology :=
  Multiplication.matrixVector matrix cycle

open Purelib.Topology.Surface.CellularHomology.GenusOne
/-- Read the two scalar coordinates of a displayed two-by-two matrix action. -/
theorem act_matrix₂ (a b c d : Int) (cycle :
  GenusOne.Basic.Homology) :
    actMatrix (Two.matrix₂ a b c d) cycle =
      Data.Vector.Basic.vectorOfFn fun coordinate : Fin 2 =>
        if coordinate = 0 then a * cycle 0 + b * cycle 1
        else c * cycle 0 + d * cycle 1 := by
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rcases Two.finTwo_cases coordinate with coordinateZero | coordinateOne
  · subst coordinate
    rw [actMatrix, Multiplication.matrixVector_apply, FiniteSum.Fin.sumFin_two_int,
      Data.Vector.Basic.vectorOfFn_apply]
    rfl
  · subst coordinate
    rw [actMatrix, Multiplication.matrixVector_apply, FiniteSum.Fin.sumFin_two_int,
      Data.Vector.Basic.vectorOfFn_apply]
    rfl

/-- Matrix multiplication agrees with successive genus-one homology actions. -/
@[simp] theorem actMatrix_mul (left right :
  LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (cycle : GenusOne.Basic.Homology) :
    actMatrix (Multiplication.mul left right) cycle =
      actMatrix left (actMatrix right cycle) :=
  Multiplication.matrixVector_mul left right cycle

/-- The identity matrix fixes every genus-one homology vector. -/
@[simp] theorem actMatrix_identity (cycle :
  GenusOne.Basic.Homology) :
    actMatrix Multiplication.identity cycle = cycle := by
  change Multiplication.matrixVector (Multiplication.scaleIdentity (1 : Int)) cycle = cycle
  rw [Multiplication.matrixVector_scaleIdentity]
  apply Data.Vector.Basic.vector_ext
  intro coordinate
  rw [Data.Vector.Basic.vectorOfFn_apply]
  ring1
end Purelib.Topology.Surface.CellularHomology.GenusOne.Action

end
