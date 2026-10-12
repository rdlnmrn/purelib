module
public import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Reflection.Line
public import Purelib.Geometry.Stars.Regular.OrderThree.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Stars.Regular

section
@[expose] public section

/-!
# Divine Proportions, Theorem 95: regular stars of order three

The three-line star is finite data.  Its cyclic rule stores the three
reflection-lineation equations explicitly, and mutual nonparallelism replaces
any appeal to a global collection of lines.
-/

namespace Purelib.Geometry.Stars.Regular.OrderThree.Construction

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The second explicit line `⟨r:1:0⟩`. -/
def orderThreeLine₁ [Nontrivial K] (root : K) :
  Plane.Line K where
  a := root
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- The third explicit line `⟨-r:1:0⟩`. -/
def orderThreeLine₂ [Nontrivial K] (root : K) :
  Plane.Line K where
  a := -root
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- The source's three displayed lines form a regular star whenever `3 = r²` with `r ≠ 0`. -/
def orderThreeStar [Nontrivial K] [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0) (threeSquare : (3 : K) = root ^ 2)
    (twoNonzero : (2 : K) ≠ 0) : OrderThree.Basic.RegularThreeStar K where
  line₀ := Purelib.Geometry.Plane.Line.Basic.xAxis
  line₁ := orderThreeLine₁ root
  line₂ := orderThreeLine₂ root
  line₀NonNull := by
    intro nullNorm
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  line₁NonNull := by
    intro nullNorm
    apply Characteristic.Nonzero.four_ne_zero twoNonzero
    calc
      (4 : K) = root ^ 2 + 1 ^ 2 := by rw [← threeSquare]; ring1
      _ = 0 := nullNorm
  line₂NonNull := by
    intro nullNorm
    apply Characteristic.Nonzero.four_ne_zero twoNonzero
    calc
      (4 : K) = root ^ 2 + 1 ^ 2 := by rw [← threeSquare]; ring1
      _ = (-root) ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  line₀Line₁Nonparallel := by
    intro parallel
    apply rootNonzero
    unfold Purelib.Geometry.Plane.Line.Parallel Purelib.Geometry.Plane.Line.Basic.xAxis
      orderThreeLine₁ at parallel
    calc
      root = -(0 * 1 - root * 1) := by ring1
      _ = 0 := by rw [parallel]; ring1
  line₁Line₂Nonparallel := by
    intro parallel
    have productNonzero := Algebra.Field.ExplicitField.mul_ne_zero twoNonzero rootNonzero
    apply productNonzero
    unfold Purelib.Geometry.Plane.Line.Parallel
      orderThreeLine₁
      orderThreeLine₂ at parallel
    calc
      (2 : K) * root = root * 1 - (-root) * 1 := by ring1
      _ = 0 := parallel
  line₂Line₀Nonparallel := by
    intro parallel
    apply rootNonzero
    unfold Purelib.Geometry.Plane.Line.Parallel
      orderThreeLine₂
      Purelib.Geometry.Plane.Line.Basic.xAxis at parallel
    calc
      root = -((-root) * 1 - 0 * 1) := by ring1
      _ = 0 := by rw [parallel]; ring1
  reflectAround₀ := by
    unfold Purelib.Geometry.Plane.Line.Equivalent
    simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
      Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
        orderThreeLine₁,
        orderThreeLine₂]
    constructor
    · ring1
    constructor <;> ring1
  reflectAround₁ := by
    unfold Purelib.Geometry.Plane.Line.Equivalent
    simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
      Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
        orderThreeLine₁,
        orderThreeLine₂]
    constructor
    · rw [← threeSquare]
      ring1
    constructor <;> ring1
  reflectAround₂ := by
    unfold Purelib.Geometry.Plane.Line.Equivalent
    simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
      Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
        orderThreeLine₁,
        orderThreeLine₂]
    constructor
    · rw [show (-root) ^ 2 = (3 : K) by
        calc
          (-root) ^ 2 = root ^ 2 := by ring1
          _ = 3 := threeSquare.symm]
      ring1
    constructor <;> ring1
end Purelib.Geometry.Stars.Regular.OrderThree.Construction

end
