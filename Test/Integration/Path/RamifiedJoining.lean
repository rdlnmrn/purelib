module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

public import Purelib.Integration.Path.IncrementArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Integration.Path

@[expose] public section

/-! Exact coordinate regression for the odd reciprocal chart w = t².
The identity primitive evaluated at t and at w gives different closed polygon
areas. This refutes a coordinate-only identification, not the period theorem. -/
namespace Test.Integration.Path.RamifiedJoining
open Purelib.Integration.Path.IncrementArea (Gaussian Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)

/-- The exact root-plane point at one quarter on the real axis. -/
def firstRoot : Gaussian := ⟨1 / 4, 0⟩
/-- The exact root-plane point at one quarter on the imaginary axis. -/
def secondRoot : Gaussian := ⟨0, 1 / 4⟩
/-- The exact root-plane point with both coordinates one quarter. -/
def thirdRoot : Gaussian := ⟨1 / 4, 1 / 4⟩

/-- The ordered three-edge closed polygon joining the retained root-plane points. -/
def rootIncrements : List Gaussian :=
  [secondRoot - firstRoot, thirdRoot - secondRoot,
    firstRoot - thirdRoot]

/-- The ordered closed polygon joining the squares of the same retained root-plane points. -/
def reciprocalIncrements : List Gaussian :=
  [secondRoot^2 - firstRoot^2, thirdRoot^2 -
    secondRoot^2, firstRoot^2 - thirdRoot^2]

/-- The first exact root-plane point squares to real one sixteenth. -/
theorem first_square : firstRoot^2 = (⟨1 / 16, 0⟩ : IncrementArea.Gaussian) := by decide +kernel
/-- The second exact root-plane point squares to real negative one sixteenth. -/
theorem second_square : secondRoot^2 = (⟨-1 / 16, 0⟩ : IncrementArea.Gaussian) := by decide +kernel
/-- The third exact root-plane point squares to imaginary one eighth. -/
theorem third_square : thirdRoot^2 = (⟨0, 1 / 8⟩ : IncrementArea.Gaussian) := by decide +kernel

/-- The original three root-plane increments sum exactly to zero. -/
theorem roots_closed :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum rootIncrements = 0 := by
  decide +kernel
/-- The three squared-coordinate increments sum exactly to zero. -/
theorem reciprocals_closed : Data.Gaussian.Norm.Sum.Basic.gaussianSum reciprocalIncrements = 0 :=
  by decide +kernel

/-- The root-plane triangle has exact signed Gaussian area negative imaginary one eighth. -/
theorem root_area : IncrementArea.pathArea rootIncrements = (⟨0, -1 / 8⟩ : IncrementArea.Gaussian) := by
  decide +kernel
/-- The squared-coordinate triangle has exact signed Gaussian area negative imaginary one thirty-second. -/
theorem reciprocal_area : IncrementArea.pathArea reciprocalIncrements = (⟨0, -1 / 32⟩ :
  IncrementArea.Gaussian) := by decide +kernel

/-- The closed root-plane and squared-coordinate polygons have distinct exact signed areas. -/
theorem areas_differ : IncrementArea.pathArea rootIncrements ≠ IncrementArea.pathArea
  reciprocalIncrements := by decide +kernel

/-- The exact signed area discrepancy is negative imaginary three thirty-seconds. -/
theorem area_difference : IncrementArea.pathArea rootIncrements - IncrementArea.pathArea
  reciprocalIncrements =
    (⟨0, -3 / 32⟩ : IncrementArea.Gaussian) := by decide +kernel

/-- The two closed polygons have an exact, nonzero discrepancy. Closure of both totals supplies no reason for the root
and squared-coordinate areas to agree. -/
theorem discrepancy_positive :
    (0 : IncrementArea.Coordinate) <
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea rootIncrements -
        IncrementArea.pathArea reciprocalIncrements) := by
  decide +kernel

end Test.Integration.Path.RamifiedJoining
