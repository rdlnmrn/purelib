module
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-! A coherent imaginary unit whose first enclosure delays strict sign discovery. -/

@[expose] public section

namespace Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit

open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian (Process)

/-- The exact Gaussian point with zero real coordinate and unit imaginary coordinate. -/
def value : Canonical := point 0 1

/-- A two-state process whose first enclosure is inconclusive and whose refinement exposes the exact imaginary unit.

Both states retain the same possible value and witness; refinement changes only the certified enclosure. -/
def process : Process where
  State := Bool
  ball state := if state then
    { center := DelayedUnit.value, radiusSq := 0, radiusSq_nonneg := le_rfl }
    else { center := 0, radiusSq := 4, radiusSq_nonneg := by decide }
  Possible _ value := value = DelayedUnit.value
  witness _ := ⟨value, rfl⟩
  possible_inside := by
    intro state value equal
    subst value
    cases state <;> decide
  refine _ _ _ := true
  refine_persists := by
    intro state target positive value possible
    exact possible
  accurate := by
    intro state target positive
    exact positive
  centerBound := 1
  centerBound_nonneg := by decide
  center_bounded := by
    intro state
    cases state <;> decide

/-- The initial squared allowance is four and the refined exact allowance is zero. -/
def allowance (state : Bool) : Fraction.Rational := if state then 0 else 4

/-- The coherence certificate retaining the same imaginary-unit value across both delayed process states. -/
def coherent : Process.Coherence.Basic.Coherent process where
  allowance := DelayedUnit.allowance
  allowance_nonneg := by intro state; cases state <;> decide
  ball_radius_le := by intro state; cases state <;> decide
  possible_close := by
    intro left right leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    cases left <;> cases right <;> decide
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

/-- The coherent delayed imaginary-unit name at its original unresolved state. -/
def name : Name.Coherent.CoherentNamed where
  name := { process := DelayedUnit.process, state := false }
  coherent := DelayedUnit.coherent

end Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit
