module
public import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.Bound.Operational
public import Purelib.Approximation.Rational.Uniform.Modulus
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Uniform variation for finite numerical point processes

Each rational point has its own original rational enclosure process. The
variation law relates their actual finite states through overlap bounds; it
does not select an exact rational value or a completed real value.
-/

public section

namespace Purelib.Approximation.Rational.Uniform

open Purelib.Data.Rat

set_option genInjectivity false in
/-- Effective uniform variation between finite rational point-enclosure processes.

For nearby ordered points, each displayed point interval overlaps the other
after the requested variation is added. The law quantifies over the original
process states, so it covers independent requests without choosing a common
completed value or supplying an integration result. -/
structure Numerical (source : Fraction.Rational → BoundProcess) where
  /-- Compute the positive distance for the retained variation request. -/ radius :
    Fraction.Rational → Fraction.Rational
  /-- Positive variation requests produce positive rational distances. -/ radius_pos :
    ∀ variation, 0 < variation → 0 < radius variation
  /-- Every pair of finite point intervals obeys the original variation overlap bounds. -/ variation :
    ∀ variation, 0 < variation → ∀ first second, 0 ≤ first → first ≤ second → second ≤ 1 →
      second - first < radius variation → ∀ firstState : (source first).State,
      ∀ secondState : (source second).State,
        ((source first).bound firstState).lower - variation ≤ ((source second).bound secondState).upper ∧
        ((source second).bound secondState).lower ≤ ((source first).bound firstState).upper + variation

constructive_injectivity Numerical

/-- One directed point-state overlap follows from arbitrarily small finite variation requests. -/
private theorem state_lower_le_upper {source : Fraction.Rational → BoundProcess} (modulus : Numerical source)
    (point : Fraction.Rational) (lower : 0 ≤ point) (upper : point ≤ 1)
    (first second : (source point).State) :
    ((source point).bound first).lower ≤ ((source point).bound second).upper := by
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro separated
  let gap := ((source point).bound first).lower - ((source point).bound second).upper
  have gapPositive : 0 < gap := Fraction.Order.Arithmetic.sub_pos_direct separated
  have halfPositive : 0 < gap / 2 := Fraction.Order.Field.div_pos_direct gapPositive (by decide)
  have small : point - point < modulus.radius (gap / 2) := by
    have identity : point - point = 0 := by ring1
    rw [identity]
    exact modulus.radius_pos (gap / 2) halfPositive
  have observed := modulus.variation (gap / 2) halfPositive point point lower le_rfl upper small first second
  have translated := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp observed.1
  have gapBound := Fraction.Order.Arithmetic.sub_le_sub_right_direct translated ((source point).bound second).upper
  have identity : (((source point).bound second).upper + gap / 2) - ((source point).bound second).upper =
      gap / 2 := by ring1
  rw [identity] at gapBound
  exact (not_lt_of_ge gapBound) (Fraction.Order.Field.half_lt_self gapPositive)

/-- Every rational unit point's original numerical process has coherent finite states.

For any two independently chosen states, the variation law at that same
point rules out a positive separating gap. The proof uses one finite positive
variation request for each endpoint comparison and selects no common value. -/
theorem Numerical.coherent {source : Fraction.Rational → BoundProcess} (modulus : Numerical source)
    (point : Fraction.Rational) (lower : 0 ≤ point) (upper : point ≤ 1) : (source point).Coherent := by
  intro first second
  exact ⟨state_lower_le_upper modulus point lower upper first second,
    state_lower_le_upper modulus point lower upper second first⟩

/-- An exact rational source modulus induces numerical point processes with exact readings.

Each point uses the original exact rational bound process, and its overlap
law is the original source's effective variation law. -/
@[expose] def Numerical.ofExact {source : Fraction.Rational → Fraction.Rational} (modulus : Modulus source) :
    Numerical (fun point => BoundProcess.exact (source point)) where
  radius := modulus.radius
  radius_pos := modulus.radius_pos
  variation := by
    intro variation positive first second lower ordered upper small firstState secondState
    cases firstState
    cases secondState
    exact modulus.variation variation positive first second lower ordered upper small

end Purelib.Approximation.Rational.Uniform

end
