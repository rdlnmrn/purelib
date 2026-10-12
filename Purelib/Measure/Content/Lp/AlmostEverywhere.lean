module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Lp.L2
public import Purelib.Measure.Content.Lp.Natural
public import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Lp.AlmostEverywhere
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
public section

/-!
# Finite almost-everywhere calculus

Equality almost everywhere means equality at every displayed atom whose
rational weight is nonzero.  The relation is executable on finite atom
tables and supports arithmetic, integration, and an exact L1
characterization without quotienting a function space.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace Content

/-- Require observable equality at each exact content occurrence unless that occurrence has zero weight.

The finite predicate is stated on the retained atom list and works for arbitrary observable codomains. -/
@[expose]
def EqualAlmostEverywhere {α β : Type} (content : Content α)
    (left right : α → β) : Prop :=
  EqualOffZeroWeightOn content.atoms left right

/-- Observables equal at all nonzero-weight occurrences have equal integrals over the same content. -/
theorem integral_congr_almostEverywhere {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (equal : content.EqualAlmostEverywhere left right) :
    content.integral left = content.integral right :=
  expectationWeight_congr_off_zero content.atoms left right equal

/-- Equality at nonzero-weight occurrences makes integrated separation vanish. -/
theorem l1Distance_eq_zero_of_equalAlmostEverywhere {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (equal : content.EqualAlmostEverywhere left right) :
    content.l1Distance left right = 0 := by
  have separationEqual : EqualOffZeroWeightOn content.atoms
      (fun item => Distance.rationalSeparation (left item) (right item))
      (fun _ => (0 : Fraction.Rational)) := by
    intro atom member
    rcases equal atom member with zero | same
    · exact Or.inl zero
    · apply Or.inr
      change Distance.rationalSeparation (left atom.item) (right atom.item) = 0
      rw [same]
      exact (Distance.rationalSeparation_eq_zero_iff _ _).mpr rfl
  calc
    content.l1Distance left right = content.integral (fun _ => 0) := by
      unfold l1Distance Content.integral
      exact expectationWeight_congr_off_zero content.atoms _ _
        separationEqual
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- A zero integrated separation forces equality at every nonzero-weight occurrence. -/
theorem equalAlmostEverywhere_of_l1Distance_eq_zero {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (zero : content.l1Distance left right = 0) :
    content.EqualAlmostEverywhere left right := by
  apply equalOffZeroWeight_of_poweredDistance_eq_zero left right 0 content.atoms
  have same := expectationWeight_congr_off_zero content.atoms
    (fun item => Distance.rationalSeparation (left item) (right item) ^ (0 + 1))
    (fun item => Distance.rationalSeparation (left item) (right item))
    (by
      intro atom member
      exact Or.inr (pow_one _))
  exact same.trans zero

/-- Integrated separation vanishes exactly when the two observables agree at every nonzero-weight occurrence. -/
theorem l1Distance_eq_zero_iff {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.l1Distance left right = 0 ↔
      content.EqualAlmostEverywhere left right :=
  ⟨content.equalAlmostEverywhere_of_l1Distance_eq_zero left right,
    content.l1Distance_eq_zero_of_equalAlmostEverywhere left right⟩

end Content

end Purelib.Measure

end

section
public section

/-!
# Powered Lp quantities modulo finite almost-everywhere equality

Natural-powered finite magnitudes and distances depend only on displayed
nonzero-weight rows.  At every explicitly positive natural exponent they
vanish exactly when the relevant observables are equal in the finite
almost-everywhere sense.  The proof is a direct induction over the weighted
atom list and uses no quotient function space.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat
namespace Content

/-- Equality at nonzero-weight occurrences preserves every natural-powered magnitude integral. -/
theorem poweredLp_congr_almostEverywhere {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational)
    (equal : content.EqualAlmostEverywhere left right) :
    content.poweredLp exponent left = content.poweredLp exponent right := by
  unfold poweredLp
  apply content.integral_congr_almostEverywhere
  exact equal.comp fun value => Distance.rationalSeparation value 0 ^ exponent

/-- Replacing either observable by one equal at nonzero-weight occurrences preserves every powered distance. -/
theorem poweredLpDistance_congr_almostEverywhere {α : Type}
    (content : Content α) (exponent : Nat)
    (leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational)
    (leftEqual : content.EqualAlmostEverywhere leftFirst leftSecond)
    (rightEqual : content.EqualAlmostEverywhere rightFirst rightSecond) :
    content.poweredLpDistance exponent leftFirst rightFirst =
      content.poweredLpDistance exponent leftSecond rightSecond := by
  unfold poweredLpDistance
  apply content.integral_congr_almostEverywhere
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation (leftFirst atom.item) (rightFirst atom.item) ^
        exponent =
      Distance.rationalSeparation (leftSecond atom.item) (rightSecond atom.item) ^
        exponent
    rw [leftSame, rightSame]

/-- A positive natural-powered distance vanishes exactly when its observables agree at every nonzero-weight occurrence.
-/
theorem poweredLpDistance_eq_zero_iff {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    content.poweredLpDistance (exponent + 1) left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  constructor
  · intro zero
    exact Measure.equalOffZeroWeight_of_poweredDistance_eq_zero
      left right exponent content.atoms zero
  · intro equal
    unfold poweredLpDistance
    have integrandEqual : content.EqualAlmostEverywhere
        (fun item => Distance.rationalSeparation (left item) (right item) ^
          (exponent + 1))
        (fun _ => (0 : Fraction.Rational)) := by
      intro atom member
      rcases equal atom member with weightZero | same
      · exact Or.inl weightZero
      · apply Or.inr
        have separationZero :
            Distance.rationalSeparation (left atom.item) (right atom.item) = 0 :=
          (Distance.rationalSeparation_eq_zero_iff _ _).mpr same
        change Distance.rationalSeparation (left atom.item) (right atom.item) ^
            (exponent + 1) = 0
        rw [separationZero]
        exact zero_pow (Nat.zero_lt_succ exponent).ne'
    calc
      content.integral (fun item =>
            Distance.rationalSeparation (left item) (right item) ^ (exponent + 1)) =
          content.integral (fun _ => 0) :=
        content.integral_congr_almostEverywhere _ _ integrandEqual
      _ = content.total * 0 := content.integral_constant 0
      _ = 0 := mul_zero _

/-- A positive natural-powered magnitude integral vanishes exactly when the observable is zero at every nonzero-weight
occurrence. -/
theorem poweredLp_eq_zero_iff {α : Type}
    (content : Content α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    content.poweredLp (exponent + 1) value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have differenceIdentity := content.poweredLp_sub_eq_poweredLpDistance
    (exponent + 1) value (fun _ => 0)
  have identity : content.poweredLp (exponent + 1) value =
      content.poweredLpDistance (exponent + 1) value (fun _ => 0) := by
    calc
      content.poweredLp (exponent + 1) value =
          content.poweredLp (exponent + 1)
            (fun item => value item - 0) := by
        unfold poweredLp
        exact content.integral_congr _ _ (fun item => by
          have same : value item = value item - 0 := by ring1
          exact congrArg (fun scalar : Fraction.Rational =>
            Distance.rationalSeparation scalar 0 ^ (exponent + 1)) same)
      _ = content.poweredLpDistance (exponent + 1) value (fun _ => 0) :=
        differenceIdentity
  rw [identity]
  exact content.poweredLpDistance_eq_zero_iff exponent value (fun _ => 0)

/-- An integral of magnitude vanishes exactly when its observable is zero at every nonzero-weight occurrence. -/
theorem poweredL1_eq_zero_iff {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredL1 value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have characterization := content.poweredLp_eq_zero_iff 0 value
  simpa only [-eq_self, -iff_self, Nat.zero_add, content.poweredLp_one] using characterization

/-- A square integral vanishes exactly when its observable is zero at every nonzero-weight occurrence. -/
theorem poweredL2_eq_zero_iff {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredL2 value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have characterization := content.poweredLp_eq_zero_iff 1 value
  simpa only [-eq_self, -iff_self, content.poweredLp_two] using characterization

/-- Squared integrated distance vanishes exactly when the observables agree at every nonzero-weight occurrence. -/
theorem poweredL2Distance_eq_zero_iff {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.poweredL2Distance left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  have characterization := content.poweredLpDistance_eq_zero_iff
    1 left right
  simpa only [-eq_self, -iff_self, content.poweredLpDistance_two] using characterization

end Content

end Purelib.Measure

end
