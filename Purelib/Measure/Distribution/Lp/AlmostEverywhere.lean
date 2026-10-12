module
import Purelib.Measure.Content.Lp.AlmostEverywhere
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
public import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

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

namespace Distribution

/-- Require the two observables to agree at every original distribution occurrence unless its weight is zero. -/
@[expose]
def EqualAlmostEverywhere {α β : Type} (distribution : Distribution α)
    (left right : α → β) : Prop :=
  EqualOffZeroWeightOn distribution.atoms left right

/-- Expected separation vanishes exactly when the observables agree at every nonzero-weight occurrence. -/
theorem l1Distance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.l1Distance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toContent.l1Distance_eq_zero_iff left right

end Distribution

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

namespace Distribution

/-- Equality at nonzero-weight occurrences preserves every natural-powered magnitude expectation. -/
theorem poweredLp_congr_almostEverywhere {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational)
    (equal : distribution.EqualAlmostEverywhere left right) :
    distribution.poweredLp exponent left =
      distribution.poweredLp exponent right :=
  distribution.toContent.poweredLp_congr_almostEverywhere
    exponent left right equal

/-- Replacing either observable by one equal at nonzero-weight occurrences preserves every powered distance. -/
theorem poweredLpDistance_congr_almostEverywhere {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational)
    (leftEqual : distribution.EqualAlmostEverywhere leftFirst leftSecond)
    (rightEqual : distribution.EqualAlmostEverywhere rightFirst rightSecond) :
    distribution.poweredLpDistance exponent leftFirst rightFirst =
      distribution.poweredLpDistance exponent leftSecond rightSecond :=
  distribution.toContent.poweredLpDistance_congr_almostEverywhere
    exponent leftFirst leftSecond rightFirst rightSecond leftEqual rightEqual

/-- Positive natural-powered distance vanishes exactly when the observables agree at all nonzero-weight occurrences. -/
theorem poweredLpDistance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance (exponent + 1) left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toContent.poweredLpDistance_eq_zero_iff
    exponent left right

/-- Positive natural-powered magnitude expectation vanishes exactly when the observable is zero at all nonzero-weight
occurrences. -/
theorem poweredLp_eq_zero_iff {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    distribution.poweredLp (exponent + 1) value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toContent.poweredLp_eq_zero_iff exponent value

/-- Expected magnitude vanishes exactly when the observable is zero at every nonzero-weight occurrence. -/
theorem poweredL1_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL1 value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toContent.poweredL1_eq_zero_iff value

/-- Expected square vanishes exactly when the observable is zero at every nonzero-weight occurrence. -/
theorem poweredL2_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.poweredL2 value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toContent.poweredL2_eq_zero_iff value

/-- Expected squared distance vanishes exactly when the observables agree at every nonzero-weight occurrence. -/
theorem poweredL2Distance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL2Distance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toContent.poweredL2Distance_eq_zero_iff left right

end Distribution

end Purelib.Measure

end
