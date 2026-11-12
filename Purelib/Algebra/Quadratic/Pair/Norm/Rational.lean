module

public import Purelib.Algebra.Quadratic.Pair.Norm
public import Purelib.Data.Rat.Fraction.Square.Check
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Rational quadratic norms from finite square inspection

The original pair parameter is minus the rational generator square. The
canonical-coordinate checker supplies nonsquareness at that same parameter,
so every nonzero original pair has nonzero norm and valid inverse coordinates.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair

open Purelib.Data.Rat.Fraction

/-- Nonsquareness of the rational generator square makes every nonzero pair norm nonzero. -/
theorem norm_ne_zero_of_nonsquare (parameter : Rational)
    (nonsquare : ∀ candidate : Rational, candidate * candidate ≠ parameter)
    {value : Pair Rational (-parameter)} (nonzero : value ≠ 0) : value.norm ≠ 0 := by
  apply norm_ne_zero ?_ nonzero
  intro candidate same
  exact nonsquare candidate (same.trans (by ring1))

/-- A complete retained rational-square exclusion gives nonzero norm for every nonzero original pair. -/
theorem norm_ne_zero_of_inspection {parameter : Rational} (inspection : Square.Inspection parameter)
    (missing : inspection.root? = none) {value : Pair Rational (-parameter)} (nonzero : value ≠ 0) :
    value.norm ≠ 0 :=
  norm_ne_zero_of_nonsquare parameter (inspection.not_square_of_missing missing) nonzero

/-- The finite square inspection certifies the explicit right inverse of every nonzero original rational pair. -/
theorem mul_inverse_of_inspection {parameter : Rational} (inspection : Square.Inspection parameter)
    (missing : inspection.root? = none) (value : Pair Rational (-parameter)) (nonzero : value ≠ 0) :
    value * value.inverse = 1 :=
  value.mul_inverse (norm_ne_zero_of_inspection inspection missing nonzero)

/-- The same retained inspection certifies the explicit left inverse of the original pair. -/
theorem inverse_mul_of_inspection {parameter : Rational} (inspection : Square.Inspection parameter)
    (missing : inspection.root? = none) (value : Pair Rational (-parameter)) (nonzero : value ≠ 0) :
    value.inverse * value = 1 :=
  value.inverse_mul (norm_ne_zero_of_inspection inspection missing nonzero)

end Purelib.Algebra.Quadratic.Pair

end
