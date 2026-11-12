module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Fin.Two
import Purelib.Tactic.Ring

/-! # The actual site-centred labelled Legendre parameter meridian

The parameter is criticalValue plus the original labelled displacement
multiplied by the SAME rational unit phase. This treats both original
collision sites without replacing the critical-one meridian by rotation
about zero. The half-gap scales once and the original smoothing scales by
the phase squared. Original radius bounds and both singular exclusions
are derived pointwise; no frame or root continuation is inferred from them.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)

/-- A retained original certified unit phase is nonzero by its exact original norm certificate. -/
private theorem phase_ne_zero (phase : UnitVertex) : phase.value ≠ 0 := by
  intro zero
  have unit := phase.unit
  rewrite [zero, Norm.Basic.normSq_zero] at unit
  exact (by decide +kernel : (0 : Fraction.Rational) ≠ 1) unit

/-- The actual labelled meridian rotates the same original parameter displacement around its selected critical value. -/
def parameterAt (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) : Canonical :=
  criticalValue site + (Twist.phase time).value * (parameter - criticalValue site)

/-- The actual meridian displacement is the original labelled displacement multiplied by its retained unit phase. -/
theorem displacement (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    parameterAt site parameter time - criticalValue site =
      (Twist.phase time).value * (parameter - criticalValue site) := by unfold parameterAt; ring1

/-- The actual original parameter starts unchanged at the initial phase. -/
theorem parameter_zero (site : Fin 2) (parameter : Canonical) : parameterAt site parameter 0 = parameter := by
  unfold parameterAt
  rewrite [Twist.phase_zero_value]
  ring1

/-- After all four original rational phase quarters, the SAME original labelled parameter returns exactly. -/
theorem parameter_one (site : Fin 2) (parameter : Canonical) : parameterAt site parameter 1 = parameter := by
  unfold parameterAt
  rewrite [Twist.phase_one_value]
  ring1

/-- The original exact labelled half-gap scales once by that SAME actual parameter phase. -/
theorem halfGap_at (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    halfGap site (parameterAt site parameter time) = (Twist.phase time).value * halfGap site parameter := by
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  calc
    _ = parameterAt site parameter time - criticalValue site :=
      Polynomial.Quadratic.Split.halfGap_mul_two _ _ (by decide +kernel)
    _ = (Twist.phase time).value * (parameter - criticalValue site) := displacement site parameter time
    _ = (Twist.phase time).value * (halfGap site parameter * 2) :=
      congrArg (fun value : Canonical => (Twist.phase time).value * value)
        (Polynomial.Quadratic.Split.halfGap_mul_two (criticalValue site) parameter (by decide +kernel)).symm
    _ = _ := by ring1

/-- The original labelled smoothing has the phase-squared base change, derived from its actual half-gap definition. -/
theorem smoothing_at (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    smoothing site (parameterAt site parameter time) = (Twist.phase time).value ^ 2 * smoothing site parameter := by
  unfold smoothing
  rewrite [halfGap_at]
  ring1

/-- The square of the SAME certified unit phase has exact unit norm. -/
theorem phase_square_norm (phase : UnitVertex) : Norm.Basic.normSq (phase.value ^ 2) = 1 := by
  rewrite [pow_two]
  exact (Norm.Basic.normSq_mul _ _).trans
    ((congrArg₂ (fun first last : Fraction.Rational => first * last) phase.unit phase.unit).trans
      (by decide +kernel))

/-- The actual meridian retains the original exact squared parameter displacement at every rational time. -/
theorem displacement_normSq (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    Norm.Basic.normSq (parameterAt site parameter time - criticalValue site) =
      Norm.Basic.normSq (parameter - criticalValue site) := by
  rewrite [displacement, Norm.Basic.normSq_mul, (Twist.phase time).unit]
  exact Fraction.Field.one_mul _

/-- The original admitted parameter-distance bound remains paid at every actual meridian time. -/
theorem bound_at {site : Fin 2} {parameter : Canonical}
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) :
    Norm.Basic.normSq (parameterAt site parameter time - criticalValue site) ≤ 1 / 64 :=
  (displacement_normSq site parameter time).trans_le bound

/-- Nonzero original labelled displacement remains nonzero at every actual meridian parameter. -/
theorem regular_at {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site)
    (time : Fraction.Rational) : parameterAt site parameter time ≠ criticalValue site := by
  have nonzero : parameter - criticalValue site ≠ 0 := by
    intro zero
    apply regular
    calc
      parameter = (parameter - criticalValue site) + criticalValue site := by ring1
      _ = criticalValue site := by rewrite [zero]; ring1
  have product := Field.mul_ne_zero_direct (phase_ne_zero (Twist.phase time)) nonzero
  intro same
  apply product
  calc
    _ = parameterAt site parameter time - criticalValue site := (displacement site parameter time).symm
    _ = 0 := by rewrite [same]; ring1

/-- The same original small bound places every meridian parameter in its retained critical-value patch. -/
theorem parameter_inside {site : Fin 2} {parameter : Canonical}
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) : (parameterBox site).Contains (parameterAt site parameter time) :=
  Waist.parameter_inside site (parameterAt site parameter time)
    ((bound_at bound time).trans (by decide +kernel))

/-- Both actual singular values are excluded throughout the SAME labelled meridian, with no frame equality premise. -/
theorem parameter_regular {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (time : Fraction.Rational) : parameterAt site parameter time ≠ 0 ∧ parameterAt site parameter time ≠ 1 := by
  have selected := regular_at regular time
  have other := Degeneration.parameter_ne_remaining site
    (parameter := parameterAt site parameter time) (parameter_inside bound time)
  rcases Data.Fin.Two.finTwo_cases site with zero | one
  · subst site
    exact ⟨selected, other⟩
  · subst site
    exact ⟨other, selected⟩

/-- The smoothing's actual norm remains unchanged, although its exact value follows the squared phase. -/
theorem smoothing_normSq (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    Norm.Basic.normSq (smoothing site (parameterAt site parameter time)) =
      Norm.Basic.normSq (smoothing site parameter) := by
  rewrite [smoothing_at, Norm.Basic.normSq_mul, phase_square_norm (Twist.phase time)]
  exact Fraction.Field.one_mul _

/-- The actual source and target conic fibres retain exactly the SAME computed inner radial bound. -/
theorem innerRadiusSq_at (site : Fin 2) (parameter : Canonical) (time : Fraction.Rational) :
    innerRadiusSq site (parameterAt site parameter time) = innerRadiusSq site parameter := by
  unfold innerRadiusSq
  rewrite [smoothing_normSq]
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

end
