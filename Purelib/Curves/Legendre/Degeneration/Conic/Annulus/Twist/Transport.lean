module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian
import Purelib.Curves.Legendre.Degeneration.Conic.Rotation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Explicit conic-fibre transport over the labelled parameter phase meridian

For the source radial parameter alpha, the first coordinate is multiplied
by P(time*alpha)^2. The second is multiplied by
P(time)^2*conj(P(time*alpha))^2. Original unit/product laws prove the actual
target conic equation and an executable inverse, without assuming that the
rational phase respects addition. At time one this is exactly two applications
of the original annular twist, after an explicit fibre-parameter transport.

This is a conic chart transport candidate. It supplies no retained cubic or
cofactor root comparison, fixed complement/collar gluing, canonical-cycle
attachment, differential integral agreement or parameter-monodromy realization.
On an admitted regular annulus this candidate fixes the small coordinate
on each boundary; the large coordinate follows the squared loop phase.
A matching complement fibre transport must retain those actual boundary
families and its own endpoint return and cycle contribution. Boundary return
alone supplies no complement-return or geometric-monodromy certificate.

Point coordinate equalities concern the exact algebraic Point record only.
They identify no Frame, sheet, root or Owner by coordinates or labels.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)

variable {site : Fin 2} {parameter : Canonical}

/-- The SAME actual unit phase and its conjugate cancel through the original Gaussian norm certificate. -/
private theorem unit_product (phase : UnitVertex) : phase.value * Basic.conj phase.value = 1 := by
  have product := Basic.Canonical.mul_conj phase.value
  rewrite [← Norm.Basic.normSq_eq_canonical, phase.unit] at product
  exact product

/-- The actual squared phase and squared conjugate cancel by finite commutative-ring arithmetic. -/
private theorem square_product (phase : UnitVertex) : phase.value ^ 2 * Basic.conj phase.value ^ 2 = 1 := by
  calc
    _ = (phase.value * Basic.conj phase.value) ^ 2 := by ring1
    _ = 1 := by rewrite [unit_product]; decide +kernel

/-- The squared conjugate of the SAME certified phase has exact unit norm. -/
private theorem conjugate_square_norm (phase : UnitVertex) :
    Norm.Basic.normSq (Basic.conj phase.value ^ 2) = 1 := by
  have unit := (Norm.Basic.normSq_conj phase.value).trans phase.unit
  rewrite [pow_two]
  exact (Norm.Basic.normSq_mul _ _).trans
    ((congrArg₂ (fun first last : Fraction.Rational => first * last) unit unit).trans
      (by decide +kernel))

/-- Transport one original conic Point to the actual site-centred parameter-meridian fibre.

Both original unit phase caches are bound once. The source radial coordinate
is computed in its SAME original annulus. Its phase is evaluated at the
ordinary product time*alpha; no additive or exponential phase law is assumed.
-/
def transport (time : Fraction.Rational) (point : Point site parameter) :
    Point site (parameterAt site parameter time) :=
  let loop := Twist.phase time
  let radial := Twist.phase (time * Twist.radialParameter site parameter point.plus)
  { plus := radial.value ^ 2 * point.plus
    minus := loop.value ^ 2 * Basic.conj radial.value ^ 2 * point.minus
    equation := by
      calc
        _ = loop.value ^ 2 * (radial.value ^ 2 * Basic.conj radial.value ^ 2) *
            (point.plus * point.minus) := by ring1
        _ = loop.value ^ 2 * smoothing site parameter := by rewrite [square_product, point.equation]; ring1
        _ = smoothing site (parameterAt site parameter time) := (smoothing_at site parameter time).symm }

/-- The actual first transported coordinate retains the SAME source coordinate and squared radial-time phase. -/
theorem transport_plus (time : Fraction.Rational) (point : Point site parameter) :
    (transport time point).plus =
      (Twist.phase (time * Twist.radialParameter site parameter point.plus)).value ^ 2 * point.plus := by
  unfold transport
  rfl

/-- The actual second coordinate retains both independent original phases, with their exact conjugate placement. -/
theorem transport_minus (time : Fraction.Rational) (point : Point site parameter) :
    (transport time point).minus = (Twist.phase time).value ^ 2 *
      Basic.conj (Twist.phase (time * Twist.radialParameter site parameter point.plus)).value ^ 2 * point.minus := by
  unfold transport
  rfl

/-- The actual fibre transport preserves the exact first-coordinate squared radius. -/
theorem transport_plus_normSq (time : Fraction.Rational) (point : Point site parameter) :
    Norm.Basic.normSq (transport time point).plus = Norm.Basic.normSq point.plus := by
  rewrite [transport_plus, Norm.Basic.normSq_mul, phase_square_norm]
  exact Fraction.Field.one_mul _

/-- Both actual phase factors have unit norm, so the original second-coordinate squared radius is also preserved. -/
theorem transport_minus_normSq (time : Fraction.Rational) (point : Point site parameter) :
    Norm.Basic.normSq (transport time point).minus = Norm.Basic.normSq point.minus := by
  rewrite [transport_minus, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    phase_square_norm, conjugate_square_norm, Fraction.Field.one_mul, Fraction.Field.one_mul]
  rfl

/-- Actual target annulus admission follows from the SAME input admission and original radius identities. -/
theorem transport_contains (time : Fraction.Rational) (point : Point site parameter)
    (inside : Contains site parameter point.plus) :
    Contains site (parameterAt site parameter time) (transport time point).plus := by
  unfold Contains
  rewrite [innerRadiusSq_at, transport_plus_normSq]
  exact inside

/-- Both actual fibre parameters and the transported first coordinate give the SAME original normalized radius. -/
theorem radialParameter_transport (time : Fraction.Rational) (point : Point site parameter) :
    Twist.radialParameter site (parameterAt site parameter time) (transport time point).plus =
      Twist.radialParameter site parameter point.plus := by
  unfold Twist.radialParameter
  rewrite [innerRadiusSq_at, transport_plus_normSq]
  rfl

/-- The actual normalized source radius and admitted time give an original unit-interval radial-phase argument. -/
theorem radialTime_inside (time : Fraction.Rational) (point : Point site parameter)
    (timeInside : 0 ≤ time ∧ time ≤ 1)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (inside : Contains site parameter point.plus) :
    0 ≤ time * Twist.radialParameter site parameter point.plus ∧
      time * Twist.radialParameter site parameter point.plus ≤ 1 := by
  have radial := Twist.radialParameter_inside bound inside
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radial.2 timeInside.1
  rewrite [Fraction.Field.mul_one_direct] at upper
  exact ⟨Fraction.Order.Arithmetic.mul_nonneg_direct timeInside.1 radial.1, upper.trans timeInside.2⟩

/-- Invert the explicit conic transport using the actual target squared radius and conjugate loop phase.

The original source parameter remains the output index. The target Point
and its own actual annulus supply alpha; exact radius identities later prove
that this is the SAME alpha as the forward source. No target-root or
monodromy comparison is a premise.
-/
def inverse (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) : Point site parameter :=
  let loop := Twist.phase time
  let radial := Twist.phase (time * Twist.radialParameter site (parameterAt site parameter time) point.plus)
  { plus := Basic.conj radial.value ^ 2 * point.plus
    minus := Basic.conj loop.value ^ 2 * radial.value ^ 2 * point.minus
    equation := by
      calc
        _ = Basic.conj loop.value ^ 2 * (radial.value ^ 2 * Basic.conj radial.value ^ 2) *
            (point.plus * point.minus) := by ring1
        _ = Basic.conj loop.value ^ 2 * smoothing site (parameterAt site parameter time) := by
          rewrite [square_product, point.equation]
          ring1
        _ = Basic.conj loop.value ^ 2 * (loop.value ^ 2 * smoothing site parameter) :=
          congrArg (fun value : Canonical => Basic.conj loop.value ^ 2 * value) (smoothing_at site parameter time)
        _ = (loop.value ^ 2 * Basic.conj loop.value ^ 2) * smoothing site parameter := by ring1
        _ = smoothing site parameter := by rewrite [square_product]; ring1 }

/-- Read the exact first-coordinate inverse formula on the GIVEN target-fibre Point. -/
theorem inverse_plus (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    (inverse time point).plus =
      Basic.conj (Twist.phase
        (time * Twist.radialParameter site (parameterAt site parameter time) point.plus)).value ^ 2 * point.plus := by
  unfold inverse
  rfl

/-- Read the SAME independent conjugate loop phase and radial phase in the second-coordinate inverse formula. -/
theorem inverse_minus (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    (inverse time point).minus = Basic.conj (Twist.phase time).value ^ 2 *
      (Twist.phase (time * Twist.radialParameter site (parameterAt site parameter time) point.plus)).value ^ 2 *
        point.minus := by unfold inverse; rfl

/-- The executable inverse preserves the actual target's first-coordinate squared radius. -/
theorem inverse_plus_normSq (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    Norm.Basic.normSq (inverse time point).plus = Norm.Basic.normSq point.plus := by
  rewrite [inverse_plus, Norm.Basic.normSq_mul, conjugate_square_norm]
  exact Fraction.Field.one_mul _

/-- The inverse preserves the actual target's independent second-coordinate squared radius. -/
theorem inverse_minus_normSq (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    Norm.Basic.normSq (inverse time point).minus = Norm.Basic.normSq point.minus := by
  rewrite [inverse_minus, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    conjugate_square_norm, phase_square_norm, Fraction.Field.one_mul, Fraction.Field.one_mul]
  rfl

/-- The inverse returns the SAME admitted target Point to the original source annulus. -/
theorem inverse_contains (time : Fraction.Rational) (point : Point site (parameterAt site parameter time))
    (inside : Contains site (parameterAt site parameter time) point.plus) :
    Contains site parameter (inverse time point).plus := by
  unfold Contains at inside ⊢
  rewrite [innerRadiusSq_at] at inside
  rewrite [inverse_plus_normSq]
  exact inside

/-- The actual inverse retains the SAME normalized radius from its target-fibre Point. -/
theorem radialParameter_inverse (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    Twist.radialParameter site parameter (inverse time point).plus =
      Twist.radialParameter site (parameterAt site parameter time) point.plus := by
  unfold Twist.radialParameter
  rewrite [innerRadiusSq_at, inverse_plus_normSq]
  rfl

/-- The actual inverse undoes the original conic transport on the whole source Point. -/
theorem inverse_transport (time : Fraction.Rational) (point : Point site parameter) :
    inverse time (transport time point) = point := by
  apply Point.coordinates_eq
  · rewrite [inverse_plus, radialParameter_transport, transport_plus]
    let radial := Twist.phase (time * Twist.radialParameter site parameter point.plus)
    change Basic.conj radial.value ^ 2 * (radial.value ^ 2 * point.plus) = point.plus
    calc
      _ = (radial.value ^ 2 * Basic.conj radial.value ^ 2) * point.plus := by ring1
      _ = point.plus := by rewrite [square_product]; ring1
  · rewrite [inverse_minus, radialParameter_transport, transport_minus]
    let loop := Twist.phase time
    let radial := Twist.phase (time * Twist.radialParameter site parameter point.plus)
    change Basic.conj loop.value ^ 2 * radial.value ^ 2 *
      (loop.value ^ 2 * Basic.conj radial.value ^ 2 * point.minus) = point.minus
    calc
      _ = (loop.value ^ 2 * Basic.conj loop.value ^ 2) *
          (radial.value ^ 2 * Basic.conj radial.value ^ 2) * point.minus := by ring1
      _ = point.minus := by rewrite [square_product loop, square_product radial]; ring1

/-- The original transport undoes the executable inverse on the SAME whole actual target-fibre Point. -/
theorem transport_inverse (time : Fraction.Rational) (point : Point site (parameterAt site parameter time)) :
    transport time (inverse time point) = point := by
  apply Point.coordinates_eq
  · rewrite [transport_plus, radialParameter_inverse, inverse_plus]
    let radial := Twist.phase (time * Twist.radialParameter site (parameterAt site parameter time) point.plus)
    change radial.value ^ 2 * (Basic.conj radial.value ^ 2 * point.plus) = point.plus
    calc
      _ = (radial.value ^ 2 * Basic.conj radial.value ^ 2) * point.plus := by ring1
      _ = point.plus := by rewrite [square_product]; ring1
  · rewrite [transport_minus, radialParameter_inverse, inverse_minus]
    let loop := Twist.phase time
    let radial := Twist.phase (time * Twist.radialParameter site (parameterAt site parameter time) point.plus)
    change loop.value ^ 2 * Basic.conj radial.value ^ 2 *
      (Basic.conj loop.value ^ 2 * radial.value ^ 2 * point.minus) = point.minus
    calc
      _ = (loop.value ^ 2 * Basic.conj loop.value ^ 2) *
          (radial.value ^ 2 * Basic.conj radial.value ^ 2) * point.minus := by ring1
      _ = point.minus := by rewrite [square_product loop, square_product radial]; ring1

/-- Initial chart transport is the SAME whole source Point after its explicit original parameter-index equality. -/
theorem transport_zero (point : Point site parameter) :
    (transport 0 point).castParameter (parameter_zero site parameter) = point := by
  apply Point.coordinates_eq
  · rewrite [Point.castParameter_plus, transport_plus, Fraction.Field.zero_mul_direct, Twist.phase_zero_value]
    ring1
  · rewrite [Point.castParameter_minus, transport_minus, Fraction.Field.zero_mul_direct, Twist.phase_zero_value]
    have conjugate : Basic.conj (1 : Canonical) = 1 := by decide +kernel
    rewrite [conjugate]
    ring1

/-- The returning conic chart map is exactly TWO original annular twists, with the fibre index transported explicitly.

This uses only actual radius invariance and the endpoint values of the
original rational phase. It assumes no additive phase law, cubic root
identity, Dehn homology action or parameter-monodromy realization.
-/
theorem transport_one (point : Point site parameter) :
    (transport 1 point).castParameter (parameter_one site parameter) = annularTwist (annularTwist point) := by
  apply Point.coordinates_eq
  · rewrite [Point.castParameter_plus, transport_plus, Fraction.Field.one_mul,
      annularTwist_plus (annularTwist point), annularTwist_radialParameter point, annularTwist_plus point]
    ring1
  · rewrite [Point.castParameter_minus, transport_minus, Fraction.Field.one_mul, Twist.phase_one_value,
      annularTwist_minus (annularTwist point), annularTwist_radialParameter point, annularTwist_minus point]
    ring1

/-- The actual inner-boundary fibre trivialization fixes plus and scales minus by the original squared loop phase. -/
def innerTrivialization (time : Fraction.Rational) (point : Point site parameter) :
    Point site (parameterAt site parameter time) :=
  let loop := Twist.phase time
  { plus := point.plus
    minus := loop.value ^ 2 * point.minus
    equation := by
      calc
        _ = loop.value ^ 2 * (point.plus * point.minus) := by ring1
        _ = smoothing site (parameterAt site parameter time) :=
          (congrArg (fun value : Canonical => loop.value ^ 2 * value) point.equation).trans
            (smoothing_at site parameter time).symm }

/-- The actual outer-boundary fibre trivialization scales plus and fixes minus on the SAME target conic. -/
def outerTrivialization (time : Fraction.Rational) (point : Point site parameter) :
    Point site (parameterAt site parameter time) :=
  let loop := Twist.phase time
  { plus := loop.value ^ 2 * point.plus
    minus := point.minus
    equation := by
      calc
        _ = loop.value ^ 2 * (point.plus * point.minus) := by ring1
        _ = smoothing site (parameterAt site parameter time) :=
          (congrArg (fun value : Canonical => loop.value ^ 2 * value) point.equation).trans
            (smoothing_at site parameter time).symm }

/-- On the actual inner boundary, transport equals the complete inner trivialization at the SAME actual target index. -/
theorem transport_inner (time : Fraction.Rational) (point : Point site parameter)
    (boundary : Norm.Basic.normSq point.plus = innerRadiusSq site parameter) :
    transport time point = innerTrivialization time point := by
  have radial := Twist.radialParameter_inner boundary
  apply Point.coordinates_eq
  · rewrite [transport_plus, radial, Fraction.Field.mul_zero_direct, Twist.phase_zero_value]
    change (1 : Canonical) ^ 2 * point.plus = point.plus
    ring1
  · rewrite [transport_minus, radial, Fraction.Field.mul_zero_direct, Twist.phase_zero_value]
    change (Twist.phase time).value ^ 2 * Basic.conj (1 : Canonical) ^ 2 * point.minus =
      (Twist.phase time).value ^ 2 * point.minus
    have conjugate : Basic.conj (1 : Canonical) = 1 := by decide +kernel
    rewrite [conjugate]
    ring1

/-- The admitted source bound derives the actual outer trivialization, without a supplied proper-width conclusion. -/
theorem transport_outer (time : Fraction.Rational) (point : Point site parameter)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (boundary : Norm.Basic.normSq point.plus = outerRadiusSq) :
    transport time point = outerTrivialization time point := by
  have radial := Twist.radialParameter_outer bound boundary
  apply Point.coordinates_eq
  · rewrite [transport_plus, radial, Fraction.Field.mul_one_direct]
    rfl
  · rewrite [transport_minus, radial, Fraction.Field.mul_one_direct]
    let loop := Twist.phase time
    change loop.value ^ 2 * Basic.conj loop.value ^ 2 * point.minus = point.minus
    rewrite [square_product, Basic.one_mul]
    rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

end
