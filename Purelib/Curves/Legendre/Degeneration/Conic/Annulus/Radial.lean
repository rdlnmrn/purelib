module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
public import Purelib.Approximation.Gaussian.Division.Prepared.ExactFactor
import Purelib.Data.Gaussian.Scale
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Quadratic.Split
import Purelib.Tactic.Ring

/-!
# Radial original conic circles and regular parallel waist channels

The positive rational scale sends the original half-gap circle to the exact
conic coordinates `u=r*h*z` and `v=(h/r)*conj(z)`. Scales from one to two fit
the original annulus under the computed tighter parameter radius. Scale one
recovers the complete original waist point; scale two has an internally proved
uniform nonzero normalized ordinate and a division-ready presentation of the
identical original cubic lift channel.

The pointwise radial construction supplies no integral homotopy by itself.
Finite radial/time root transport, realized primitive boundaries, agreement of
value integrals and canonical cut attachment remain separate certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.Field
open Purelib.Geometry.Rational

/-- Rational coordinate scaling by one preserves the identical original Gaussian point. -/
private theorem scale_one (value : Canonical) : Scale.scale 1 value = value := by
  apply Basic.ext
  · change 1 * value.re = value.re
    exact Fraction.Field.one_mul _
  · change 1 * value.im = value.im
    exact Fraction.Field.one_mul _

/-- The retained certified unit direction multiplied by its conjugate is exactly one. -/
private theorem unit_product (original : UnitVertex) : original.value * Basic.conj original.value = 1 := by
  have result := Basic.Canonical.mul_conj original.value
  rewrite [← Norm.Basic.normSq_eq_canonical, original.unit] at result
  exact result

/-- Construct the original exact conic point with both computed radial coordinates on the retained unit direction. -/
def point (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) : Point site parameter :=
  { plus := Scale.scale scale (halfGap site parameter * original.value)
    minus := Scale.scale scale⁻¹ (halfGap site parameter * Basic.conj original.value)
    equation := by
      rewrite [Scale.scale_mul_scale, Fraction.Field.mul_inv_cancel scale positive.ne', scale_one]
      calc
        _ = halfGap site parameter ^ 2 * (original.value * Basic.conj original.value) := by ring1
        _ = halfGap site parameter ^ 2 * 1 := congrArg (fun value => halfGap site parameter ^ 2 * value)
          (unit_product original)
        _ = smoothing site parameter := by
          rewrite [Basic.mul_one]
          rfl }

/-- The original first conic coordinate is the actual retained radially scaled half-gap direction. -/
theorem point_plus (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) :
    (point site parameter scale original positive).plus =
      Scale.scale scale (halfGap site parameter * original.value) := by
  unfold point
  rfl

/-- The original second conic coordinate is the actual retained inverse-scaled conjugate half-gap direction. -/
theorem point_minus (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) :
    (point site parameter scale original positive).minus =
      Scale.scale scale⁻¹ (halfGap site parameter * Basic.conj original.value) := by
  unfold point
  rfl

/-- The tighter original parameter-distance bound gives the exact radial family half-gap budget. -/
theorem halfGap_bound (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Norm.Basic.normSq (halfGap site parameter) ≤ 1 / 256 := by
  have norm := congrArg Norm.Basic.normSq
    (Polynomial.Quadratic.Split.halfGap_mul_two (criticalValue site) parameter (by decide +kernel))
  change Norm.Basic.normSq (halfGap site parameter * 2) = Norm.Basic.normSq (parameter - criticalValue site) at norm
  rewrite [Norm.Basic.normSq_mul, show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel] at norm
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4) _ (by decide +kernel)
  calc
    _ = Norm.Basic.normSq (parameter - criticalValue site) := norm
    _ ≤ 1 / 64 := bound
    _ = (1 / 256 : Fraction.Rational) * 4 := by decide +kernel

/-- Both original radial conic coordinates satisfy the annulus outer bound throughout the retained scale interval. -/
theorem point_norm_bounds (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Norm.Basic.normSq (point site parameter scale original positive).plus ≤ outerRadiusSq ∧
      Norm.Basic.normSq (point site parameter scale original positive).minus ≤ outerRadiusSq := by
  have gapBound := halfGap_bound site parameter bound
  have scaleBound : scale ^ 2 ≤ 4 := by
    have result := Arithmetic.pow_le_pow_direct positive.le upper 2
    rewrite [show (2 : Fraction.Rational) ^ 2 = 4 by decide +kernel] at result
    exact result
  have inverseBound : scale⁻¹ ≤ 1 := by
    have result := Fraction.Order.Field.inv_le_inv_of_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 1) lower
    rewrite [show (1 : Fraction.Rational)⁻¹ = 1 by decide +kernel] at result
    exact result
  have inverseSquare : (scale⁻¹) ^ 2 ≤ 1 := by
    have result := Arithmetic.pow_le_pow_direct (Fraction.Order.Field.inv_pos_direct positive).le
      inverseBound 2
    rewrite [show (1 : Fraction.Rational) ^ 2 = 1 by decide +kernel] at result
    exact result
  constructor
  · rewrite [point_plus, Scale.normSq_scale, Norm.Basic.normSq_mul, original.unit, Fraction.Field.mul_one_direct]
    calc
      _ ≤ 4 * Norm.Basic.normSq (halfGap site parameter) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct scaleBound (Norm.Basic.normSq_nonneg _)
      _ ≤ 4 * (1 / 256) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct gapBound (by decide +kernel)
      _ = outerRadiusSq := by decide +kernel
  · rewrite [point_minus, Scale.normSq_scale, Norm.Basic.normSq_mul, Norm.Basic.normSq_conj,
      original.unit, Fraction.Field.mul_one_direct]
    calc
      _ ≤ 1 * Norm.Basic.normSq (halfGap site parameter) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct inverseSquare (Norm.Basic.normSq_nonneg _)
      _ = Norm.Basic.normSq (halfGap site parameter) := Fraction.Field.one_mul _
      _ ≤ 1 / 256 := gapBound
      _ ≤ outerRadiusSq := by decide +kernel

/-- The same original radially scaled point is admitted to the original annulus with all clearance paid internally. -/
theorem point_contains (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Contains site parameter (point site parameter scale original positive).plus :=
  contains_of_norm_bounds (point site parameter scale original positive)
    (point_norm_bounds site parameter scale original positive lower upper bound).1
    (point_norm_bounds site parameter scale original positive lower upper bound).2

/-- All original radial-family bases have internally derived clearance in the same signed cofactor patch. -/
theorem point_inside (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    (spatialBox site).Contains (point site parameter scale original positive).base := by
  have bounds := point_norm_bounds site parameter scale original positive lower upper bound
  exact Point.base_inside (point site parameter scale original positive)
    (Waist.parameter_inside site parameter (bound.trans (by decide +kernel)))
    (Annulus.coordinate_inside bounds.1) (Annulus.coordinate_inside bounds.2)

/-- Construct original cubic channels on the radial family, acquiring the original signed cofactor certificate once. -/
def lift (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Lift (point site parameter scale original positive)
      (UnitRoot.owner site (point site parameter scale original positive).base
        (point_inside site parameter scale original positive lower upper bound)) :=
  Lift.build (point site parameter scale original positive)
    (point_inside site parameter scale original positive lower upper bound)

/-- Scale one recovers the complete original waist point on its original retained unit direction. -/
theorem point_one (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)) :
    point site parameter 1 original (by decide +kernel) = Waist.point site parameter original regular bound := by
  apply Point.coordinates_eq
  · rewrite [point_plus, Waist.point_plus, scale_one]
    rfl
  · rewrite [point_minus, Waist.point_minus, show (1 : Fraction.Rational)⁻¹ = 1 by decide +kernel, scale_one]
    rfl

/-- The two retained original signed cubic lifts agree whenever their exact original conic points agree. -/
private def lifts_agree {site : Fin 2} {parameter : Canonical} {first last : Point site parameter}
    (equal : first = last) (firstInside : (spatialBox site).Contains first.base)
    (lastInside : (spatialBox site).Contains last.base)
    (firstLift : Lift first (UnitRoot.owner site first.base firstInside))
    (lastLift : Lift last (UnitRoot.owner site last.base lastInside)) :
    NamedEquivalent firstLift.value.name lastLift.value.name := by
  cases equal
  have roots : firstLift.unitRoot.value = lastLift.unitRoot.value := by
    rewrite [firstLift.unitRoot_eq, lastLift.unitRoot_eq, firstLift.unitOwner_eq, lastLift.unitOwner_eq]
    rfl
  exact Lift.value_agrees firstLift lastLift
    (NamedEquivalent.transport (congrArg (fun value => value.name) roots).symm rfl (NamedEquivalent.refl _))

/-- The actual scale-one radial cubic channel agrees with the complete original waist channel, retaining both owners. -/
def lift_one_agrees (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    NamedEquivalent (lift site parameter 1 original (by decide +kernel) (by decide +kernel)
      (by decide +kernel) bound).value.name
      (Waist.lift site parameter original regular (bound.trans (by decide +kernel))).value.name :=
  lifts_agree (point_one site parameter original regular (bound.trans (by decide +kernel)))
    (point_inside site parameter 1 original (by decide +kernel) (by decide +kernel) (by decide +kernel) bound)
    (Waist.point_inside site parameter original regular (bound.trans (by decide +kernel)))
    (lift site parameter 1 original (by decide +kernel) (by decide +kernel) (by decide +kernel) bound)
    (Waist.lift site parameter original regular (bound.trans (by decide +kernel)))

/-- The two exact ellipse coefficients of the radial normalized-ordinate direction. -/
@[expose] def ordinateDirection (scale : Fraction.Rational) (original : UnitVertex) : Canonical :=
  ⟨((scale - scale⁻¹) * (1 / 2)) * original.value.re,
    ((scale + scale⁻¹) * (1 / 2)) * original.value.im⟩

/-- The actual original normalized ordinate retains the original half-gap and computed ellipse direction. -/
theorem point_ordinate (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (original : UnitVertex)
    (positive : 0 < scale) :
    (point site parameter scale original positive).ordinate =
      halfGap site parameter * ordinateDirection scale original := by
  have halfTwo : (1 / 2 : Fraction.Rational) * 2 = 1 := by decide +kernel
  have directionTwo : ordinateDirection scale original * 2 =
      Scale.scale scale original.value - Scale.scale scale⁻¹ (Basic.conj original.value) := by
    apply Basic.ext
    · simp only [Basic.mul_re, Basic.sub_re, Scale.scale_re, ordinateDirection, Basic.conj,
        show (2 : Canonical).re = 2 by decide +kernel, show (2 : Canonical).im = 0 by decide +kernel]
      calc
        _ = ((scale - scale⁻¹) * original.value.re) * ((1 / 2) * 2) := by ring1
        _ = (scale - scale⁻¹) * original.value.re := by
          rewrite [halfTwo, Fraction.Field.mul_one_direct]
          rfl
        _ = _ := by ring1
    · simp only [Basic.mul_im, Basic.sub_im, Scale.scale_im, ordinateDirection, Basic.conj,
        show (2 : Canonical).re = 2 by decide +kernel, show (2 : Canonical).im = 0 by decide +kernel]
      calc
        _ = ((scale + scale⁻¹) * original.value.im) * ((1 / 2) * 2) := by ring1
        _ = (scale + scale⁻¹) * original.value.im := by
          rewrite [halfTwo, Fraction.Field.mul_one_direct]
          rfl
        _ = _ := by ring1
  apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  calc
    _ = (point site parameter scale original positive).plus - (point site parameter scale original positive).minus :=
      Polynomial.Quadratic.Split.halfGap_mul_two _ _ (by decide +kernel)
    _ = (halfGap site parameter * ordinateDirection scale original) * 2 := by
      rewrite [point_plus, point_minus]
      rewrite [Scale.scale_mul_right, Scale.scale_mul_right]
      calc
        _ = halfGap site parameter *
            (Scale.scale scale original.value - Scale.scale scale⁻¹ (Basic.conj original.value)) := by ring1
        _ = halfGap site parameter * (ordinateDirection scale original * 2) :=
          congrArg (fun value => halfGap site parameter * value) directionTwo.symm
        _ = _ := by ring1

/-- Every radial ellipse direction has the exact squared lower bound of its shorter axis. -/
theorem ordinateDirection_lower (scale : Fraction.Rational) (original : UnitVertex) (positive : 0 < scale) :
    ((scale - scale⁻¹) * (1 / 2)) ^ 2 ≤ Norm.Basic.normSq (ordinateDirection scale original) := by
  let short := (scale - scale⁻¹) * (1 / 2)
  let long := (scale + scale⁻¹) * (1 / 2)
  have difference : long ^ 2 = short ^ 2 + 1 := by
    calc
      _ = short ^ 2 + (scale * scale⁻¹) * (4 * (1 / 2) ^ 2) := by unfold short long; ring1
      _ = short ^ 2 + scale * scale⁻¹ := by
        rewrite [show (4 * (1 / 2) ^ 2 : Fraction.Rational) = 1 by decide +kernel,
          Fraction.Field.mul_one_direct]
        rfl
      _ = _ := congrArg (fun value => short ^ 2 + value) (Fraction.Field.mul_inv_cancel scale positive.ne')
  have unit := original.unit
  change original.value.re ^ 2 + original.value.im ^ 2 = 1 at unit
  change short ^ 2 ≤ (short * original.value.re) ^ 2 + (long * original.value.im) ^ 2
  have reading : (short * original.value.re) ^ 2 + (long * original.value.im) ^ 2 =
      short ^ 2 + original.value.im ^ 2 := by
    calc
      _ = short ^ 2 * (original.value.re ^ 2 + original.value.im ^ 2) +
          (long ^ 2 - short ^ 2) * original.value.im ^ 2 := by ring1
      _ = short ^ 2 * 1 + ((short ^ 2 + 1) - short ^ 2) * original.value.im ^ 2 := by
        rewrite [unit, difference]
        rfl
      _ = _ := by ring1
  rewrite [reading]
  have paid := Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (short ^ 2))
    (Arithmetic.sq_nonneg_direct original.value.im)
  rewrite [add_zero] at paid
  exact paid

/-- The full original radial normalized ordinate has the computed half-gap times short-axis squared-norm lower bound. -/
theorem point_ordinate_lower (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational)
    (original : UnitVertex) (positive : 0 < scale) :
    Norm.Basic.normSq (halfGap site parameter) * ((scale - scale⁻¹) * (1 / 2)) ^ 2 ≤
      Norm.Basic.normSq (point site parameter scale original positive).ordinate := by
  rewrite [point_ordinate, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (ordinateDirection_lower scale original positive) (Norm.Basic.normSq_nonneg _)

/-- The scale-two parallel circle stays uniformly away from normalized-ordinate zero. -/
theorem parallel_ordinate_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    (9 / 16 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq (point site parameter 2 original (by decide +kernel)).ordinate := by
  have result := point_ordinate_lower site parameter 2 original (by decide +kernel)
  rewrite [show (((2 : Fraction.Rational) - 2⁻¹) * (1 / 2)) ^ 2 = 9 / 16 by decide +kernel] at result
  exact (Fraction.Field.mul_comm _ _).trans_le result

/-- Intrinsic regularity gives the exact nonzero normalized ordinate of the original parallel cubic channel. -/
theorem parallel_ordinate_ne_zero (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) :
    (point site parameter 2 original (by decide +kernel)).ordinate ≠ 0 := by
  have gapNonzero := Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm
  have positive := Arithmetic.mul_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 9 / 16)
    (Norm.Basic.normSq_pos gapNonzero)
  have paid := positive.trans_le (parallel_ordinate_lower site parameter original)
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at paid
  exact (by decide +kernel : ¬ (0 : Fraction.Rational) < 0) paid

/-- Prepare the identical retained parallel cubic channel for odd-power differentials using its same cofactor cache. -/
def parallelPrepared {site : Fin 2} {parameter : Canonical} (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    {unit : Owner ((unitPolynomial site).eval (point site parameter 2 original (by decide +kernel)).base)}
    (actual : Lift (point site parameter 2 original (by decide +kernel)) unit) : Division.Prepared actual.value :=
  Division.Prepared.ofExactRight actual.value actual.unitRoot.value
    (point site parameter 2 original (by decide +kernel)).ordinate actual.value_eq
    (parallel_ordinate_ne_zero site parameter original regular) actual.unitRoot.apart

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
