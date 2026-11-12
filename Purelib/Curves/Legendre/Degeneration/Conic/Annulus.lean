module

public import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Quadratic.Split
import Purelib.Tactic.Ring

/-!
# The bounded annulus of the original Legendre conic

The first conic coordinate parametrizes the regular product conic. Its exact
partner is the original smoothing parameter divided by that coordinate. The
computed inner and outer squared radii bound both coordinates and derive
spatial admission for the original signed cubic lift. Exchanging coordinates
preserves this annulus and reverses its two boundaries.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.Field
open Purelib.Geometry.Rational
open Purelib.Polynomial.Quadratic

/-- The computed squared outer radius corresponding to the conic half-width one eighth. -/
@[expose] def outerRadiusSq : Fraction.Rational := (1 / 8) ^ 2

/-- The computed squared inner radius for the same original smoothing value. -/
@[expose] def innerRadiusSq (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  Norm.Basic.normSq (smoothing site parameter) / outerRadiusSq

/-- The closed radial annulus in the original first conic coordinate. -/
@[expose] def Contains (site : Fin 2) (parameter coordinate : Canonical) : Prop :=
  innerRadiusSq site parameter ≤ Norm.Basic.normSq coordinate ∧ Norm.Basic.normSq coordinate ≤ outerRadiusSq

/-- A regular labelled fibre has a strictly positive computed hole radius. -/
theorem innerRadiusSq_pos (site : Fin 2) {parameter : Canonical} (regular : parameter ≠ criticalValue site) :
    0 < innerRadiusSq site parameter :=
  Fraction.Order.Field.div_pos_direct (Norm.Basic.normSq_pos (smoothing_ne_zero site regular))
    (by decide +kernel)

/-- Every admitted coordinate on a regular fibre is apart from the exact Gaussian zero. -/
theorem coordinate_ne_zero {site : Fin 2} {parameter coordinate : Canonical}
    (regular : parameter ≠ criticalValue site) (inside : Contains site parameter coordinate) : coordinate ≠ 0 := by
  have positive := (innerRadiusSq_pos site regular).trans_le inside.1
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at positive
  exact (by decide +kernel : ¬ (0 : Fraction.Rational) < 0) positive

/-- The exact second coordinate determined by the same original smoothing and first coordinate. -/
@[expose] def partner (site : Fin 2) (parameter coordinate : Canonical) : Canonical :=
  smoothing site parameter / coordinate

/-- Multiplying the partner by the same supplied nonzero coordinate recovers the original smoothing. -/
theorem partner_mul_coordinate (site : Fin 2) (parameter coordinate : Canonical) (nonzero : coordinate ≠ 0) :
    partner site parameter coordinate * coordinate = smoothing site parameter :=
  ExplicitField.div_mul_cancel _ nonzero

/-- A regular fibre's partner remains nonzero whenever its first coordinate is nonzero. -/
theorem partner_ne_zero (site : Fin 2) {parameter coordinate : Canonical}
    (regular : parameter ≠ criticalValue site) (nonzero : coordinate ≠ 0) :
    partner site parameter coordinate ≠ 0 :=
  ExplicitField.div_ne_zero (smoothing_ne_zero site regular) nonzero

/-- Exchanging the exact quotient coordinates twice recovers the original first coordinate. -/
theorem partner_partner (site : Fin 2) {parameter coordinate : Canonical}
    (regular : parameter ≠ criticalValue site) (nonzero : coordinate ≠ 0) :
    partner site parameter (partner site parameter coordinate) = coordinate := by
  apply ExplicitField.eq_of_mul_eq_mul_right (partner_ne_zero site regular nonzero)
  exact (partner_mul_coordinate _ _ _ (partner_ne_zero site regular nonzero)).trans
    ((partner_mul_coordinate _ _ _ nonzero).symm.trans (Basic.mul_comm _ _))

/-- The squared norms of the original coordinate pair have the computed smoothing norm as their product. -/
theorem partner_normSq_product (site : Fin 2) (parameter coordinate : Canonical) (nonzero : coordinate ≠ 0) :
    Norm.Basic.normSq (partner site parameter coordinate) * Norm.Basic.normSq coordinate =
      Norm.Basic.normSq (smoothing site parameter) :=
  (Norm.Basic.normSq_mul _ _).symm.trans (congrArg Norm.Basic.normSq (partner_mul_coordinate _ _ _ nonzero))

/-- Exchanging the exact conic coordinates preserves both computed radial bounds. -/
theorem partner_contains {site : Fin 2} {parameter coordinate : Canonical}
    (regular : parameter ≠ criticalValue site) (inside : Contains site parameter coordinate) :
    Contains site parameter (partner site parameter coordinate) := by
  have nonzero := coordinate_ne_zero regular inside
  have product := partner_normSq_product site parameter coordinate nonzero
  have outerPositive : (0 : Fraction.Rational) < outerRadiusSq := by decide +kernel
  have originalLower : Norm.Basic.normSq (smoothing site parameter) / outerRadiusSq ≤
      Norm.Basic.normSq coordinate := inside.1
  have multiplied := (Fraction.Order.Field.div_le_iff_pos outerPositive).mp originalLower
  refine ⟨?_, ?_⟩
  · apply (Fraction.Order.Field.div_le_iff_pos outerPositive).mpr
    calc
      Norm.Basic.normSq (smoothing site parameter) =
          Norm.Basic.normSq (partner site parameter coordinate) * Norm.Basic.normSq coordinate := product.symm
      _ ≤ Norm.Basic.normSq (partner site parameter coordinate) * outerRadiusSq :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2 (Norm.Basic.normSq_nonneg _)
  · apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := Norm.Basic.normSq coordinate) _
      (Norm.Basic.normSq_pos nonzero)
    calc
      Norm.Basic.normSq (partner site parameter coordinate) * Norm.Basic.normSq coordinate =
          Norm.Basic.normSq (smoothing site parameter) := product
      _ ≤ Norm.Basic.normSq coordinate * outerRadiusSq := multiplied
      _ = outerRadiusSq * Norm.Basic.normSq coordinate := Fraction.Field.mul_comm _ _

/-- A radial outer bound internally admits the same coordinate to the computed conic square. -/
theorem coordinate_inside {coordinate : Canonical} (bound : Norm.Basic.normSq coordinate ≤ outerRadiusSq) :
    coordinateBox.Contains coordinate := by
  have distance : Norm.Basic.normSq (coordinate - 0) ≤ (1 / 8 : Fraction.Rational) ^ 2 := by
    rewrite [Basic.sub_zero]
    exact bound
  exact Box.Square.Centered.centeredBox_contains_of_normSq_sub_le (by decide +kernel) distance

/-- Construct the original exact conic point at an admitted regular annulus coordinate. -/
def point (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (inside : Contains site parameter coordinate) : Point site parameter :=
  Point.ofPlus site parameter coordinate (coordinate_ne_zero regular inside)

/-- The annulus parametrization retains the original first coordinate. -/
theorem point_plus (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (inside : Contains site parameter coordinate) :
    (point site parameter coordinate regular inside).plus = coordinate :=
  Point.ofPlus_plus _ _ _ _

/-- The annulus parametrization retains the exact original partner as its second coordinate. -/
theorem point_minus (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (inside : Contains site parameter coordinate) :
    (point site parameter coordinate regular inside).minus = partner site parameter coordinate :=
  Point.ofPlus_minus _ _ _ _

/-- Parametrizing the partner gives the exchanged complete original conic point. -/
theorem point_partner (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (inside : Contains site parameter coordinate) :
    point site parameter (partner site parameter coordinate) regular (partner_contains regular inside) =
      (point site parameter coordinate regular inside).exchange := by
  have recover (conic : Point site parameter) (input : Canonical) (nonzero : input ≠ 0) (same : conic.plus = input) :
      Point.ofPlus site parameter input nonzero = conic := by
    cases same
    exact Point.ofPlus_original conic nonzero
  exact recover _ _ (coordinate_ne_zero regular (partner_contains regular inside)) (point_minus _ _ _ regular inside)

/-- Intrinsic parameter and annulus bounds internally admit the actual recovered cubic base. -/
theorem point_inside (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (parameterInside : (parameterBox site).Contains parameter) (inside : Contains site parameter coordinate) :
    (spatialBox site).Contains (point site parameter coordinate regular inside).base := by
  apply Point.base_inside _ parameterInside
  · rewrite [point_plus]
    exact coordinate_inside inside.2
  · rewrite [point_minus]
    exact coordinate_inside (partner_contains regular inside).2

/-- Construct actual original cubic channels from an annulus coordinate with internally derived spatial clearance. -/
def lift (site : Fin 2) (parameter coordinate : Canonical) (regular : parameter ≠ criticalValue site)
    (parameterInside : (parameterBox site).Contains parameter) (inside : Contains site parameter coordinate) :
    Lift (point site parameter coordinate regular inside)
      (UnitRoot.owner site (point site parameter coordinate regular inside).base
        (point_inside _ _ _ regular parameterInside inside)) :=
  Lift.build (point site parameter coordinate regular inside) (point_inside _ _ _ regular parameterInside inside)

/-- Bounds on both original conic coordinates place its first coordinate in the computed annulus. -/
theorem contains_of_norm_bounds {site : Fin 2} {parameter : Canonical} (conic : Point site parameter)
    (plusBound : Norm.Basic.normSq conic.plus ≤ outerRadiusSq)
    (minusBound : Norm.Basic.normSq conic.minus ≤ outerRadiusSq) : Contains site parameter conic.plus := by
  refine ⟨?_, plusBound⟩
  apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < outerRadiusSq)).mpr
  calc
    Norm.Basic.normSq (smoothing site parameter) = Norm.Basic.normSq (conic.plus * conic.minus) :=
      congrArg Norm.Basic.normSq conic.equation.symm
    _ = Norm.Basic.normSq conic.plus * Norm.Basic.normSq conic.minus := Norm.Basic.normSq_mul _ _
    _ ≤ Norm.Basic.normSq conic.plus * outerRadiusSq :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct minusBound (Norm.Basic.normSq_nonneg _)

/-- Parametrizing an original radially bounded regular conic point recovers that complete exact point. -/
theorem point_original {site : Fin 2} {parameter : Canonical} (conic : Point site parameter)
    (regular : parameter ≠ criticalValue site) (plusBound : Norm.Basic.normSq conic.plus ≤ outerRadiusSq)
    (minusBound : Norm.Basic.normSq conic.minus ≤ outerRadiusSq) :
    point site parameter conic.plus regular (contains_of_norm_bounds conic plusBound minusBound) = conic :=
  Point.ofPlus_original _ _

/-- The exact coordinate exchange takes an outer annulus boundary to its computed inner boundary. -/
theorem partner_outer_boundary {site : Fin 2} {parameter coordinate : Canonical}
    (boundary : Norm.Basic.normSq coordinate = outerRadiusSq) :
    Norm.Basic.normSq (partner site parameter coordinate) = innerRadiusSq site parameter := by
  have nonzero : coordinate ≠ 0 := by
    intro zero
    rewrite [zero, Norm.Basic.normSq_zero] at boundary
    exact (by decide +kernel : (0 : Fraction.Rational) ≠ outerRadiusSq) boundary
  apply Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : outerRadiusSq ≠ 0)
  calc
    Norm.Basic.normSq (partner site parameter coordinate) * outerRadiusSq =
        Norm.Basic.normSq (partner site parameter coordinate) * Norm.Basic.normSq coordinate :=
      congrArg (fun value => Norm.Basic.normSq (partner site parameter coordinate) * value) boundary.symm
    _ = Norm.Basic.normSq (smoothing site parameter) := partner_normSq_product _ _ _ nonzero
    _ = innerRadiusSq site parameter * outerRadiusSq :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)).symm

/-- The exact coordinate exchange takes a regular inner boundary to the same original outer boundary. -/
theorem partner_inner_boundary {site : Fin 2} {parameter coordinate : Canonical}
    (regular : parameter ≠ criticalValue site)
    (boundary : Norm.Basic.normSq coordinate = innerRadiusSq site parameter) :
    Norm.Basic.normSq (partner site parameter coordinate) = outerRadiusSq := by
  have innerPositive := innerRadiusSq_pos site regular
  have nonzero : coordinate ≠ 0 := by
    intro zero
    rewrite [zero, Norm.Basic.normSq_zero] at boundary
    have positive := innerPositive
    rewrite [← boundary] at positive
    exact (by decide +kernel : ¬ (0 : Fraction.Rational) < 0) positive
  apply Fraction.Field.mul_right_cancel_of_ne innerPositive.ne'
  calc
    Norm.Basic.normSq (partner site parameter coordinate) * innerRadiusSq site parameter =
        Norm.Basic.normSq (partner site parameter coordinate) * Norm.Basic.normSq coordinate :=
      congrArg (fun value => Norm.Basic.normSq (partner site parameter coordinate) * value) boundary.symm
    _ = Norm.Basic.normSq (smoothing site parameter) := partner_normSq_product _ _ _ nonzero
    _ = innerRadiusSq site parameter * outerRadiusSq :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)).symm
    _ = outerRadiusSq * innerRadiusSq site parameter := Fraction.Field.mul_comm _ _

/-- The original half-gap is on the annulus waist whenever its computed squared norm fits the outer bound. -/
theorem waist_contains (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (halfGap site parameter) ≤ outerRadiusSq) :
    Contains site parameter (halfGap site parameter) := by
  refine ⟨?_, bound⟩
  apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < outerRadiusSq)).mpr
  unfold smoothing
  rewrite [pow_two, Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound (Norm.Basic.normSq_nonneg _)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus
