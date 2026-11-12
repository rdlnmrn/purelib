module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
public import Purelib.Data.Gaussian.Norm.Components.Maximum
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Tactic.Ring
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field

/-! # Branch-factor clearance on the actual parallel conic

The two labelled collision factors have exact ellipse quadrances. A local
square whose half-width is one thirty-second of the original half-gap's
maximum absolute coordinate retains explicit floors on both branch factors
and the remaining cofactor. Their product constructs the existing full-cubic
RegionClearance. A constant dyadic chart depth pays these spatial squares;
no mesh is enumerated and no root or preparation cache is replaced.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rational.Box.Square
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches

/-- The original unit quadrance bounds the signed real coordinate without extracting a square root. -/
private theorem real_bounds (original : UnitVertex) : -1 ≤ original.value.re ∧ original.value.re ≤ 1 := by
  have realSquare : original.value.re ^ 2 ≤ Norm.Basic.normSq original.value := by
    change original.value.re ^ 2 ≤ original.value.re ^ 2 + original.value.im ^ 2
    exact (show original.value.re ^ 2 = original.value.re ^ 2 + 0 from by ring1).trans_le
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.sq_nonneg_direct original.value.im))
  rewrite [original.unit] at realSquare
  exact Bounds.Square.signed_bounds_of_sq_le_sq (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    (realSquare.trans_eq (by decide +kernel : (1 : Fraction.Rational) = 1 ^ 2))

/-- The actual original parallel ellipse has the internally computed longer axis five quarters. -/
private theorem longAxis_two : longAxis 2 = (5 / 4 : Fraction.Rational) := by decide +kernel

/-- The actual original parallel ellipse has the internally computed shorter axis three quarters. -/
private theorem shortAxis_two : shortAxis 2 = (3 / 4 : Fraction.Rational) := by decide +kernel

/-- Division by the original thirty-two retains its exact squared rational coefficient. -/
private theorem divide_thirtyTwo_sq (value : Fraction.Rational) :
    (value / 32) ^ 2 = (1 / Fraction.Cast.fromInt 1024) * value ^ 2 := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.mul_pow_direct]
  calc
    _ = ((32 : Fraction.Rational)⁻¹) ^ 2 * value ^ 2 := by ring1
    _ = _ := congrArg (fun factor => factor * value ^ 2)
      (by decide +kernel : ((32 : Fraction.Rational)⁻¹) ^ 2 = 1 / Fraction.Cast.fromInt 1024)

/-- A common branch-factor movement payment retains one quarter of the original factor quadrance. -/
private theorem factor_lower_of_distance (source root value : Canonical) (gap : Fraction.Rational)
    (gapNonnegative : 0 ≤ gap) (sourceLower : gap / 16 ≤ Norm.Basic.normSq (source - root))
    (distance : Norm.Basic.normSq (value - source) ≤ gap / Fraction.Cast.fromInt 512) :
    gap / 64 ≤ Norm.Basic.normSq (value - root) := by
  have first : gap / Fraction.Cast.fromInt 512 ≤ (gap / 16) / 4 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ ≤ gap * ((16 : Fraction.Rational)⁻¹ * (4 : Fraction.Rational)⁻¹) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) gapNonnegative
      _ = _ := by ring1
  have quarter := Fraction.Order.Field.divide_mono sourceLower (by decide +kernel : (0 : Fraction.Rational) < 4)
  have originalDistance : Norm.Basic.normSq ((source - root) - (value - root)) =
      Norm.Basic.normSq (value - source) := by
    rewrite [show (source - root) - (value - root) = source - value by ring1]
    exact Norm.Bounds.normSq_sub_symm source value
  have close : Norm.Basic.normSq ((source - root) - (value - root)) ≤
      Norm.Basic.normSq (source - root) / 4 := by
    rewrite [originalDistance]
    exact distance.trans (first.trans quarter)
  calc
    _ = (gap / 16) / 4 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = gap * ((64 : Fraction.Rational)⁻¹) := rfl
        _ = gap * ((16 : Fraction.Rational)⁻¹ * (4 : Fraction.Rational)⁻¹) :=
          congrArg (fun factor => gap * factor) (by decide +kernel)
        _ = _ := by ring1
    _ ≤ Norm.Basic.normSq (source - root) / 4 := quarter
    _ ≤ Norm.Basic.normSq (value - root) := Norm.Bounds.quarter_normSq_le_of_close _ _ close

/-- The original parallel base direction plus one has the exact fixed-branch ellipse quadrance. -/
theorem baseDirection_add_one_normSq (original : UnitVertex) :
    Norm.Basic.normSq (baseDirection 2 original.value + 1) = (5 / 4 + original.value.re) ^ 2 := by
  unfold Norm.Basic.normSq
  simp only [Basic.add_re, Basic.add_im, baseDirection,
    show (1 : Canonical).re = 1 by decide +kernel, show (1 : Canonical).im = 0 by decide +kernel]
  rewrite [longAxis_two, shortAxis_two]
  have unit : original.value.re ^ 2 + original.value.im ^ 2 = 1 := original.unit
  have axes : (5 / 4 : Fraction.Rational) ^ 2 = (3 / 4) ^ 2 + 1 := by decide +kernel
  calc
    _ = ((5 / 4) ^ 2 - (3 / 4) ^ 2 - 1) * original.value.re ^ 2 +
        (3 / 4) ^ 2 * (original.value.re ^ 2 + original.value.im ^ 2 - 1) +
        (1 - (5 / 4) ^ 2 + (3 / 4) ^ 2) + (5 / 4 + original.value.re) ^ 2 := by ring1
    _ = _ := by rewrite [axes, unit]; ring1

/-- The original parallel base direction minus one has the exact moving-branch ellipse quadrance. -/
theorem baseDirection_sub_one_normSq (original : UnitVertex) :
    Norm.Basic.normSq (baseDirection 2 original.value - 1) = (5 / 4 - original.value.re) ^ 2 := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re, Basic.sub_im, baseDirection,
    show (1 : Canonical).re = 1 by decide +kernel, show (1 : Canonical).im = 0 by decide +kernel]
  rewrite [longAxis_two, shortAxis_two]
  have unit : original.value.re ^ 2 + original.value.im ^ 2 = 1 := original.unit
  have axes : (5 / 4 : Fraction.Rational) ^ 2 = (3 / 4) ^ 2 + 1 := by decide +kernel
  calc
    _ = ((5 / 4) ^ 2 - (3 / 4) ^ 2 - 1) * original.value.re ^ 2 +
        (3 / 4) ^ 2 * (original.value.re ^ 2 + original.value.im ^ 2 - 1) +
        (1 - (5 / 4) ^ 2 + (3 / 4) ^ 2) + (5 / 4 - original.value.re) ^ 2 := by ring1
    _ = _ := by rewrite [axes, unit]; ring1

/-- Each exact parallel branch direction has quadrance at least one sixteenth. -/
theorem baseDirection_branch_lower (original : UnitVertex) :
    (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq (baseDirection 2 original.value + 1) ∧
      (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq (baseDirection 2 original.value - 1) := by
  have real := real_bounds original
  have plus := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (5 / 4 : Fraction.Rational)) real.1
  have minus := Arithmetic.sub_le_sub_left_direct real.2 (5 / 4)
  rewrite [show (5 / 4 + -1 : Fraction.Rational) = 1 / 4 by decide +kernel] at plus
  rewrite [show (5 / 4 - 1 : Fraction.Rational) = 1 / 4 by decide +kernel] at minus
  have plusSquare := Arithmetic.pow_le_pow_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 4) plus 2
  have minusSquare := Arithmetic.pow_le_pow_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 4) minus 2
  rewrite [show (1 / 4 : Fraction.Rational) ^ 2 = 1 / 16 by decide +kernel] at plusSquare minusSquare
  exact ⟨plusSquare.trans_eq (baseDirection_add_one_normSq original).symm,
    minusSquare.trans_eq (baseDirection_sub_one_normSq original).symm⟩

/-- The actual original parallel spatial point retains both labelled collision-factor quadrance floors. -/
theorem point_branch_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    Norm.Basic.normSq (halfGap site parameter) / 16 ≤ Norm.Basic.normSq
      ((point site parameter 2 original (by decide +kernel)).base - criticalValue site) ∧
    Norm.Basic.normSq (halfGap site parameter) / 16 ≤ Norm.Basic.normSq
      ((point site parameter 2 original (by decide +kernel)).base - parameter) := by
  have fixedRoot : center site parameter - halfGap site parameter = criticalValue site :=
    Polynomial.Quadratic.Split.center_sub_halfGap _ _ (by decide +kernel)
  have movingRoot : center site parameter + halfGap site parameter = parameter :=
    Polynomial.Quadratic.Split.center_add_halfGap _ _ (by decide +kernel)
  have fixed : (point site parameter 2 original (by decide +kernel)).base - criticalValue site =
      halfGap site parameter * (baseDirection 2 original.value + 1) := by
    rewrite [point_base]
    calc
      _ = center site parameter + halfGap site parameter * baseDirection 2 original.value -
          (center site parameter - halfGap site parameter) :=
        congrArg (fun root => center site parameter + halfGap site parameter * baseDirection 2 original.value - root)
          fixedRoot.symm
      _ = _ := by ring1
  have moving : (point site parameter 2 original (by decide +kernel)).base - parameter =
      halfGap site parameter * (baseDirection 2 original.value - 1) := by
    rewrite [point_base]
    calc
      _ = center site parameter + halfGap site parameter * baseDirection 2 original.value -
          (center site parameter + halfGap site parameter) :=
        congrArg (fun root => center site parameter + halfGap site parameter * baseDirection 2 original.value - root)
          movingRoot.symm
      _ = _ := by ring1
  have directions := baseDirection_branch_lower original
  have floorReading : Norm.Basic.normSq (halfGap site parameter) / 16 =
      Norm.Basic.normSq (halfGap site parameter) * (1 / 16) := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct]
    exact congrArg (fun factor => Norm.Basic.normSq (halfGap site parameter) * factor) (by decide +kernel)
  constructor
  · rewrite [fixed, Norm.Basic.normSq_mul]
    exact floorReading.trans_le
      (Arithmetic.mul_le_mul_of_nonneg_left_direct directions.1 (Norm.Basic.normSq_nonneg _))
  · rewrite [moving, Norm.Basic.normSq_mul]
    exact floorReading.trans_le
      (Arithmetic.mul_le_mul_of_nonneg_left_direct directions.2 (Norm.Basic.normSq_nonneg _))

/-- The fixed spatial half-width is one thirty-second of the original signed half-gap's maximum absolute coordinate. -/
@[expose] def radius (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  Norm.Components.maximum (halfGap site parameter) / 32

/-- A regular labelled collision parameter makes the original factor-clear half-width strictly positive. -/
theorem radius_positive (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    0 < radius site parameter :=
  Fraction.Order.Field.div_pos_direct (Norm.Components.maximum_positive
    (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm)) (by decide +kernel)

/-- The retained radius square is at most one thousand twenty-fourth of the original gap quadrance. -/
theorem radius_sq_upper (site : Fin 2) (parameter : Canonical) :
    radius site parameter ^ 2 ≤ Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 1024 := by
  rewrite [radius, divide_thirtyTwo_sq]
  calc
    _ ≤ (1 / Fraction.Cast.fromInt 1024) * Norm.Basic.normSq (halfGap site parameter) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Norm.Components.maximum_sq_le_normSq _) (by decide +kernel)
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- The retained radial parameter bound puts the same sharp half-width below one five-hundred-twelfth.

The original half-gap quadrance bound and radius-square estimate give the
closed scalar bound without extracting a square root or replacing a cache.
-/
theorem radius_le (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    radius site parameter ≤ 1 / Fraction.Cast.fromInt 512 := by
  have divided := Fraction.Order.Field.divide_mono (halfGap_bound site parameter bound)
    (by decide +kernel : (0 : Fraction.Rational) < Fraction.Cast.fromInt 1024)
  have squared : radius site parameter ^ 2 ≤ (1 / Fraction.Cast.fromInt 512 : Fraction.Rational) ^ 2 :=
    (radius_sq_upper site parameter).trans (divided.trans_eq (by decide +kernel))
  exact (Bounds.Square.signed_bounds_of_sq_le_sq (by decide +kernel) squared).2

/-- The retained radius square bounds one two-thousand-forty-eighth of the original gap quadrance. -/
theorem radius_sq_lower (site : Fin 2) (parameter : Canonical) :
    Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 2048 ≤ radius site parameter ^ 2 := by
  rewrite [radius, divide_thirtyTwo_sq, Fraction.Field.div_eq_mul_inv_direct]
  calc
    _ ≤ (2 * Norm.Components.maximum (halfGap site parameter) ^ 2) *
        (Fraction.Cast.fromInt 2048)⁻¹ :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Norm.Components.normSq_le_twice_maximum_sq _) (by decide +kernel)
    _ = (2 * (Fraction.Cast.fromInt 2048)⁻¹) * Norm.Components.maximum (halfGap site parameter) ^ 2 := by ring1
    _ = _ := congrArg (fun factor => factor * Norm.Components.maximum (halfGap site parameter) ^ 2)
      (by decide +kernel : 2 * (Fraction.Cast.fromInt 2048 : Fraction.Rational)⁻¹ = 1 / Fraction.Cast.fromInt 1024)

/-- The exact original parallel spatial point and positive factor-clear radius determine one actual rational square. -/
@[expose] def box (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) : Box :=
  Geometry.Rational.Box.Square.Centered.Affine.centeredSquare
    (point site parameter 2 original (by decide +kernel)).base (radius site parameter)
      (radius_positive site parameter regular).le

/-- The actual original parallel point belongs to the same retained factor-clear spatial square. -/
theorem point_inside_box (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) :
    (box site parameter original regular).Contains (point site parameter 2 original (by decide +kernel)).base :=
  Geometry.Rational.Box.Square.Centered.centeredSquare_contains_center _ _
    (radius_positive site parameter regular).le

/-- Actual squared spatial displacement paid by the original factor radius gives containment in that exact square. -/
theorem contains_of_distance (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (paid : Norm.Basic.normSq (value - (point site parameter 2 original (by decide +kernel)).base) ≤
      radius site parameter ^ 2) : (box site parameter original regular).Contains value :=
  Geometry.Rational.Box.Square.Centered.centeredBox_contains_of_normSq_sub_le
    (radius_positive site parameter regular).le paid

/-- Every point of the retained factor-clear square moves by at most one five-hundred-twelfth of the gap quadrance. -/
theorem displacement_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (value - (point site parameter 2 original (by decide +kernel)).base) ≤
      Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512 := by
  have original := Geometry.Rational.Box.Square.Centered.centeredSquare_normSq_sub_center_le _
    (radius_positive site parameter regular).le inside
  have doubled := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (radius_sq_upper site parameter) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  exact original.trans (doubled.trans_eq (by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = Norm.Basic.normSq (halfGap site parameter) * (2 * (Fraction.Cast.fromInt 1024)⁻¹) := by ring1
      _ = _ := congrArg (fun factor => Norm.Basic.normSq (halfGap site parameter) * factor) (by decide +kernel)))

/-- Both original labelled collision factors retain the same explicit floor throughout that exact spatial square. -/
theorem branch_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (halfGap site parameter) / 64 ≤ Norm.Basic.normSq (value - criticalValue site) ∧
      Norm.Basic.normSq (halfGap site parameter) / 64 ≤ Norm.Basic.normSq (value - parameter) :=
  ⟨factor_lower_of_distance _ _ _ _ (Norm.Basic.normSq_nonneg _)
      (point_branch_lower site parameter original).1 (displacement_le site parameter original regular inside),
    factor_lower_of_distance _ _ _ _ (Norm.Basic.normSq_nonneg _)
      (point_branch_lower site parameter original).2 (displacement_le site parameter original regular inside)⟩

/-- The remaining original cofactor retains quadrance at least one sixteenth throughout the factor-clear square. -/
theorem cofactor_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq ((unitPolynomial site).eval value) := by
  let source := (point site parameter 2 original (by decide +kernel)).base
  have sourceLower := unit_lower site (point_inside site parameter 2 original (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound)
  have displacement := displacement_le site parameter original regular inside
  have upper := Fraction.Order.Field.divide_mono
    ((halfGap_bound site parameter bound).trans (by decide +kernel : (1 / 256 : Fraction.Rational) ≤ 1))
    (by decide +kernel : (0 : Fraction.Rational) < Fraction.Cast.fromInt 512)
  have small : Norm.Basic.normSq (value - source) ≤ (1 / 16 : Fraction.Rational) :=
    displacement.trans (upper.trans (by decide +kernel))
  have difference : (unitPolynomial site).eval source - (unitPolynomial site).eval value = source - value := by
    rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
      Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    ring1
  have sourceQuarter := Fraction.Order.Field.divide_mono sourceLower (by decide +kernel : (0 : Fraction.Rational) < 4)
  rewrite [show ((1 / 4) / 4 : Fraction.Rational) = 1 / 16 by decide +kernel] at sourceQuarter
  have close : Norm.Basic.normSq ((unitPolynomial site).eval source - (unitPolynomial site).eval value) ≤
      Norm.Basic.normSq ((unitPolynomial site).eval source) / 4 := by
    rewrite [difference, Norm.Bounds.normSq_sub_symm source value]
    exact small.trans sourceQuarter
  exact sourceQuarter.trans (Norm.Bounds.quarter_normSq_le_of_close _ _ close)

/-- The same positive full-cubic floor is retained by all original factor-clear squares at a fixed regular parameter. -/
@[expose] def floor (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (1 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) ^ 2

/-- The original signed nonzero half-gap makes the retained full-cubic factor floor strictly positive. -/
theorem floor_positive (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    0 < floor site parameter :=
  Arithmetic.mul_pos_direct (by decide +kernel)
    (Arithmetic.pow_pos_direct
      (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm)) 2)

/-- Every point in the actual factor-clear square pays the internally derived original full-cubic quadrance floor. -/
theorem cubic_lower (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    floor site parameter ≤ Norm.Basic.normSq ((Paths.polynomial parameter).eval value) := by
  have branch := branch_lower site parameter original regular inside
  have unit := cofactor_lower site parameter original regular bound inside
  have gapNonnegative := Norm.Basic.normSq_nonneg (halfGap site parameter)
  have branchNonnegative : 0 ≤ Norm.Basic.normSq (halfGap site parameter) / 64 :=
    Fraction.Order.Field.div_nonneg_direct gapNonnegative (by decide +kernel)
  have pair := (Arithmetic.mul_le_mul_of_nonneg_right_direct branch.1 branchNonnegative).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct branch.2 (Norm.Basic.normSq_nonneg _))
  have triple := (Arithmetic.mul_le_mul_of_nonneg_right_direct pair
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 16)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct unit
        (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)))
  have exactFloor : (Norm.Basic.normSq (halfGap site parameter) / 64) *
      (Norm.Basic.normSq (halfGap site parameter) / 64) * (1 / 16) = floor site parameter := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    unfold floor
    calc
      _ = ((64 : Fraction.Rational)⁻¹ ^ 2 * (16 : Fraction.Rational)⁻¹) *
          Norm.Basic.normSq (halfGap site parameter) ^ 2 := by ring1
      _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
        (by decide +kernel : (64 : Fraction.Rational)⁻¹ ^ 2 * (16 : Fraction.Rational)⁻¹ =
          1 / Fraction.Cast.fromInt 65536)
  rewrite [polynomial_eq_pair, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  exact exactFloor.symm.trans_le triple

/-- The uniform original owner-reading quadrance floor on the retained regular parallel chart. -/
@[expose] def rootFloor (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  min 1 (floor site parameter / 4) / 8

/-- Regularity makes the retained uniform owner-reading floor strictly positive. -/
theorem rootFloor_positive (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site) :
    0 < rootFloor site parameter :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Basic.lt_min (by decide +kernel)
      (Fraction.Order.Field.div_pos_direct (floor_positive site parameter regular) (by decide +kernel)))
    (by decide +kernel)

/-- Every actual owner above a point in the retained chart region keeps the same uniform sample-norm floor.

The original factor floor bounds the actual full cubic radicand. Its capped
quarter, divided by eight, is below the actual certificate's unchanged whole-ball margin, regardless
of the inherited owner's box diameter or clearance.
-/
theorem rootFloor_le_owner (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    {value : Canonical} (inside : (box site parameter original regular).Contains value)
    (owner : Owner ((Paths.polynomial parameter).eval value)) :
    rootFloor site parameter ≤ (owner.certificate owner.parameterNonzero).apart.certificate.lowerSq := by
  rewrite [owner.certificate_lowerSq]
  have fullBound := cubic_lower site parameter original regular bound inside
  rewrite [Norm.Basic.normSq_eq_canonical] at fullBound
  exact Fraction.Order.Field.divide_mono
    (SquareRootSheets.capped_quarter_le_sampleNormLower fullBound)
    (by decide +kernel : (0 : Fraction.Rational) < 8)

/-- Every actual indexed approximation sample keeps the common chart root floor.

The supplied original owner may have an arbitrary inherited box. Its genuine
sample-norm law and the full-cubic region floor give the same lower bound
without refining or replacing that owner.
-/
theorem rootFloor_le_sample (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    {value : Canonical} (inside : (box site parameter original regular).Contains value)
    (owner : Owner ((Paths.polynomial parameter).eval value))
    (index : Nat) : rootFloor site parameter ≤
      Norm.Basic.normSq ((CertifiedSquareRoot.approximation owner.track).sample index) := by
  rewrite [Norm.Basic.normSq_eq_canonical]
  have lower := rootFloor_le_owner site parameter original regular bound inside owner
  rewrite [owner.certificate_lowerSq] at lower
  exact lower.trans ((Fraction.Order.Field.divide_le_self
    (SquareRootSheets.sampleLower_positive owner.parameterNonzero).le
    (by decide +kernel : (1 : Fraction.Rational) ≤ 8)).trans
      (CertifiedSquareRoot.sample_norm_lower owner.parameterNonzero owner.track index))

/-- Construct the original region-clearance container on the actual retained factor-clear spatial square. -/
@[expose] def clearance (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    RegionClearance (Paths.polynomial parameter) (box site parameter original regular) :=
  ⟨floor site parameter, floor_positive site parameter regular,
    fun _ inside => cubic_lower site parameter original regular bound inside⟩

/-- The retained original clearance exposes its exact full-cubic factor payment without recomputing it. -/
theorem clearance_bound (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    (clearance site parameter original regular bound).bound = floor site parameter := rfl

/-- The original depth-seven geometric allowance is the exact square of a one-hundred-twenty-eighth width. -/
theorem quarterRadius_seven : Approximation.Rational.Geometric.Basic.quarterRadius 1 7 =
    (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational) := by
  rewrite [Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  decide +kernel

/-- The actual depth-seven quarter payment uses at most twenty-five thirty-seconds of the retained sharp radius square.

The original spatial displacement, chart allowance and gap-radius bound
refer to the same quarter endpoints and retain their fixed depth seven.
-/
theorem quarter_target_distance_le (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (first last : Fraction.Rational)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    Norm.Basic.normSq
        ((point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base -
          (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) ≤
      (25 / 32) * radius site parameter ^ 2 := by
  have distance := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    (by decide +kernel) (by decide +kernel) last first
  have gapNonnegative := Norm.Basic.normSq_nonneg (halfGap site parameter)
  have small := Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 25 / 4)
      gapNonnegative)
  rewrite [quarterRadius_seven] at small
  calc
    _ ≤ ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) *
        (1 / Fraction.Cast.fromInt 16384) := distance.trans small
    _ = (25 / 32) * (Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 2048) := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct
        (Norm.Basic.normSq (halfGap site parameter)) (Fraction.Cast.fromInt 2048)]
      calc
        _ = Norm.Basic.normSq (halfGap site parameter) *
            ((25 / 4) * (1 / Fraction.Cast.fromInt 16384)) := by ring1
        _ = Norm.Basic.normSq (halfGap site parameter) *
            ((25 / 32) * (Fraction.Cast.fromInt 2048)⁻¹) :=
          congrArg (fun factor => Norm.Basic.normSq (halfGap site parameter) * factor)
            (by decide +kernel : (25 / 4 : Fraction.Rational) * (1 / Fraction.Cast.fromInt 16384) =
              (25 / 32) * (Fraction.Cast.fromInt 2048)⁻¹)
        _ = _ := by ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (radius_sq_lower site parameter) (by decide +kernel)

/-- A constant original-quarter chart payment puts its actual spatial endpoint in the factor-clear source square.

The original base-coordinate displacement budget is multiplied by the same
actual gap quadrance as the radius lower bound. Thus depth seven is sufficient
uniformly even when the regular parameter approaches the labelled collision.
-/
theorem quarter_target_inside (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site) (first last : Fraction.Rational)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    (box site parameter (Waist.direction quarter first) regular).Contains
      (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base := by
  apply contains_of_distance
  exact (quarter_target_distance_le site parameter quarter first last paid).trans
    ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (25 / 32 : Fraction.Rational) ≤ 1)
      (Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1))

/-- The paid endpoint has a radius-thirty-second neighbourhood strictly inside the original source square.

The original twenty-five thirty-seconds displacement fits a concentric
fifteen-sixteenths square. Its remaining coordinate margin pays the displayed
neighbourhood, without a new smallness premise or another clearance search.
-/
theorem quarter_target_neighborhood_strictInterior
    (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (regular : parameter ≠ criticalValue site) (first last : Fraction.Rational)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    Box.StrictInterior
      (Centered.Affine.centeredSquare
        (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base
        (radius site parameter / 32)
        (Fraction.Order.Field.div_pos_direct (radius_positive site parameter regular) (by decide +kernel)).le)
      (box site parameter (Waist.direction quarter first) regular) := by
  let source := (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base
  let target := (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base
  let selected := radius site parameter
  let inner := (15 / 16 : Fraction.Rational) * selected
  have positive : 0 < selected := radius_positive site parameter regular
  have innerNonnegative : 0 ≤ inner :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le
  have squared : (25 / 32) * selected ^ 2 ≤ inner ^ 2 := by
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (25 / 32 : Fraction.Rational) ≤ (15 / 16) ^ 2)
      (Arithmetic.sq_nonneg_direct selected)
    exact scaled.trans_eq (by dsimp only [inner]; ring1)
  have inside := Centered.centeredBox_contains_of_normSq_sub_le
    innerNonnegative ((quarter_target_distance_le site parameter quarter first last paid).trans squared)
  have margin : inner + selected / 32 < selected := by
    calc
      inner + selected / 32 = (31 / 32 : Fraction.Rational) * selected := by
        dsimp only [inner]
        rewrite [Fraction.Field.div_eq_mul_inv_direct selected 32]
        calc
          _ = ((15 / 16 : Fraction.Rational) + 32⁻¹) * selected := by ring1
          _ = _ := congrArg (fun factor => factor * selected)
            (by decide +kernel : (15 / 16 : Fraction.Rational) + 32⁻¹ = 31 / 32)
      _ < 1 * selected := Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide +kernel) positive
      _ = selected := by ring1
  have lower (coordinate current : Fraction.Rational) (bound : coordinate - inner ≤ current) :
      coordinate - selected < current - selected / 32 := by
    calc
      coordinate - selected < coordinate - (inner + selected / 32) :=
        Arithmetic.sub_lt_sub_left_direct margin coordinate
      _ = (coordinate - inner) - selected / 32 := by ring1
      _ ≤ current - selected / 32 := Arithmetic.sub_le_sub_right_direct bound _
  have upper (coordinate current : Fraction.Rational) (bound : current ≤ coordinate + inner) :
      current + selected / 32 < coordinate + selected := by
    calc
      current + selected / 32 ≤ (coordinate + inner) + selected / 32 :=
        Arithmetic.add_le_add_right_direct bound _
      _ = coordinate + (inner + selected / 32) := by ring1
      _ < coordinate + selected := Arithmetic.add_lt_add_left_direct margin coordinate
  exact ⟨lower source.re target.re inside.1, upper source.re target.re inside.2.1,
    lower source.im target.im inside.2.2.1, upper source.im target.im inside.2.2.2⟩

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance
