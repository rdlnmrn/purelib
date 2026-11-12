module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Paid factor movements in an original parallel spatial square

The original branch-factor square gives simultaneous budgets on normalized
quadratic and cofactor movements without changing any root owner. The actual
original target ordinate on a paid quarter edge remains in its source signed
square. These geometric payments support factor-channel continuation; they
do not identify the separate full-cubic covered-path finish owner.
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
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square
open Purelib.Geometry.Rational.Box.Square.Centered (Separation)

/-- The original normalized quadratic at a supplied physical spatial coordinate. -/
@[expose] def normalizedRadicand (site : Fin 2) (parameter value : Canonical) : Canonical :=
  coordinate site parameter value ^ 2 - smoothing site parameter

/-- The source conic coordinate is its actual original half-gap times the parallel base ellipse direction. -/
theorem source_coordinate (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    coordinate site parameter (Parameter.sourcePoint site parameter original).base =
      halfGap site parameter * baseDirection 2 original.value := by
  unfold Parameter.sourcePoint
  rewrite [coordinate, point_base]
  ring1

/-- A physical displacement changes the same original normalized quadratic by its exact linear and square terms. -/
theorem normalized_difference (site : Fin 2) (parameter : Canonical) (original : UnitVertex) (value : Canonical) :
    normalizedRadicand site parameter value - (Parameter.sourcePoint site parameter original).ordinate ^ 2 =
      (2 * (halfGap site parameter * baseDirection 2 original.value)) *
        (value - (Parameter.sourcePoint site parameter original).base) +
          (value - (Parameter.sourcePoint site parameter original).base) ^ 2 := by
  have sourceSquare := (Parameter.sourcePoint site parameter original).quadratic
  rewrite [← (Parameter.sourcePoint site parameter original).coordinate_base, source_coordinate] at sourceSquare
  have coordinateDiff : coordinate site parameter value =
      halfGap site parameter * baseDirection 2 original.value +
        (value - (Parameter.sourcePoint site parameter original).base) := by
    rewrite [← source_coordinate, coordinate, coordinate]
    ring1
  unfold normalizedRadicand
  rewrite [sourceSquare, coordinateDiff]
  ring1

/-- The original normalized quadratic's linear displacement coefficient retains its twenty-five-quarter gap budget. -/
theorem normalized_slope_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex) :
    Norm.Basic.normSq (2 * (halfGap site parameter * baseDirection 2 original.value)) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) := by
  have direction := baseDirection_normSq_le 2 original.value
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rewrite [original.unit, Fraction.Field.mul_one_direct] at direction
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    show Norm.Basic.normSq (2 : Canonical) = 4 by decide +kernel]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct direction (Norm.Basic.normSq_nonneg _))
    (by decide +kernel)).trans_eq (by
      calc
        _ = ((4 : Fraction.Rational) * (25 / 16)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
        _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
          (by decide +kernel : ((4 : Fraction.Rational) * (25 / 16)) = 25 / 4))

/-- Every physical point in the original sharp square pays a uniform normalized quadratic movement budget.

The original displacement is at most one five-hundred-twelfth of the gap
quadrance. Its linear and squared terms have respectively twenty-five over
two thousand forty-eight and one over two hundred sixty-two thousand one
hundred forty-four gap-fourth-power ceilings. The finite sum norm estimate
retains their computed original coefficient.
-/
theorem normalized_movement_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (normalizedRadicand site parameter value -
      (Parameter.sourcePoint site parameter original).ordinate ^ 2) ≤
        (Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072) *
          Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
  have distance := displacement_le site parameter original regular inside
  change Norm.Basic.normSq (value - (Parameter.sourcePoint site parameter original).base) ≤
    Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512 at distance
  have slope := normalized_slope_le site parameter original
  have linear := Arithmetic.mul_le_mul_direct slope distance
    (Norm.Basic.normSq_nonneg (value - (Parameter.sourcePoint site parameter original).base))
    (Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 25 / 4 by decide +kernel)
      (Norm.Basic.normSq_nonneg (halfGap site parameter)))
  have quadratic := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) distance 2
  rewrite [normalized_difference]
  have sum := Norm.Bounds.normSq_add_le_two
    ((2 * (halfGap site parameter * baseDirection 2 original.value)) *
      (value - (Parameter.sourcePoint site parameter original).base))
    ((value - (Parameter.sourcePoint site parameter original).base) ^ 2)
  rewrite [Norm.Basic.normSq_mul, Data.Gaussian.Power.normSq_pow] at sum
  calc
    _ ≤ _ := sum
    _ ≤ 2 * (((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) *
        (Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512) +
          (Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512) ^ 2) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct linear quadratic) (by decide +kernel)
    _ = _ := by
      simp only [Fraction.Field.div_eq_mul_inv_direct (Norm.Basic.normSq (halfGap site parameter))
        (Fraction.Cast.fromInt 512), -eq_self, -iff_self]
      calc
        _ = (2 * ((25 / 4) * (Fraction.Cast.fromInt 512)⁻¹ +
          ((Fraction.Cast.fromInt 512)⁻¹) ^ 2)) * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by ring1
        _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter) ^ 2)
          (by decide +kernel : (2 * ((25 / 4) * (Fraction.Cast.fromInt 512)⁻¹ +
            ((Fraction.Cast.fromInt 512)⁻¹) ^ 2) : Fraction.Rational) =
              Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072)

/-- Every point in the same original sharp square pays the existing unit-root reference movement allowance.

The original remaining factor is affine. The base displacement and retained
source branch-factor ceiling therefore give its exact common gap-quadrance
bound, independently of any target root or sampler choice.
-/
theorem cofactor_movement_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value) ≤
      (Fraction.Cast.fromInt 2625 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) := by
  have displacement := displacement_le site parameter original regular inside
  have source := Parameter.branchFactor_normSq_le site parameter original
  change Norm.Basic.normSq ((Parameter.sourcePoint site parameter original).base - criticalValue site) ≤
    (41 / 8) * Norm.Basic.normSq (halfGap site parameter) at source
  have difference : UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value = -(value - criticalValue site) :=
    UnitRoot.displacement site value
  rewrite [difference, Norm.Basic.normSq_neg]
  have split : value - criticalValue site = (value - (Parameter.sourcePoint site parameter original).base) +
    ((Parameter.sourcePoint site parameter original).base - criticalValue site) := by ring1
  rewrite [split]
  calc
    _ ≤ _ := Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512 +
        (41 / 8) * Norm.Basic.normSq (halfGap site parameter)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct displacement source) (by decide +kernel)
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = (2 * ((Fraction.Cast.fromInt 512)⁻¹ + 41 / 8)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
        _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
          (by decide +kernel : (2 * ((Fraction.Cast.fromInt 512)⁻¹ + 41 / 8) : Fraction.Rational) =
            Fraction.Cast.fromInt 2625 / Fraction.Cast.fromInt 256)

/-- The original sharper parameter admission pays one half of cofactor movement throughout the same spatial square. -/
theorem cofactor_movement_half (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value) ≤ (1 / 2 : Fraction.Rational) :=
  (cofactor_movement_le site parameter original regular inside).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (halfGap_bound site parameter bound)
      (by decide +kernel)).trans (by decide +kernel))

/-- An original paid parallel-quarter target ordinate remains in the source's identical retained signed square.

The source ordinate floor and the original separation radius give a common
nine-over-one-hundred-twenty-eight gap-quadrance radius floor. Depth-seven
original time movement is smaller than that floor, so the actual target
ordinate lies in the same original square without constructing a target seed.
-/
theorem quarter_ordinate_inside (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (first last : Fraction.Rational)
    (separation : Separation (Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    (Box.Square.Centered.Affine.centeredSquare
      (Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate separation.radius
      separation.positive.le).Contains
        (Parameter.sourcePoint site parameter (Waist.direction quarter last)).ordinate := by
  have lower := parallel_ordinate_lower site parameter (Waist.direction quarter first)
  have radiusLower := Fraction.Order.Field.divide_mono (lower.trans separation.norm_le)
    (by decide +kernel : (0 : Fraction.Rational) < 8)
  have movement := quarter_ordinate_distance_le site parameter 2 quarter (by decide +kernel)
    (by decide +kernel) (by decide +kernel) last first
  have paidMovement := Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 25 / 4)
      (Norm.Basic.normSq_nonneg (halfGap site parameter)))
  rewrite [quarterRadius_seven] at paidMovement
  have radiusPaid : ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) *
      (1 / Fraction.Cast.fromInt 16384) ≤ separation.radius ^ 2 := by
    calc
      _ = ((25 / 4) * (1 / Fraction.Cast.fromInt 16384)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
      _ ≤ (9 / 128) * Norm.Basic.normSq (halfGap site parameter) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)
      _ = ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) / 8 := by
        rewrite [Fraction.Field.div_eq_mul_inv_direct
          ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) 8]
        calc
          _ = ((9 / 16) * (8 : Fraction.Rational)⁻¹) * Norm.Basic.normSq (halfGap site parameter) :=
            congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
              (by decide +kernel : (9 / 128 : Fraction.Rational) = (9 / 16) * (8 : Fraction.Rational)⁻¹)
          _ = _ := by ring1
      _ ≤ (8 * separation.radius ^ 2) / 8 := radiusLower
      _ = separation.radius ^ 2 := by
        rewrite [Fraction.Field.div_eq_mul_inv_direct]
        calc
          _ = ((8 : Fraction.Rational) * (8 : Fraction.Rational)⁻¹) * separation.radius ^ 2 := by ring1
          _ = _ := by rewrite [show ((8 : Fraction.Rational) * (8 : Fraction.Rational)⁻¹) = 1 by decide +kernel]
                      exact Fraction.Field.one_mul _
  change (Box.Square.Centered.BoxTransport.centeredBox
    (Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate separation.radius
    separation.positive.le).Contains _
  exact Box.Square.Centered.centeredBox_contains_of_normSq_sub_le separation.positive.le
    (movement.trans (paidMovement.trans radiusPaid))

/-- Every physical point in the original source square retains its finite normalized-coordinate norm ceiling. -/
theorem coordinate_normSq_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {value : Canonical}
    (inside : (box site parameter original regular).Contains value) :
    Norm.Basic.normSq (coordinate site parameter value) ≤
      (Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) := by
  have direction := baseDirection_normSq_le 2 original.value
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rewrite [original.unit, Fraction.Field.mul_one_direct] at direction
  have sourceBound := Arithmetic.mul_le_mul_of_nonneg_left_direct direction
    (Norm.Basic.normSq_nonneg (halfGap site parameter))
  have distance := Clearance.displacement_le site parameter original regular inside
  have split : coordinate site parameter value =
      coordinate site parameter (Parameter.sourcePoint site parameter original).base +
        (value - (Parameter.sourcePoint site parameter original).base) := by
    rewrite [coordinate, coordinate]
    ring1
  rewrite [split, Clearance.source_coordinate]
  have sum := Norm.Bounds.normSq_add_le_two
    (coordinate site parameter (Parameter.sourcePoint site parameter original).base)
    (value - (Parameter.sourcePoint site parameter original).base)
  rewrite [Clearance.source_coordinate, Norm.Basic.normSq_mul] at sum
  calc
    _ ≤ _ := sum
    _ ≤ 2 * (Norm.Basic.normSq (halfGap site parameter) * (25 / 16) +
        Norm.Basic.normSq (halfGap site parameter) / Fraction.Cast.fromInt 512) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct sourceBound distance) (by decide +kernel)
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct (Norm.Basic.normSq (halfGap site parameter))
        (Fraction.Cast.fromInt 512)]
      calc
        _ = (2 * ((25 / 16) + (Fraction.Cast.fromInt 512)⁻¹)) * Norm.Basic.normSq (halfGap site parameter) := by ring1
        _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
          (by decide +kernel : (2 * ((25 / 16) + (Fraction.Cast.fromInt 512)⁻¹) : Fraction.Rational) =
            Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256)

/-- Independently retained normalized signed squares at the same physical point have a positive common sum floor.

Each exact source ordinate supplies its OWN original signed square and
physical factor-clear region. Their actual samples have the same positive
waist projection, even when the source directions differ or the point is
visited again. The existing coordinate ceiling converts that shared sign
into the explicit gap-quadrance sum floor; equality of squares is unused.
-/
theorem normalized_sum_lower (site : Fin 2) (parameter : Canonical)
    (firstDirection lastDirection : UnitVertex) (regular : parameter ≠ criticalValue site)
    (firstSeparation : Separation (point site parameter 2 firstDirection (by decide +kernel)).ordinate)
    (lastSeparation : Separation (point site parameter 2 lastDirection (by decide +kernel)).ordinate)
    {firstSample lastSample value : Canonical}
    (firstContained : (Centered.Affine.centeredSquare
      (point site parameter 2 firstDirection (by decide +kernel)).ordinate firstSeparation.radius
        firstSeparation.positive.le).Contains firstSample)
    (lastContained : (Centered.Affine.centeredSquare
      (point site parameter 2 lastDirection (by decide +kernel)).ordinate lastSeparation.radius
        lastSeparation.positive.le).Contains lastSample)
    (firstRegion : (box site parameter firstDirection regular).Contains value)
    (lastRegion : (box site parameter lastDirection regular).Contains value) :
    (1 / 4096 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq (firstSample + lastSample) := by
  let gapNorm := Norm.Basic.normSq (halfGap site parameter)
  let offset := coordinate site parameter value
  have positive : 0 < gapNorm := Norm.Basic.normSq_pos
    (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm)
  have firstDistance := displacement_le site parameter firstDirection regular firstRegion
  have lastDistance := displacement_le site parameter lastDirection regular lastRegion
  have firstPaid : Norm.Basic.normSq
      (value - (point site parameter 2 firstDirection (by decide +kernel)).base) ≤ gapNorm / 512 :=
    firstDistance.trans_eq (by
      rewrite [show (Fraction.Cast.fromInt 512 : Fraction.Rational) = 512 by decide +kernel]
      rfl)
  have lastPaid : Norm.Basic.normSq
      (value - (point site parameter 2 lastDirection (by decide +kernel)).base) ≤ gapNorm / 512 :=
    lastDistance.trans_eq (by
      rewrite [show (Fraction.Cast.fromInt 512 : Fraction.Rational) = 512 by decide +kernel]
      rfl)
  have firstProjection := parallel_signed_square_projection site parameter firstDirection
    firstSeparation firstContained firstPaid
  have lastProjection := parallel_signed_square_projection site parameter lastDirection
    lastSeparation lastContained lastPaid
  change (1 / 64 : Fraction.Rational) * gapNorm ≤ (firstSample * Basic.conj offset).re at firstProjection
  change (1 / 64 : Fraction.Rational) * gapNorm ≤ (lastSample * Basic.conj offset).re at lastProjection
  have sumProjection : (1 / 32 : Fraction.Rational) * gapNorm ≤
      ((firstSample + lastSample) * Basic.conj offset).re := by
    calc
      _ = ((1 / 64) + (1 / 64)) * gapNorm := congrArg (fun scalar => scalar * gapNorm)
        (by decide +kernel : (1 / 32 : Fraction.Rational) = (1 / 64) + (1 / 64))
      _ = (1 / 64) * gapNorm + (1 / 64) * gapNorm := by ring1
      _ ≤ (firstSample * Basic.conj offset).re + (lastSample * Basic.conj offset).re :=
        Arithmetic.add_le_add_direct firstProjection lastProjection
      _ = _ := by
        simp only [Basic.mul_re, Basic.conj, Basic.add_re, Basic.add_im]
        ring1
  have lowerSquare := Arithmetic.pow_le_pow_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le) sumProjection 2
  have offsetUpper : Norm.Basic.normSq offset ≤ 4 * gapNorm :=
    (coordinate_normSq_le site parameter firstDirection regular firstRegion).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide +kernel : (Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256 : Fraction.Rational) ≤ 4)
        positive.le)
  have dot := Norm.Bounds.projection_sq_le_normSq_mul (firstSample + lastSample) offset
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := 4 * gapNorm) _
    (Arithmetic.mul_pos_direct (by decide +kernel) positive)
  calc
    _ = ((1 / 4096) * 4) * gapNorm ^ 2 := by ring1
    _ = ((1 / 32 : Fraction.Rational) ^ 2) * gapNorm ^ 2 :=
      congrArg (fun scalar => scalar * gapNorm ^ 2)
        (by decide +kernel : ((1 / 4096) * 4 : Fraction.Rational) = (1 / 32) ^ 2)
    _ = ((1 / 32) * gapNorm) ^ 2 := by ring1
    _ ≤ ((firstSample + lastSample) * Basic.conj offset).re ^ 2 := lowerSquare
    _ = ((firstSample + lastSample).re * offset.re + (firstSample + lastSample).im * offset.im) ^ 2 := by
      simp only [Basic.mul_re, Basic.conj]
      ring1
    _ ≤ Norm.Basic.normSq (firstSample + lastSample) * Norm.Basic.normSq offset := dot
    _ ≤ Norm.Basic.normSq (firstSample + lastSample) * (4 * gapNorm) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct offsetUpper (Norm.Basic.normSq_nonneg _)

/-- Two actual points in the same original square pay the normalized quadratic's spatial variation budget. -/
theorem normalized_distance_le (site : Fin 2) (parameter : Canonical) (original : UnitVertex)
    (regular : parameter ≠ criticalValue site) {left right : Canonical}
    (leftInside : (box site parameter original regular).Contains left)
    (rightInside : (box site parameter original regular).Contains right) :
    Norm.Basic.normSq (Clearance.normalizedRadicand site parameter left -
      Clearance.normalizedRadicand site parameter right) ≤
        (Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter) *
          Norm.Basic.normSq (left - right) := by
  have leftBound := coordinate_normSq_le site parameter original regular leftInside
  have rightBound := coordinate_normSq_le site parameter original regular rightInside
  have sum := Norm.Bounds.normSq_add_le_two
    (coordinate site parameter left) (coordinate site parameter right)
  have sumBound : Norm.Basic.normSq (coordinate site parameter left + coordinate site parameter right) ≤
      (Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter) := by
    calc
      _ ≤ _ := sum
      _ ≤ 2 * ((Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) +
          (Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct leftBound rightBound) (by decide +kernel)
      _ = _ := by
        calc
          _ = (4 * (Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256)) *
              Norm.Basic.normSq (halfGap site parameter) := by ring1
          _ = _ := congrArg (fun factor => factor * Norm.Basic.normSq (halfGap site parameter))
            (by decide +kernel : (4 * (Fraction.Cast.fromInt 801 / Fraction.Cast.fromInt 256) : Fraction.Rational) =
              Fraction.Cast.fromInt 801 / 64)
  have difference : Clearance.normalizedRadicand site parameter left -
      Clearance.normalizedRadicand site parameter right =
        (left - right) * (coordinate site parameter left + coordinate site parameter right) := by
    unfold Clearance.normalizedRadicand
    rewrite [coordinate, coordinate]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (Norm.Basic.normSq_nonneg _)).trans_eq
    (Fraction.Field.mul_comm _ _)

/-- The original cofactor has exactly the same quadrance displacement as its physical spatial inputs. -/
theorem cofactor_distance (site : Fin 2) (left right : Canonical) :
    Norm.Basic.normSq ((unitPolynomial site).eval left - (unitPolynomial site).eval right) =
      Norm.Basic.normSq (left - right) := by
  rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
    Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
  exact congrArg Norm.Basic.normSq (by ring1)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance
