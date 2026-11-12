module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Factors
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
public import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Data.Gaussian.Power
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Existing covered trace diameters on the original sharp spatial box

The original known-root radius and original factor movement bounds give a
uniform full-cubic quadrance ceiling on the unchanged spatial square. Both
terms of the original trace lower-bound factory are thereby bounded by
sixteen radius squares. Its existing diameter request and the actual prepared
box already fit the full-product signed-sum payment; no new root acquisition
or changed request is needed for this diameter certificate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Branches.PreparedSheetContinuation

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : SquareRootContinuationChain.Owner
  ((unitPolynomial site).eval (Parameter.sourcePoint site parameter original).base)}
variable {source : Lift (Parameter.sourcePoint site parameter original) unit}

/-- The original source radius pays the half-gap quadrance through the retained parallel ordinate floor. -/
private theorem gap_norm_le (anchor : Parameter.Anchor source) :
    Norm.Basic.normSq (halfGap site parameter) ≤
      (Fraction.Cast.fromInt 128 / 9) * anchor.seed.separation.radius ^ 2 := by
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct anchor.radius_lower
    (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 128 / 9)
  calc
    _ = (Fraction.Cast.fromInt 128 / 9) * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) := by
      calc
        _ = ((Fraction.Cast.fromInt 128 / 9) * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) := by
          rewrite [show ((Fraction.Cast.fromInt 128 / 9) * (9 / 128) : Fraction.Rational) = 1 by decide +kernel]
          exact (Fraction.Field.one_mul _).symm
        _ = _ := by ring1
    _ ≤ _ := scaled

/-- The same original sharp square pays an eight-radius-fourth-power normalized-radicand displacement. -/
private theorem normalized_displacement_le (anchor : Parameter.Anchor source) {value : Canonical}
    (inside : (box site parameter original anchor.regular).Contains value) :
    Norm.Basic.normSq (normalizedRadicand site parameter value -
      (Parameter.sourcePoint site parameter original).ordinate ^ 2) ≤
      8 * (anchor.seed.separation.radius ^ 2) ^ 2 := by
  have movement := normalized_movement_le site parameter original anchor.regular inside
  have gaps := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) (gap_norm_le anchor) 2
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct gaps
    (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072)
  calc
    _ ≤ _ := movement
    _ ≤ _ := scaled
    _ = ((Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072) *
        (Fraction.Cast.fromInt 128 / 9) ^ 2) * (anchor.seed.separation.radius ^ 2) ^ 2 := by ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : ((Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072) *
        (Fraction.Cast.fromInt 128 / 9) ^ 2 : Fraction.Rational) ≤ 8)
      (Arithmetic.sq_nonneg_direct _)

/-- The actual normalized quadratic has its internally derived one-hundred-forty-four-radius-fourth-power ceiling. -/
private theorem normalized_normSq_le (anchor : Parameter.Anchor source) {value : Canonical}
    (inside : (box site parameter original anchor.regular).Contains value) :
    Norm.Basic.normSq (normalizedRadicand site parameter value) ≤
      144 * (anchor.seed.separation.radius ^ 2) ^ 2 := by
  have sourceNorm := Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _)
    anchor.seed.separation.norm_le 2
  have sourceSquare : Norm.Basic.normSq ((Parameter.sourcePoint site parameter original).ordinate ^ 2) ≤
      64 * (anchor.seed.separation.radius ^ 2) ^ 2 := by
    rewrite [Power.normSq_pow]
    exact sourceNorm.trans_eq (by ring1)
  have displacement := normalized_displacement_le anchor inside
  have identity : normalizedRadicand site parameter value =
      (Parameter.sourcePoint site parameter original).ordinate ^ 2 +
        (normalizedRadicand site parameter value - (Parameter.sourcePoint site parameter original).ordinate ^ 2) :=
    by ring1
  rewrite [identity]
  exact ((Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct sourceSquare displacement) (by decide +kernel))).trans_eq
        (by ring1)

/-- The remaining original affine radicand has quadrance at most three throughout the same admitted sharp square. -/
private theorem cofactor_normSq_le (anchor : Parameter.Anchor source) {value : Canonical}
    (inside : (box site parameter original anchor.regular).Contains value) :
    Norm.Basic.normSq ((unitPolynomial site).eval value) ≤ 3 := by
  have movement := cofactor_movement_half site parameter original anchor.regular anchor.bound inside
  have seed : Norm.Basic.normSq (UnitRoot.seed site ^ 2) = (1 : Fraction.Rational) := by
    rcases Data.Fin.Two.finTwo_cases site with zero | one
    · subst site
      decide +kernel
    · subst site
      decide +kernel
  have identity : (unitPolynomial site).eval value = UnitRoot.seed site ^ 2 -
      (UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value) := by ring1
  have bound := Norm.Bounds.normSq_sub_le_two (UnitRoot.seed site ^ 2)
    (UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value)
  rewrite [seed, ← identity] at bound
  exact (bound.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) movement)
    (by decide +kernel))).trans_eq (by decide +kernel : (2 * (1 + 1 / 2) : Fraction.Rational) = 3)

/-- The original full cubic on the retained physical source box has quadrance at most the square of thirty-two radii.

Both actual original factors use their original geometric movement bounds.
The known-root source square supplies the scale, independently of a queried
root process or its prepared presentation.
-/
theorem cubic_normSq_le (anchor : Parameter.Anchor source) {value : Canonical}
    (inside : (box site parameter original anchor.regular).Contains value) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval value) ≤
      (32 * anchor.seed.separation.radius ^ 2) ^ 2 := by
  have normalized := normalized_normSq_le anchor inside
  have cofactor := cofactor_normSq_le anchor inside
  rewrite [polynomial_centered]
  change Norm.Basic.normSq (normalizedRadicand site parameter value * (unitPolynomial site).eval value) ≤ _
  rewrite [Norm.Basic.normSq_mul]
  have product := Arithmetic.mul_le_mul_direct normalized cofactor
    (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct
      (by decide +kernel : (0 : Fraction.Rational) ≤ 144) (Arithmetic.sq_nonneg_direct _))
  calc
    _ ≤ (144 * (anchor.seed.separation.radius ^ 2) ^ 2) * 3 := product
    _ = 432 * (anchor.seed.separation.radius ^ 2) ^ 2 := by ring1
    _ ≤ (32 : Fraction.Rational) ^ 2 * (anchor.seed.separation.radius ^ 2) ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        ((Fraction.Cast.Order.natCast_le_direct (m := 432) (n := 1024) (by decide +kernel)).trans_eq (by
          rewrite [Fraction.Cast.natCast_eq_fromInt]
          decide +kernel))
        (Arithmetic.sq_nonneg_direct _)
    _ = _ := by ring1

/-- The original cubic's dominant absolute coordinate is bounded by the same thirty-two radius squares. -/
private theorem cubic_coordinate_le (anchor : Parameter.Anchor source) {value : Canonical}
    (inside : (box site parameter original anchor.regular).Contains value) :
    Riemann.Branches.SquareRootSheets.coordinateNormLower ((Paths.polynomial parameter).eval value) ≤
      32 * anchor.seed.separation.radius ^ 2 := by
  have coordinate := Riemann.Branches.SquareRootSheets.coordinateNormLower_sq_le_normSq
    ((Paths.polynomial parameter).eval value)
  rewrite [← Norm.Basic.normSq_eq_canonical] at coordinate
  exact Arithmetic.le_of_sq_le_sq_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.sq_nonneg_direct _))
    (coordinate.trans (cubic_normSq_le anchor inside))

variable {start finish : Canonical} {left right : Endpoint}

/-- The actual original segment trace lower bound is at most sixteen squares of the retained source radius.

The original segment clearance and its retained coordinate cover are bounded
at the same original parameter-zero spatial point. Capping the first square
bound at one gives the same linear scale in both size cases; neither the
cover nor any root preparation is rebuilt.
-/
theorem trace_lower_le (anchor : Parameter.Anchor source)
    (segment : ClearSegment (Paths.polynomial parameter) (box site parameter original anchor.regular) start finish)
    (within : segment.WithinAmbient) (budget : PreparedTraceBudget segment left right) :
    budget.lower ≤ 16 * anchor.seed.separation.radius ^ 2 := by
  have inside := segment.pointAt_contains within 0 (by decide +kernel)
  have norm := cubic_normSq_le anchor inside
  have region := segment.clearanceBound_le_eval_normSq (segment.pointAt_onCertifiedLine 0 (by decide +kernel))
  have clearance : segment.clearanceBound / 4 ≤ (16 * anchor.seed.separation.radius ^ 2) ^ 2 := by
    have scaled := Fraction.Order.Field.divide_mono (region.trans norm)
      (by decide +kernel : (0 : Fraction.Rational) < 4)
    exact scaled.trans_eq (by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = ((32 : Fraction.Rational) ^ 2 * (4 : Fraction.Rational)⁻¹) *
            (anchor.seed.separation.radius ^ 2) ^ 2 := by ring1
        _ = _ := by
          rewrite [show ((32 : Fraction.Rational) ^ 2 * (4 : Fraction.Rational)⁻¹) = 16 ^ 2 by decide +kernel]
          ring1)
  rewrite [budget.lower_eq]
  apply Fraction.Order.Basic.max_le
  · by_cases large : (1 : Fraction.Rational) ≤ 16 * anchor.seed.separation.radius ^ 2
    · exact (Fraction.Order.Basic.min_le_left _ _).trans large
    · have small := (Arithmetic.lt_of_not_ge_direct large).le
      have squared := Arithmetic.mul_le_mul_of_nonneg_left_direct small
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
          (Arithmetic.sq_nonneg_direct anchor.seed.separation.radius))
      have squaredBound : (16 * anchor.seed.separation.radius ^ 2) ^ 2 ≤
          16 * anchor.seed.separation.radius ^ 2 := by
        calc
          _ = (16 * anchor.seed.separation.radius ^ 2) * (16 * anchor.seed.separation.radius ^ 2) := by ring1
          _ ≤ (16 * anchor.seed.separation.radius ^ 2) * 1 := squared
          _ = _ := Fraction.Field.mul_one_direct _
      exact ((Fraction.Order.Basic.min_le_right _ _).trans clearance).trans
        squaredBound
  · have coordinate := budget.clearance.coordinate_le 0 (by decide +kernel)
    have upper := cubic_coordinate_le anchor inside
    have divided := Fraction.Order.Field.divide_mono (coordinate.trans upper)
      (by decide +kernel : (0 : Fraction.Rational) < 2)
    exact (Fraction.Order.Basic.min_le_right _ _).trans (divided.trans_eq (by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = ((32 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹) * anchor.seed.separation.radius ^ 2 := by ring1
        _ = _ := by
          rewrite [show ((32 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹) = 16 by decide +kernel]
          rfl))

/-- The existing original trace request already lies below one sixteenth of the full-product source floor. -/
theorem trace_diameter_le (anchor : Parameter.Anchor source)
    (segment : ClearSegment (Paths.polynomial parameter) (box site parameter original anchor.regular) start finish)
    (within : segment.WithinAmbient) (budget : PreparedTraceBudget segment left right) :
    budget.rootDiameter ≤ (anchor.seed.separation.radius ^ 2 / 4) / 16 := by
  rewrite [budget.rootDiameter_eq]
  have denominator : ((1024 : Nat) : Fraction.Rational) = (1024 : Fraction.Rational) := by
    rewrite [Fraction.Cast.natCast_eq_fromInt]
    decide +kernel
  have denominatorPositive :=
    (Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by decide +kernel)).trans_eq denominator
  have divided := Fraction.Order.Field.divide_mono (trace_lower_le anchor segment within budget)
    denominatorPositive
  exact divided.trans_eq (by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    calc
      _ = (16 * (1024 : Fraction.Rational)⁻¹) * anchor.seed.separation.radius ^ 2 := by ring1
      _ = ((4 : Fraction.Rational)⁻¹ * (16 : Fraction.Rational)⁻¹) * anchor.seed.separation.radius ^ 2 :=
        congrArg (fun factor => factor * anchor.seed.separation.radius ^ 2)
          (by decide +kernel)
      _ = _ := by ring1)

/-- Every actual cached prepared box satisfying the original trace request fit pays the same diameter certificate. -/
theorem prepared_diameter_le (anchor : Parameter.Anchor source)
    (segment : ClearSegment (Paths.polynomial parameter) (box site parameter original anchor.regular) start finish)
    (within : segment.WithinAmbient) (budget : PreparedTraceBudget segment left right)
    (current : Endpoint) (owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter)))
    (request : StepRequest) (cached : CachedSource segment current owner request)
    (requestFit : request.rootDiameter ≤ budget.rootDiameter) :
    cached.preparedOwner.track.initial.box.diagonalSq ≤ (anchor.seed.separation.radius ^ 2 / 4) / 16 := by
  rewrite [cached.preparedOwner_eq]
  exact (prepared_diagonal_lt segment current owner request).le.trans
    (requestFit.trans (trace_diameter_le anchor segment within budget))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance
