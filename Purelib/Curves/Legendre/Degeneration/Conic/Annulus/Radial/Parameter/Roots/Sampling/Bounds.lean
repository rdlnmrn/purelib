module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling
import Purelib.Data.Gaussian.Norm.Separation.Product
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Geometric clearance of the retained full-cubic observations

The same actual source comparison transfers a product-candidate floor to
each reading of the supplied source preparation. Target candidates use the
original stored factors directly. The unchanged cofactor certificate's
construction and the original spatial admission give a common numerical
floor across every regular parallel quarter. These claims concern the actual
paid observations; they do not enlarge or replace either preparation's
original apartness certificate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Rational
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}
variable {anchor : Anchor source} {increment : Canonical}
variable {step : Step anchor increment} {sourcePrepared : Division.Prepared source.value}

/-- The unchanged original cofactor certificate retains a uniform one-hundred-twenty-eighth apartness floor. -/
theorem cofactorFloor_lower (anchor : Anchor source) :
    (1 / 128 : Fraction.Rational) ≤ source.unitRoot.apart.certificate.lowerSq := by
  let cofactor := (unitPolynomial site).eval (sourcePoint site parameter original).base
  have spatial := point_inside site parameter 2 original
    (by decide +kernel) (by decide +kernel) (by decide +kernel) anchor.bound
  have radicandLower : (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq cofactor := unit_lower site spatial
  have residualLower : (1 / 16 : Fraction.Rational) ≤ SquareRootSheets.residualTarget cofactor := by
    unfold SquareRootSheets.residualTarget
    rewrite [← Norm.Basic.normSq_eq_canonical]
    change (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq cofactor * (4 : Fraction.Rational)⁻¹
    exact (show (1 / 16 : Fraction.Rational) = (1 / 4) * (4 : Fraction.Rational)⁻¹ by decide +kernel).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_right_direct radicandLower (by decide +kernel))
  have sampleLower : (1 / 16 : Fraction.Rational) ≤ SquareRootSheets.sampleNormLower cofactor :=
    (Fraction.Order.Basic.le_min (by decide +kernel) residualLower).trans (Fraction.Order.Basic.le_max_left _ _)
  rewrite [source.unitRoot_eq]
  change (1 / 128 : Fraction.Rational) ≤ SquareRootSheets.sampleNormLower cofactor / 8
  exact (show (1 / 128 : Fraction.Rational) = (1 / 16) * (8 : Fraction.Rational)⁻¹ by decide +kernel).trans_le
    (Arithmetic.mul_le_mul_of_nonneg_right_direct sampleLower (by decide +kernel))

/-- The exact normalized source centre pays the original signed square's radius-squared floor. -/
theorem source_ordinate_lower (anchor : Anchor source) :
    anchor.seed.separation.radius ^ 2 ≤ Norm.Basic.normSq (sourcePoint site parameter original).ordinate := by
  have inside := Box.Square.Centered.centeredSquare_contains_center (sourcePoint site parameter original).ordinate
    anchor.seed.separation.radius anchor.seed.separation.positive.le
  have lower := anchor.seed.separation.zero.margin_le_normSq_sub inside
  rewrite [anchor.seed.separation.zero_margin, Basic.sub_zero] at lower
  exact lower

/-- The original full-product sum floor has a common half-gap-dependent lower bound on every regular parallel point. -/
theorem sumFloor_uniform (anchor : Anchor source) :
    (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) ≤ sumFloor anchor := by
  have product := Arithmetic.mul_le_mul_direct (cofactorFloor_lower anchor) anchor.radius_lower
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
    source.unitRoot.apart.certificate.positive.le
  exact (show (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) =
      (1 / 128) * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) by
        have coefficient : ((1 / 128) * (9 / 128) : Fraction.Rational) = 9 / Fraction.Cast.fromInt 16384 := by
          decide +kernel
        calc
          _ = ((1 / 128) * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) :=
            congrArg (fun value => value * Norm.Basic.normSq (halfGap site parameter)) coefficient.symm
          _ = _ := Fraction.Field.mul_assoc _ _ _).trans_le product

/-- The quarter of the original full-product floor also has a common retained half-gap bound. -/
theorem preparedFloor_uniform (anchor : Anchor source) :
    (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) ≤ sumFloor anchor / 4 := by
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (sumFloor_uniform anchor) (by decide +kernel : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)
  exact (show (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) =
      ((9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter)) * (4 : Fraction.Rational)⁻¹ by
        have coefficient : ((9 / Fraction.Cast.fromInt 16384) * (4 : Fraction.Rational)⁻¹) =
            9 / Fraction.Cast.fromInt 65536 := by decide +kernel
        calc
          _ = ((9 / Fraction.Cast.fromInt 16384) * (4 : Fraction.Rational)⁻¹) *
              Norm.Basic.normSq (halfGap site parameter) :=
            congrArg (fun value => value * Norm.Basic.normSq (halfGap site parameter)) coefficient.symm
          _ = _ := by ring1).trans_le scaled

namespace Pair

variable {roots : Roots step sourcePrepared} {sourceAccuracy targetAccuracy : AccuracyRequest}

/-- The actual original product-side source witness retains its cofactor and exact-ordinate norm floor. -/
theorem original_normSq_lower (pair : Pair roots sourceAccuracy targetAccuracy) :
    sumFloor anchor ≤ Norm.Basic.normSq pair.originalReading := by
  rcases Roots.source_candidate_factors pair.original_reading_possible with ⟨cofactor, possible, equal⟩
  rewrite [equal, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_direct
    (source.unitRoot.apart.certificate.lower _ (source.unitRoot.value.name.process.possible_inside possible))
    (source_ordinate_lower anchor) (Arithmetic.pow_nonneg_direct anchor.seed.separation.positive.le 2)
    (Norm.Basic.normSq_nonneg _)

/-- Every prepared source reading inherits a quarter of the original product floor through its paid discrepancy. -/
theorem source_candidate_normSq_lower (pair : Pair roots sourceAccuracy targetAccuracy) {candidate : Canonical}
    (possible : pair.source.observation.Possible candidate) :
    sumFloor anchor / 4 ≤ Norm.Basic.normSq candidate := by
  have lower := Norm.Bounds.prepared_sum_lower pair.originalReading candidate 0
    (Sampling.sumFloor_positive anchor).le (by
      rewrite [Basic.add_zero]
      exact pair.original_normSq_lower) (pair.source_candidate_close possible)
  rewrite [Basic.add_zero] at lower
  exact lower

/-- Every actual source observation candidate pays the same half-gap floor throughout a retained regular quarter. -/
theorem source_candidate_uniform (pair : Pair roots sourceAccuracy targetAccuracy) {candidate : Canonical}
    (possible : pair.source.observation.Possible candidate) :
    (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) ≤ Norm.Basic.normSq candidate :=
  (preparedFloor_uniform anchor).trans (pair.source_candidate_normSq_lower possible)

/-- Every actual target observation candidate pays the original stored-factor floor on the same fixed point. -/
theorem target_candidate_uniform (pair : Pair roots sourceAccuracy targetAccuracy) {candidate : Canonical}
    (possible : pair.target.observation.Possible candidate) :
    (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) ≤ Norm.Basic.normSq candidate := by
  have original := possible
  rewrite [pair.target.observation_eq] at original
  have lower := roots.target_candidate_normSq_lower original
  have product := Arithmetic.mul_le_mul_of_nonneg_right_direct (cofactorFloor_lower anchor)
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 9 / 128)
      (Norm.Basic.normSq_nonneg (halfGap site parameter)))
  have coefficient : ((1 / 128) * (9 / 128) : Fraction.Rational) = 9 / Fraction.Cast.fromInt 16384 := by
    decide +kernel
  exact (show (9 / Fraction.Cast.fromInt 16384) * Norm.Basic.normSq (halfGap site parameter) =
      (1 / 128) * ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) by
        calc
          _ = ((1 / 128) * (9 / 128)) * Norm.Basic.normSq (halfGap site parameter) :=
            congrArg (fun value => value * Norm.Basic.normSq (halfGap site parameter)) coefficient.symm
          _ = _ := Fraction.Field.mul_assoc _ _ _).trans_le (product.trans lower)

/-- Every admitted pair of actual full-root readings has the same quarter-uniform geometric sum margin. -/
theorem sum_uniform (pair : Pair roots sourceAccuracy targetAccuracy) {first last : Canonical}
    (firstPossible : pair.source.observation.Possible first) (lastPossible : pair.target.observation.Possible last) :
    (9 / Fraction.Cast.fromInt 65536) * Norm.Basic.normSq (halfGap site parameter) ≤ Norm.Basic.normSq (first + last) :=
  (preparedFloor_uniform anchor).trans (pair.sum_normSq_lower firstPossible lastPossible)

end Pair

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling
