module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Raw collar heights from original signed channel comparisons

The actual retained height stream is compared through its pointwise sample
law. One original name comparison supplies both finite floors; no second
sampler, radius stream, phase or source channel is constructed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)

/-- The finite squared-distance amplification for normalized quadrance near one exact coordinate. -/
private def radialCost (range : Interval) (value : Canonical) : Fraction.Rational :=
  (2 * (2 * (1 + Norm.Basic.normSq value) + Norm.Basic.normSq value)) * (range.width⁻¹) ^ 2

/-- The displayed radial amplification is nonnegative, including a zero-width interval. -/
private theorem radialCost_nonneg (range : Interval) (value : Canonical) : 0 ≤ radialCost range value := by
  have first := add_pos_of_pos_of_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) < 1)
    (Norm.Basic.normSq_nonneg value)
  have twice := mul_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 2) first
  have total := add_pos_of_pos_of_nonneg_direct twice (Norm.Basic.normSq_nonneg value)
  exact mul_nonneg_direct
    (mul_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 2) total).le
    (sq_nonneg_direct _)

/-- A unit squared-distance neighborhood bounds the normalized quadrance error by its finite amplification. -/
private theorem radial_error_le (range : Interval) (candidate value : Canonical)
    (near : Norm.Basic.normSq (candidate - value) ≤ 1) :
    Norm.Basic.normSq
      ((⟨(Norm.Basic.normSq candidate - range.lower) / range.width, 0⟩ : Canonical) -
        ⟨(Norm.Basic.normSq value - range.lower) / range.width, 0⟩) ≤
      radialCost range value * Norm.Basic.normSq (candidate - value) := by
  have candidateBound : Norm.Basic.normSq candidate ≤ 2 * (1 + Norm.Basic.normSq value) :=
    ((congrArg Norm.Basic.normSq (show candidate = (candidate - value) + value by ring1)).trans_le
      (Norm.Bounds.normSq_add_le_two (candidate - value) value)).trans
        (mul_le_mul_of_nonneg_left_direct
          (add_le_add_direct near (Fraction.Order.Basic.le_refl _))
          (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  have coefficient := mul_le_mul_of_nonneg_left_direct
    (add_le_add_direct candidateBound (Fraction.Order.Basic.le_refl (Norm.Basic.normSq value)))
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have scalar : Norm.Basic.normSq
      ((⟨(Norm.Basic.normSq candidate - range.lower) / range.width, 0⟩ : Canonical) -
        ⟨(Norm.Basic.normSq value - range.lower) / range.width, 0⟩) =
      (Norm.Basic.normSq candidate - Norm.Basic.normSq value) ^ 2 * (range.width⁻¹) ^ 2 := by
    change ((Norm.Basic.normSq candidate - range.lower) / range.width -
      (Norm.Basic.normSq value - range.lower) / range.width) ^ 2 + (0 - 0 : Fraction.Rational) ^ 2 = _
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring1
  have squared := normSq_difference_sq_le_two_mul candidate value
  have rearrange : 2 * Norm.Basic.normSq (candidate - value) *
      (Norm.Basic.normSq candidate + Norm.Basic.normSq value) =
      Norm.Basic.normSq (candidate - value) *
        (2 * (Norm.Basic.normSq candidate + Norm.Basic.normSq value)) := by ring1
  have unscaled : (Norm.Basic.normSq candidate - Norm.Basic.normSq value) ^ 2 ≤
      Norm.Basic.normSq (candidate - value) *
        (2 * (2 * (1 + Norm.Basic.normSq value) + Norm.Basic.normSq value)) :=
    (squared.trans_eq rearrange).trans
      (mul_le_mul_of_nonneg_left_direct coefficient (Norm.Basic.normSq_nonneg (candidate - value)))
  exact scalar.trans_le
    ((mul_le_mul_of_nonneg_right_direct unscaled (sq_nonneg_direct _)).trans_eq (by
      unfold radialCost
      ring1))

/-- Normalize the actual retained radius stream through one given original signed channel comparison.

Each request uses the smaller of one and the target divided by one plus
the displayed quadrance amplification. The original comparison executes
once and supplies both independent floors and every later sample bound.
The height input and its sample law retain the original numerical owner.
-/
def radial_to_exact (name : Named) (range : Interval) (height : GeometricApproximation) (value : Canonical)
    (sampleLaw : ∀ index, height.sample index =
      (⟨(Norm.Basic.normSq ((Sampling.approximation name).sample index) - range.lower) / range.width, 0⟩ : Canonical))
    (original : NamedEquivalent name (Named.exact value)) :
    Equivalent height.toApproximation
      (Sequence.Constant.constantApproximation
        (⟨(Norm.Basic.normSq value - range.lower) / range.width, 0⟩ : Canonical)) where
  compare firstStart lastStart target positive := by
    let cost := radialCost range value
    have nonnegative : 0 ≤ cost := radialCost_nonneg range value
    let tolerance := min 1 (target / (cost + 1))
    have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min
      (by decide +kernel : (0 : Fraction.Rational) < 1)
      (Fraction.Order.Field.div_pos_direct positive
        (add_pos_of_nonneg_of_pos_direct nonnegative (by decide +kernel : (0 : Fraction.Rational) < 1)))
    let compared := original.compare firstStart lastStart tolerance tolerancePositive
    exact
      { leftIndex := compared.leftIndex
        rightIndex := compared.rightIndex
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have close := compared.close firstAfter lastAfter
          rewrite [Sequence.Name.Exact.exactNamedSample value lastLater] at close
          have near := close.le.trans (Fraction.Order.Basic.min_le_left 1 (target / (cost + 1)))
          have error := radial_error_le range ((Sampling.approximation name).sample firstLater) value near
          change Norm.Basic.normSq (height.sample firstLater -
            (⟨(Norm.Basic.normSq value - range.lower) / range.width, 0⟩ : Canonical)) < target
          rewrite [sampleLaw firstLater]
          exact (error.trans (mul_le_mul_of_nonneg_left_direct close.le nonnegative)).trans_lt
            (Fraction.Order.Field.mul_min_one_div_lt nonnegative positive) }

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Profile

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    (profile : Profile channels bound)

/-- The same actual raw profile inherits its exact radial value from the given original plus-channel comparison. -/
def raw_to_exact (value : Canonical) (original : NamedEquivalent channels.plus.name (Named.exact value)) :
    Equivalent profile.1.val.toApproximation
      (Sequence.Constant.constantApproximation (⟨(Norm.Basic.normSq value - (Collar.range site parameter bound).lower) /
        (Collar.range site parameter bound).width, 0⟩ : Canonical)) :=
  Collar.radial_to_exact channels.plus.name (Collar.range site parameter bound) profile.1.val value
    (fun index => (congrArg (fun height : GeometricApproximation => height.sample index) profile.1.property).trans
      ((Collar.radial_sample_eq (Collar.range site parameter bound) (GeometricApproximation.ofNamed channels.plus.name)
        index).trans (congrArg (fun sample : Canonical =>
          (⟨(Norm.Basic.normSq sample - (Collar.range site parameter bound).lower) /
            (Collar.range site parameter bound).width, 0⟩ : Canonical))
          (GeometricApproximation.ofNamed_sample channels.plus.name index)))) original

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Profile

end
