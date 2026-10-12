module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Enclosure
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalDistance

import Purelib.Approximation.CCL.Prefix.Sensitivity
import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.Comparison
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Stability between finite CCL prefix realizations

Any two explicit realizations of the same completed CCL prefix are close in
squared chordal distance.  A supplied probe sensitivity certificate turns
that geometric fact into direct pointwise, L1, powered-Lp, and tail bounds
between two complete finite realization families.  No limiting CCL value is
chosen.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Two probe realizations of the same retained prefixes have L1 distance at most the expected scaled cylinder spread.
-/
theorem prefixFamilyProbe_l1Distance_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  change distribution.expectation
      (fun certificate => Distance.rationalSeparation
        (probe (leftPoints certificate)) (probe (rightPoints certificate))) ≤
    distribution.expectation fun certificate =>
      factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  exact Approximation.CCL.Prefix.realized_probe_separation_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

section
open Purelib.Measure
/-- Two realizing probe expectations differ by at most the expected scaled cylinder spread. -/
theorem prefixFamilyProbe_expectation_separation_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_le_l1Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (prefixFamilyProbe_l1Distance_le distribution probe factor
        factorNonnegative sensitive leftPoints rightPoints leftRealizes
        rightRealizes)

/-- A realizing probe expectation lies within the retained expected radius of the original witness expectation. -/
theorem prefixFamilyProbe_expectation_separation_witness_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate => probe (points certificate))
        (CCL.Prefix.prefixFamilyProbeWitnessExpectation distribution probe) ≤
      CCL.Prefix.prefixFamilyProbeRadius distribution factor := by
  exact prefixFamilyProbe_expectation_separation_le distribution probe factor
    factorNonnegative sensitive points (fun certificate => certificate.witness)
    pointsRealize (fun atom member => atom.item.witnessRealizes)

end

/-- Powered Lp distance between two realizing probe families is bounded by the expected power of scaled spread. -/
theorem prefixFamilyProbe_poweredLpDistance_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.poweredLpDistance exponent
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ^ exponent := by
  change distribution.expectation
      (fun certificate => Distance.rationalSeparation
        (probe (leftPoints certificate))
        (probe (rightPoints certificate)) ^ exponent) ≤
    distribution.expectation fun certificate =>
      (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ^ exponent
  apply distribution.expectation_mono
  intro atom member
  have separationLe := Approximation.CCL.Prefix.realized_probe_separation_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive
  exact Fraction.Order.Arithmetic.pow_le_pow_direct
    (Distance.rationalSeparation_nonneg _ _) separationLe exponent

open Purelib.Measure in
/-- Separation probability is bounded by the expected powered spread divided by the positive threshold's power.

The natural exponent and both realizing families refer to the exact same original certificate distribution and retained
block prefixes. -/
theorem prefixFamilyProbe_separationProbability_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (exponent : Nat)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.probability
        (Measure.separationAtLeast threshold
          (fun certificate => probe (leftPoints certificate))
          (fun certificate => probe (rightPoints certificate))) ≤
      (distribution.expectation fun certificate =>
        (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ^ exponent) /
          threshold ^ exponent := by
  have markov :=
    distribution.probability_separationAtLeast_le_poweredLpDistance
      exponent threshold thresholdPositive
      (fun certificate => probe (leftPoints certificate))
      (fun certificate => probe (rightPoints certificate))
  have distanceBound := prefixFamilyProbe_poweredLpDistance_le distribution
    probe exponent factor factorNonnegative sensitive leftPoints rightPoints
    leftRealizes rightRealizes
  apply markov.trans
  change distribution.poweredLpDistance exponent
      (fun certificate => probe (leftPoints certificate))
      (fun certificate => probe (rightPoints certificate)) *
        (threshold ^ exponent)⁻¹ ≤
    distribution.expectation
        (fun certificate =>
          (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ^ exponent) *
      (threshold ^ exponent)⁻¹
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    distanceBound
    (Fraction.Order.Field.inv_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive exponent)).le

end

end Purelib.Measure.CCL.Prefix

end
