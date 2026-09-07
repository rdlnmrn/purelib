import CCL.Measure.PrefixProfile
import FiniteMeasure.NaturalLp

/-!
# Stability between finite CCL prefix realizations

Any two explicit realizations of the same completed CCL prefix are close in
squared chordal distance.  A supplied probe sensitivity certificate turns
that geometric fact into direct pointwise, L1, powered-Lp, and tail bounds
between two complete finite realization families.  No limiting CCL value is
chosen.
-/

namespace CCL.FiniteMeasure

/-- Two explicit realizations of one finite prefix have probe separation at
most the sensitivity-scaled cylinder spread. -/
theorem realized_probe_separation_le
    {blocks : List Block} {leftPoint rightPoint : Proj}
    (leftRealizes : CCL.Cylinder.Realizes blocks leftPoint)
    (rightRealizes : CCL.Cylinder.Realizes blocks rightPoint)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.rationalSeparation
        (probe leftPoint) (probe rightPoint) ≤
      factor * cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.Cylinder.Realizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)

/-- The exact finite L1 distance between any two realization families is at
most the expected sensitivity-scaled prefix spread. -/
theorem prefixFamilyProbe_l1Distance_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  change distribution.expectation
      (fun certificate => _root_.FiniteMeasure.rationalSeparation
        (probe (leftPoints certificate)) (probe (rightPoints certificate))) ≤
    distribution.expectation fun certificate =>
      factor * cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  exact realized_probe_separation_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

/-- Expectations of any two admitted realization families differ by at most
the exact expected sensitivity-scaled prefix spread. -/
theorem prefixFamilyProbe_expectation_separation_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_le_l1Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (prefixFamilyProbe_l1Distance_le distribution probe factor
        factorNonnegative sensitive leftPoints rightPoints leftRealizes
        rightRealizes)

/-- In particular, the displayed finite witness expectation approximates
every admitted realization family's exact expectation within the explicit
expected prefix radius. -/
theorem prefixFamilyProbe_expectation_separation_witness_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate => probe (points certificate))
        (prefixFamilyProbeWitnessExpectation distribution probe) ≤
      prefixFamilyProbeRadius distribution factor := by
  exact prefixFamilyProbe_expectation_separation_le distribution probe factor
    factorNonnegative sensitive points (fun certificate => certificate.witness)
    pointsRealize (fun atom member => atom.item.witnessRealizes)

/-- Natural-powered Lp distance between any two realization families is
bounded by the exact expected powered cylinder budget. -/
theorem prefixFamilyProbe_poweredLpDistance_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.poweredLpDistance exponent
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        (factor * cylinderSpread certificate.blocks) ^ exponent := by
  change distribution.expectation
      (fun certificate => _root_.FiniteMeasure.rationalSeparation
        (probe (leftPoints certificate))
        (probe (rightPoints certificate)) ^ exponent) ≤
    distribution.expectation fun certificate =>
      (factor * cylinderSpread certificate.blocks) ^ exponent
  apply distribution.expectation_mono
  intro atom member
  have separationLe := realized_probe_separation_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive
  exact RFAP.ConstructiveFraction.pow_le_pow_direct
    (_root_.FiniteMeasure.rationalSeparation_nonneg _ _) separationLe exponent

/-- The probability that two admitted realization families differ by a
displayed positive probe threshold is bounded by their exact powered prefix
budget divided by the threshold power. -/
theorem prefixFamilyProbe_separationProbability_le
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun certificate => probe (leftPoints certificate))
          (fun certificate => probe (rightPoints certificate))) ≤
      (distribution.expectation fun certificate =>
        (factor * cylinderSpread certificate.blocks) ^ exponent) /
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
          (factor * cylinderSpread certificate.blocks) ^ exponent) *
      (threshold ^ exponent)⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    distanceBound
    (RFAP.ConstructiveFraction.inv_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive exponent)).le

end CCL.FiniteMeasure
