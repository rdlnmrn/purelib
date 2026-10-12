module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.Prefix.Stability
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Lp.L1
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Couple two probe laws by pairing their values at each original certificate occurrence.

The construction retains the exact source distribution and both point families as its pushforward marginals. -/
def prefixFamilyProbeLawCoupling
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine) :
    Measure.LawCoupling
      (distribution.map fun certificate => probe (leftPoints certificate))
      (distribution.map fun certificate => probe (rightPoints certificate)) :=
  Coupling.Law.probeLawCoupling distribution probe leftPoints rightPoints

/-- The retained coupling's separation cost is the original law's L1 distance between the two probe families. -/
theorem prefixFamilyProbeLawCoupling_transportCost
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine) :
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost Distance.rationalSeparation =
      distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) := by
  unfold prefixFamilyProbeLawCoupling
  exact Coupling.Law.probeLawCoupling_transportCost distribution probe leftPoints
    rightPoints

/-- For two realizations, the retained coupling's cost is at most expected sensitivity-scaled cylinder spread. -/
theorem prefixFamilyProbeLawCoupling_transportCost_le
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
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost Distance.rationalSeparation ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  rw [prefixFamilyProbeLawCoupling_transportCost]
  exact CCL.Prefix.prefixFamilyProbe_l1Distance_le distribution probe factor
    factorNonnegative sensitive leftPoints rightPoints leftRealizes
    rightRealizes

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Enough retained blocks at the half-epsilon request make the probe coupling's cost strictly smaller than epsilon. -/
theorem prefixFamilyProbeLawCoupling_transportCost_lt_requested
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (rightPoints atom.item))
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (epsilon / 2) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbeLawCoupling distribution probe leftPoints rightPoints
      ).transportCost Distance.rationalSeparation < epsilon := by
  have transportLe := prefixFamilyProbeLawCoupling_transportCost_le
    distribution probe factor factorPositive.le sensitive leftPoints
    rightPoints leftRealizes rightRealizes
  have radiusLeHalf : distribution.expectation (fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤ epsilon / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon / 2) := by
        apply distribution.expectation_mono
        intro atom member
        have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
          atom.item.witness atom.item.witnessRealizes probe factor factorPositive
          sensitive (epsilon / 2)
          (Fraction.Order.Field.div_pos_direct positive (by decide))
          (enough atom member)
        have radiusNonnegative : 0 ≤
            factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
          Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
            (Approximation.CCL.Cylinder.cylinderSpread_nonneg atom.item.blocks)
        calc
          factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks ≤
              2 * (factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks) := by
            calc
              _ = 0 + factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks := by ring1
              _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks +
                    factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
                Fraction.Order.Arithmetic.add_le_add_direct
                  radiusNonnegative le_rfl
              _ = _ := by ring1
          _ = (Approximation.CCL.Prefix.completedPrefixProbeBound atom.item.blocks atom.item.witness
              atom.item.witnessRealizes probe factor factorPositive.le
              sensitive).width := by
            rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width]
          _ ≤ epsilon / 2 := widthSmall.le
      _ = epsilon / 2 := distribution.expectation_constant _
  exact transportLe.trans_lt
    (radiusLeHalf.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self positive))

end Purelib.Measure.CCL.Prefix

end
