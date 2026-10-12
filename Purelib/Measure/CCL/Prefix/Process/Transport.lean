module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.CCL.Prefix.Sensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
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
namespace PrefixFamilyProcess

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The original law's coupling of two current-state probe realizations costs at most the expected scaled cylinder
spread. -/
theorem probeLawCoupling_transportCost_le {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (rightPoints atom.item)) :
    (Coupling.Law.probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        Distance.rationalSeparation ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item) := by
  rw [Coupling.Law.probeLawCoupling_transportCost]
  change distribution.expectation (fun item =>
      Distance.rationalSeparation
        (probe (leftPoints item)) (probe (rightPoints item))) ≤ _
  apply distribution.expectation_mono
  intro atom member
  exact Approximation.CCL.Prefix.realized_probe_separation_le (leftRealizes atom member)
    (rightRealizes atom member) probe factor factorNonnegative sensitive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- A block request at half epsilon makes the retained probe coupling's separation cost strictly smaller than epsilon.

Both families realize the same requested prefix state, and the sensitivity factor and requested tolerance are positive.
-/
theorem request_probeLawCoupling_transportCost_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (process.request state
            (Budget.requiredProbeBlockCount (epsilon / 2) factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          (process.request state
            (Budget.requiredProbeBlockCount (epsilon / 2) factor)) atom.item)
        (rightPoints atom.item)) :
    (Coupling.Law.probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        Distance.rationalSeparation < epsilon := by
  let requested := process.request state
    (Budget.requiredProbeBlockCount (epsilon / 2) factor)
  have transportLe := (probeLawCoupling_transportCost_le process) distribution
    probe factor factorPositive.le sensitive requested leftPoints rightPoints
    leftRealizes rightRealizes
  have radiusLeHalf : distribution.expectation (fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested item)) ≤
      epsilon / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested item)) ≤
          distribution.expectation (fun _ => epsilon / 2) := by
        apply distribution.expectation_mono
        intro atom member
        have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
          (process.witness atom.item) (process.realizes requested atom.item)
          probe factor factorPositive sensitive (epsilon / 2)
          (Fraction.Order.Field.div_pos_direct positive (by decide))
          (process.request_length state
            (Budget.requiredProbeBlockCount (epsilon / 2) factor) atom.item)
        have radiusNonnegative : 0 ≤
            factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
            (Approximation.CCL.Cylinder.cylinderSpread_nonneg _)
        calc
          factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested atom.item) ≤
              2 * (factor * Approximation.CCL.Cylinder.cylinderSpread
                (process.blocks requested atom.item)) := by
            calc
              _ = 0 + factor * Approximation.CCL.Cylinder.cylinderSpread
                    (process.blocks requested atom.item) := by ring1
              _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread
                      (process.blocks requested atom.item) +
                    factor * Approximation.CCL.Cylinder.cylinderSpread
                      (process.blocks requested atom.item) :=
                Fraction.Order.Arithmetic.add_le_add_direct
                  radiusNonnegative le_rfl
              _ = _ := by ring1
          _ = (Approximation.CCL.Prefix.completedPrefixProbeBound
              (process.blocks requested atom.item) (process.witness atom.item)
              (process.realizes requested atom.item) probe factor
              factorPositive.le sensitive).width := by
            rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width]
          _ ≤ epsilon / 2 := widthSmall.le
      _ = epsilon / 2 := distribution.expectation_constant _
  exact transportLe.trans_lt
    (radiusLeHalf.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self positive))

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
