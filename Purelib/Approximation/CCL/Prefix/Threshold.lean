module
import Purelib.Approximation.CCL.Cylinder.Spread
public import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Classified.Threshold
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.CCL

open Purelib.Approximation.Rational

open Purelib.Data.CCL.Encoding

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Progressive threshold probabilities from finite CCL prefixes

A lower-threshold event can be decided after one finite prefix request when
each displayed witness probe has an explicit positive rational margin from
the threshold.  The requested completed-block count makes every current
probe enclosure narrower than that margin, so every finite row is classified
and the resulting probability enclosure has width zero.  No eventual CCL
point or infinite refinement sequence is introduced.
-/

namespace Purelib.Approximation.CCL.Prefix

/-- A sufficiently narrow completed-prefix probe enclosure is resolved by an explicit rational margin separating its
witness value from the threshold. -/
theorem completedPrefixProbeBound_thresholdResolved_of_margin
    {blocks : List Data.CCL.Encoding.Block} (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated :
      threshold + margin ≤ probe witness ∨
        probe witness + margin ≤ threshold)
    (enough : Budget.requiredProbeBlockCount margin factor ≤ blocks.length) :
    Measure.ThresholdResolved
      (Prefix.completedPrefixProbeBound blocks witness witnessRealizes probe factor
        factorPositive.le sensitive)
      threshold := by
  let radius := factor * Cylinder.cylinderSpread blocks
  have radiusNonnegative : 0 ≤ radius :=
    Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
      (Cylinder.cylinderSpread_nonneg blocks)
  have widthSmall := Prefix.completedPrefixProbeBound_width_lt_requested
    witness witnessRealizes probe factor factorPositive sensitive
    margin marginPositive enough
  have radiusSmall : radius < margin := by
    calc
      radius = radius + 0 := by ring1
      _ ≤ radius + radius := add_le_add le_rfl radiusNonnegative
      _ = 2 * radius := by ring1
      _ = (Prefix.completedPrefixProbeBound blocks witness witnessRealizes probe
          factor factorPositive.le sensitive).width := by
        rw [Prefix.completedPrefixProbeBound_width]
      _ < margin := widthSmall
  change threshold ≤ probe witness - radius ∨
    probe witness + radius < threshold
  rcases separated with inside | outside
  · apply Or.inl
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct
      ((Fraction.Order.Arithmetic.add_lt_add_left_direct
        radiusSmall threshold).le.trans inside) radius
    calc
      threshold = (threshold + radius) - radius := by ring1
      _ ≤ probe witness - radius := shifted
  · apply Or.inr
    exact (Fraction.Order.Arithmetic.add_lt_add_left_direct
      radiusSmall (probe witness)).trans_le outside

end Purelib.Approximation.CCL.Prefix

end
