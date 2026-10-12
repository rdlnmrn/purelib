module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Convolution.Basic
import Purelib.Measure.Distribution.Convolution.Cumulative
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Kolmogorov.Equivalence
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- Convolving two rational laws with the same retained left noise law cannot increase their Kolmogorov distance. -/
theorem kolmogorovDistance_convolve_left_le
    (noise left right : Measure.Distribution Fraction.Rational) :
    (noise.convolve left).kolmogorovDistance
        (noise.convolve right) ≤
      left.kolmogorovDistance right := by
  apply (noise.convolve left).kolmogorovDistance_le
    (noise.convolve right) (left.kolmogorovDistance right)
      (left.kolmogorovDistance_nonnegative right)
  intro cut
  rw [noise.cumulative_convolve left cut,
    noise.cumulative_convolve right cut]
  calc
    Distance.rationalSeparation
        (noise.expectation fun noiseValue =>
          left.cumulative (cut - noiseValue))
        (noise.expectation fun noiseValue =>
          right.cumulative (cut - noiseValue)) ≤
      noise.l1Distance
        (fun noiseValue => left.cumulative (cut - noiseValue))
        (fun noiseValue => right.cumulative (cut - noiseValue)) :=
      noise.expectation_separation_le_l1Distance _ _
    _ ≤ left.kolmogorovDistance right := by
      unfold l1Distance
      calc
        noise.expectation (fun noiseValue => Distance.rationalSeparation
            (left.cumulative (cut - noiseValue))
            (right.cumulative (cut - noiseValue))) ≤
          noise.expectation (fun _ => left.kolmogorovDistance right) := by
            apply noise.expectation_mono
            intro atom member
            exact left.cumulative_separation_leKolmogorovDistance right
              (cut - atom.item)
        _ = left.kolmogorovDistance right :=
          noise.expectation_constant _

/-- Convolving two rational laws with the same retained right noise law cannot increase their Kolmogorov distance. -/
theorem kolmogorovDistance_convolve_right_le
    (left right noise : Measure.Distribution Fraction.Rational) :
    (left.convolve noise).kolmogorovDistance
        (right.convolve noise) ≤
      left.kolmogorovDistance right := by
  calc
    (left.convolve noise).kolmogorovDistance
          (right.convolve noise) =
        (noise.convolve left).kolmogorovDistance
          (noise.convolve right) :=
      (left.convolve_comm_evaluationEquivalent noise)
        |>.kolmogorovDistance_eq
          (right.convolve_comm_evaluationEquivalent noise)
    _ ≤ left.kolmogorovDistance right :=
      noise.kolmogorovDistance_convolve_left_le left right
end Distribution

end Purelib.Measure

end
