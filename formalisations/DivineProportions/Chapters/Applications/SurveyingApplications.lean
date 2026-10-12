module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Triple.Cleared.Int

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace SurveyingApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The exact surveying ratio is 58700 over 413 and lies strictly between 142.130 and 142.131. -/
theorem example_24_1 :
    587 * 100 = 58700 ∧
      142130 * 413 < 58700 * 1000 ∧
      58700 * 1000 < 142131 * 413 := by
  decide

open Purelib.Geometry.Trigonometry.Spread.Triple.Cleared in
/-- Exact integer tests bracket the selected small spread root and its two derived quadrances.

The root lies between 0.02790 and 0.02791; the retained cross products give the quadrance intervals 210.6 to 210.8 and
82.1 to 82.2. -/
theorem example_24_2_corrected_certificates :
    0 < Int.surveyingTripleRootNumerator 23520 38970 2790 100000 ∧
    Int.surveyingTripleRootNumerator 23520 38970 2791 100000 < 0 ∧
    2106 * 2791 * 10000 < 10 * 100000 * 2352 * 25 ∧
    10 * 100000 * 2352 * 25 < 2108 * 2790 * 10000 ∧
    821 * 1000 * 2791 < 10 * (3897 * 2352 * 25) ∧
    10 * (3897 * 2352 * 25) < 822 * 1000 * 2790 := by
  decide
end SurveyingApplications
end formalisations.DivineProportions.Chapters.Applications

end
