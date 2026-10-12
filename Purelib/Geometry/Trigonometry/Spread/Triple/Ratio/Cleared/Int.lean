module
public import Purelib.Algebra.Field.ExplicitField
import Init.Data.Int.Basic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Ratio.Cleared.Int

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The general denominator-cleared pair of equations used by the Spread from ratio theorem. `sign=1` selects the `+2r`
denominator and `sign=-1` selects the other finite candidate. -/
def clearedSpreadFromRatioCandidate
    (aNumerator aDenominator spreadNumerator spreadDenominator
      rootNumerator rootDenominator
      xNumerator xDenominator yNumerator yDenominator sign : Int) : Prop :=
  aDenominator * xNumerator * yDenominator =
      aNumerator * yNumerator * xDenominator ∧
    yNumerator * spreadDenominator *
        (aNumerator * rootDenominator +
          aDenominator * rootDenominator +
          sign * 2 * rootNumerator * aDenominator) =
      yDenominator * spreadNumerator * aDenominator * rootDenominator
end
end Purelib.Geometry.Trigonometry.Spread.Triple.Ratio.Cleared.Int

end
