module
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Event.RationalOrder

section
@[expose] public section

/-!
# Uniform stability of constructive finite quantiles

Finite lower quantiles are stable under a displayed uniform rational
perturbation of the source observable.  The proof compares the two executable
cumulative events atom by atom and applies the exact finite generalized-inverse
law.  No infimum, limiting distribution, or completed metric space occurs.
-/

namespace Purelib.Measure

namespace Distribution
namespace EvaluationEquivalent

open Purelib.Data.Rat in
/-- Evaluation-equivalent rational distributions have equal cumulative probabilities at every supplied cut. -/
theorem cumulative_eq
    {left right : Distribution Fraction.Rational}
    (equivalent : EvaluationEquivalent left right)
    (cut : Fraction.Rational) :
    left.cumulative cut = right.cumulative cut :=
  equivalent.probability_eq (atMostEvent cut)
end EvaluationEquivalent
end Distribution

end Purelib.Measure

end
