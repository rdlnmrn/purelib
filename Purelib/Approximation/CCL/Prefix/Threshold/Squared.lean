module
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Power
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Event.RationalOrder

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Geometry.Projective.Line (GaussianLine)

open Purelib.Approximation.CCL

open Purelib.CCL.Measure

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Measure

section
public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.Approximation.CCL.Prefix

/-- A squared-sensitive probe has the same lower-threshold classification at a canonical cylinder witness and any
realization once the squared budget is strictly below the displayed margin square. -/
theorem realizedSquaredProbe_atLeastDecision_eq_of_margin
    {blocks : List Data.CCL.Encoding.Block} {witness point : GaussianLine}
    (witnessRealizes : Cylinder.Basic.Realizes blocks witness)
    (pointRealizes : Cylinder.Basic.Realizes blocks point)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : threshold + margin ≤ probe witness ∨
      probe witness + margin ≤ threshold)
    (budgetSmall : factor * Cylinder.cylinderSpread blocks < margin ^ 2) :
    decide (threshold ≤ probe point) =
      decide (threshold ≤ probe witness) := by
  have squareSmall := (Prefix.realized_probe_separation_sq_le pointRealizes
    witnessRealizes probe factor factorNonnegative sensitive).trans_lt
      budgetSmall
  exact Event.atLeastDecision_eq_of_margin marginPositive
    (Purelib.Data.Rat.Distance.rationalSeparation_lt_of_sq_lt_sq marginPositive squareSmall) separated

/-- Projectively rescaled encoder traces have the same margin-stable threshold classification. -/
theorem projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
    {blocks : List Data.CCL.Encoding.Block} {witness point : GaussianLine}
    (witnessRealizes : Projective.ProjectiveRealizes blocks witness)
    (pointRealizes : Projective.ProjectiveRealizes blocks point)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : threshold + margin ≤ probe witness ∨
      probe witness + margin ≤ threshold)
    (budgetSmall : factor * Cylinder.cylinderSpread blocks < margin ^ 2) :
    decide (threshold ≤ probe point) =
      decide (threshold ≤ probe witness) := by
  have squareSmall :=
    (Prefix.projectiveRealized_probe_separation_sq_le pointRealizes witnessRealizes
      probe factor factorNonnegative sensitive).trans_lt budgetSmall
  exact Event.atLeastDecision_eq_of_margin marginPositive
    (Purelib.Data.Rat.Distance.rationalSeparation_lt_of_sq_lt_sq marginPositive squareSmall) separated
end Purelib.Approximation.CCL.Prefix

end
