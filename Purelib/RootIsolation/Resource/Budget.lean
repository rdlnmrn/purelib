module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Geometry.Rational.Box.Resource
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Resource
import Purelib.Polynomial.Dense.Rational.Resource.Magnitude
public import Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation
public import Purelib.Polynomial.Elimination.Separated.Resource.Data
public import Purelib.RootIsolation.Resource.Input
public import Purelib.RootIsolation.Subdivision.Raw.Resource
public import Purelib.RootIsolation.Subdivision.Raw.Resource.Winding
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw

open Purelib.RootIsolation.Resource.Input (StageThreeInput)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Take the larger coefficient magnitude of the two original retained axis-elimination polynomials. -/
def safeEvaluationCoefficientMagnitude (input :
  StageThreeInput) : Nat :=
  max (Dense.Rational.Resource.Magnitude.coefficientMagnitude
      (id input.elimination.vertical))
    (Dense.Rational.Resource.Magnitude.coefficientMagnitude
      (id input.elimination.horizontal))
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Take the larger coefficient-slot count of the original vertical and horizontal eliminants. -/
def safeEvaluationSlotBound (input : StageThreeInput) : Nat
  :=
  max input.elimination.vertical.coeffs.length
    input.elimination.horizontal.coeffs.length
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Coarse normalized-field-operation count for building both central-third
candidate lists and evaluating both displayed elimination polynomials in one
subdivision round. -/
def safeCutRoundFieldOperationBudget (input :
  StageThreeInput) : Nat :=
  14 + (input.degreeBound + 1) *
    (10 + 2 * safeEvaluationSlotBound input) + 4
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Multiply the original per-round safe-cut operation budget by the computed subdivision depth. -/
def safeCutFieldOperationBudget (input : StageThreeInput) :
  Nat :=
  input.depth * safeCutRoundFieldOperationBudget input
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Bound original eliminant evaluation magnitudes using the retained coefficient and refined-coordinate envelopes. -/
def safeEvaluationMagnitudeBudget (input : StageThreeInput)
  : Nat :=
  let pointBound := Subdivision.Raw.Resource.refinementMagnitudeEnvelope
    input.degreeBound
    (Box.Resource.boxMagnitude input.state.box) input.depth
  Algebra.Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
    (max (safeEvaluationCoefficientMagnitude input) pointBound)
    (2 * safeEvaluationSlotBound input)
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Combine the original elimination, denominator-clearing, coordinate-refinement and winding magnitude envelopes. -/
def stageThreeCoreMagnitudeBudget (input : StageThreeInput)
  : Nat :=
  max (Elimination.Separated.Resource.Data.separatedDataMagnitudeEnvelope
      input.polynomial)
    (max (Elimination.Separated.Resource.Data.separatedDataMagnitudeEnvelope
        input.horizontalPolynomial)
      (max (max
          (Dense.Gaussian.Denominator.Clearing.Resource.coefficientDenominatorProduct
            input.polynomial.normalize.coeffs)
          (Dense.Gaussian.Denominator.Clearing.Resource.clearedCoefficientMagnitudeEnvelope
            input.polynomial.normalize.coeffs))
        (max (Subdivision.Raw.Resource.refinementMagnitudeEnvelope
            input.degreeBound
            (Box.Resource.boxMagnitude input.state.box)
            input.depth)
          (Subdivision.Raw.Resource.Winding.refinementWindingMagnitudeBudget input.elimination input.state
            input.depth))))
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Combine the retained core calculation envelope with the original safe-evaluation magnitude budget. -/
def stageThreeMagnitudeBudget (input : StageThreeInput) :
  Nat :=
  max (stageThreeCoreMagnitudeBudget input)
    (safeEvaluationMagnitudeBudget input)
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Compute the natural bit width of the original combined calculation magnitude budget. -/
def stageThreeBitBudget (input : StageThreeInput) : Nat :=
  Data.Nat.BitWidth.natWidth (stageThreeMagnitudeBudget input)
end Purelib.RootIsolation.Resource.Budget

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.RootIsolation.Resource.Budget

/-- Sum the original denominator-clearing, two-axis elimination, subdivision-search, safe-cut and winding operation
budgets. -/
def stageThreeStepBudget (input : StageThreeInput) : Nat :=
  Dense.Gaussian.Denominator.Clearing.Resource.coefficientClearingOperationBudget
      input.polynomial.normalize.coeffs +
    Elimination.Separated.Normalized.Resource.Operation.eliminantOperationBudget input.polynomial +
    Elimination.Separated.Normalized.Resource.Operation.eliminantOperationBudget input.horizontalPolynomial +
    Subdivision.Raw.Resource.subdivisionSearchBudget
      input.degreeBound input.depth +
    safeCutFieldOperationBudget input +
    Subdivision.Raw.Resource.Winding.refinementWindingStepBudget input.elimination input.state input.depth
end Purelib.RootIsolation.Resource.Budget

end
