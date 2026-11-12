module

public import Purelib.Algebra.Monogenic.Coordinates.Reading.Parameters
public import Purelib.Data.Rat.SmallWidth
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Sufficient finite error requests for original cyclic readings

The fixed cached error coefficients determine one positive tolerance for
both the parent reading and generator-column residual before either is
observed. Their actual certified errors then imply the requested child bound.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element.Reading

open Purelib.Algebra.Ring (Weight)
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}
variable {cyclic : Cyclic generator} {parent : Weight K} {parentGain radius : Rational}

set_option genInjectivity false in
/-- A positive sufficient error request from the same cached parent and source coefficients.

The retained coefficient sum, shrinking width and squared tolerance are
computed before observations. The defining equations tie the request to
the original parameter object and requested positive target.
-/
structure Request (parameters : Parameters cyclic parent parentGain radius) (target : Rational) where
  /-- The requested child error target is strictly positive. -/
  targetPositive : 0 < target
  /-- The once-computed sum of the same stored linear error coefficients. -/
  coefficient : Rational
  /-- The coefficient uses the same original cached parameter values. -/
  coefficient_eq : coefficient = parameters.parentFactor + parameters.sourceFactor
  /-- The sufficient shrinking width computed from the original coefficient and target. -/
  width : Rational
  /-- The width uses the original sufficient rational constructor. -/
  width_eq : width = SmallWidth.shrinkingWidth coefficient target
  /-- The sufficient squared error tolerance for each input. -/
  tolerance : Rational
  /-- The stored tolerance is the square of the same retained width. -/
  tolerance_eq : tolerance = width ^ 2

constructive_injectivity Request

namespace Request

/-- Compute one positive sufficient parent and source tolerance from the original fixed coefficients. -/
@[expose] def prepare (parameters : Parameters cyclic parent parentGain radius) (target : Rational)
    (targetPositive : 0 < target) : Request parameters target :=
  let coefficient := parameters.parentFactor + parameters.sourceFactor
  let width := SmallWidth.shrinkingWidth coefficient target
  { targetPositive
    coefficient
    coefficient_eq := rfl
    width
    width_eq := rfl
    tolerance := width ^ 2
    tolerance_eq := rfl }

variable {parameters : Parameters cyclic parent parentGain radius} {target : Rational}

/-- The retained request coefficient is nonnegative. -/
theorem coefficient_nonnegative (request : Request parameters target) : 0 ≤ request.coefficient := by
  rewrite [request.coefficient_eq]
  exact Order.Arithmetic.add_le_add_direct parameters.parentFactor_nonnegative parameters.sourceFactor_nonnegative

/-- The retained sufficient request width is positive. -/
theorem width_positive (request : Request parameters target) : 0 < request.width := by
  rewrite [request.width_eq]
  exact SmallWidth.shrinkingWidth_pos request.coefficient_nonnegative request.targetPositive

/-- The retained squared tolerance is positive. -/
theorem tolerance_positive (request : Request parameters target) : 0 < request.tolerance := by
  rewrite [request.tolerance_eq]
  exact Order.Arithmetic.pow_pos_direct request.width_positive 2

/-- Any two input errors within the same stored tolerance meet the original requested child bound.

The errors are the actual certified parent error and original column
residual. This theorem does not obtain them by observation or promote
an unsuccessful attempt to an impossibility result.
-/
theorem error_lt (request : Request parameters target) (parentError residual : Rational)
    (parentBound : parentError ≤ request.tolerance) (residualBound : residual ≤ request.tolerance) :
    parameters.parentFactor * parentError + parameters.sourceFactor * residual < target := by
  have bounded := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentBound parameters.parentFactor_nonnegative)
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct residualBound parameters.sourceFactor_nonnegative)
  have collected : parameters.parentFactor * request.tolerance + parameters.sourceFactor * request.tolerance =
      request.coefficient * request.width ^ 2 := by
    rewrite [request.coefficient_eq, request.tolerance_eq]
    ring0
  have strict := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
    request.coefficient_nonnegative request.targetPositive
  rewrite [← request.width_eq] at strict
  exact (bounded.trans collected.le).trans_lt strict

end Request

end Purelib.Algebra.Monogenic.Cyclic.Element.Reading

end
